use super::{AuthDevice, Device, DeviceRequest, DeviceResponse};
use crate::error::Error;
use codec::{DecodeAll, Encode};
use rand_core::CryptoRngCore;
use std::io::{self, Read, Write};

/// Largest frame either side sends or accepts.
pub const MAX_FRAME_LEN: usize = 1 << 20;

/// Frame layout: `[u32 length LE][SCALE bytes]`.
pub fn write_frame<W: Write>(writer: &mut W, bytes: &[u8]) -> io::Result<()> {
    if bytes.len() > MAX_FRAME_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "frame too large",
        ));
    }
    writer.write_all(&(bytes.len() as u32).to_le_bytes())?;
    writer.write_all(bytes)?;
    writer.flush()
}

pub fn read_frame<R: Read>(reader: &mut R) -> io::Result<Vec<u8>> {
    let mut len = [0u8; 4];
    reader.read_exact(&mut len)?;
    let len = u32::from_le_bytes(len) as usize;
    if len > MAX_FRAME_LEN {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "frame too large",
        ));
    }
    let mut bytes = vec![0u8; len];
    reader.read_exact(&mut bytes)?;
    Ok(bytes)
}

/// The enclave's connection loop.
pub fn serve<S: Read + Write, R: CryptoRngCore>(
    mut stream: S,
    device: &mut Device,
    rng: &mut R,
) -> io::Result<()> {
    loop {
        let bytes = match read_frame(&mut stream) {
            Ok(bytes) => bytes,
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(e) => return Err(e),
        };
        let response = match DeviceRequest::decode_all(&mut &bytes[..]) {
            Ok(request) => device
                .handle(request, rng)
                .unwrap_or_else(|e| DeviceResponse::Err(format!("{e}"))),
            Err(_) => DeviceResponse::Err("bad request".into()),
        };
        write_frame(&mut stream, &response.encode())?;
    }
}

/// A `Device` reached over a byte stream (vsock on the parent, or TCP for testing).
pub struct StreamDevice<S> {
    stream: S,
}

impl<S: Read + Write> StreamDevice<S> {
    pub fn new(stream: S) -> Self {
        Self { stream }
    }
}

impl<S: Read + Write> AuthDevice for StreamDevice<S> {
    fn send(&mut self, request: DeviceRequest) -> Result<DeviceResponse, Error> {
        write_frame(&mut self.stream, &request.encode())
            .map_err(|e| Error::Device(format!("write: {e}")))?;
        let bytes =
            read_frame(&mut self.stream).map_err(|e| Error::Device(format!("read: {e}")))?;
        DeviceResponse::decode_all(&mut &bytes[..]).map_err(|_| Error::DecodeError)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::device::DataKeyProvider;

    #[test]
    fn frame_length_capped() {
        let mut frame = ((MAX_FRAME_LEN + 1) as u32).to_le_bytes().to_vec();
        frame.extend_from_slice(&[0u8; 8]);
        let err = read_frame(&mut &frame[..]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidData);

        let err = write_frame(&mut Vec::new(), &vec![0u8; MAX_FRAME_LEN + 1]).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::InvalidInput);

        let mut buf = Vec::new();
        write_frame(&mut buf, &[1, 2, 3]).unwrap();
        assert_eq!(read_frame(&mut &buf[..]).unwrap(), vec![1, 2, 3]);
    }

    struct NoKeyProvider;

    impl DataKeyProvider for NoKeyProvider {
        fn fresh_data_key(&mut self) -> Result<(super::super::DataKey, Vec<u8>), Error> {
            Err(Error::Device("no key".into()))
        }

        fn unwrap_data_key(&self, _wrapped: &[u8]) -> Result<super::super::DataKey, Error> {
            Err(Error::Device("no key".into()))
        }
    }

    /// Input frames and the responses written back.
    struct Stream {
        input: io::Cursor<Vec<u8>>,
        output: Vec<u8>,
    }

    impl Read for Stream {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            self.input.read(buf)
        }
    }

    impl Write for Stream {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.output.write(buf)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn serve_answers_malformed_request_and_continues() {
        let mut input = Vec::new();
        write_frame(&mut input, &[0xff, 0xff, 0xff]).unwrap();
        write_frame(&mut input, &DeviceRequest::LoadKeys(vec![0u8; 4]).encode()).unwrap();
        let mut stream = Stream {
            input: io::Cursor::new(input),
            output: Vec::new(),
        };
        let mut device = Device::with_provider(Box::new(NoKeyProvider));
        let mut rng = rand::thread_rng();
        serve(&mut stream, &mut device, &mut rng).unwrap();

        let mut output = &stream.output[..];
        for _ in 0..2 {
            let bytes = read_frame(&mut output).unwrap();
            let response = DeviceResponse::decode_all(&mut &bytes[..]).unwrap();
            assert!(matches!(response, DeviceResponse::Err(_)));
        }
        assert!(output.is_empty());
    }
}
