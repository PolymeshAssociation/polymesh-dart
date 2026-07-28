use super::{AuthDevice, Device, DeviceRequest, DeviceResponse};
use crate::error::Error;
use codec::{Decode, Encode};
use rand_core::CryptoRngCore;
use std::io::{self, Read, Write};

/// Frame layout: `[u32 length LE][SCALE bytes]`.
pub fn write_frame<W: Write>(writer: &mut W, bytes: &[u8]) -> io::Result<()> {
    writer.write_all(&(bytes.len() as u32).to_le_bytes())?;
    writer.write_all(bytes)?;
    writer.flush()
}

pub fn read_frame<R: Read>(reader: &mut R) -> io::Result<Vec<u8>> {
    let mut len = [0u8; 4];
    reader.read_exact(&mut len)?;
    let mut bytes = vec![0u8; u32::from_le_bytes(len) as usize];
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
        let request = DeviceRequest::decode(&mut &bytes[..])
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "bad request"))?;
        let response = device
            .handle(request, rng)
            .unwrap_or_else(|e| DeviceResponse::Err(format!("{e}")));
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
        DeviceResponse::decode(&mut &bytes[..]).map_err(|_| Error::DecodeError)
    }
}
