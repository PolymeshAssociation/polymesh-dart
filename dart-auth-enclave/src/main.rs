//! The enclave holds the account keys and produces auth proofs, reached only over vsock.

#[cfg(target_os = "linux")]
fn main() -> std::io::Result<()> {
    use polymesh_dart::device::{Device, serve};
    use rand::rngs::OsRng;
    use vsock::VsockListener;

    const PORT: u32 = 5005;
    const VMADDR_CID_ANY: u32 = 0xFFFF_FFFF;

    let listener = VsockListener::bind_with_cid_port(VMADDR_CID_ANY, PORT)?;
    eprintln!("dart-auth-enclave listening on vsock port {PORT}");

    // Keys and generators live in memory for the life of the process (ephemeral for the PoC).
    let mut device = Device::new();
    let mut rng = OsRng;
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                if let Err(e) = serve(stream, &mut device, &mut rng) {
                    eprintln!("connection error: {e}");
                }
            }
            Err(e) => eprintln!("accept error: {e}"),
        }
    }
    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("dart-auth-enclave runs only on Linux (vsock); build for x86_64-unknown-linux-musl");
}
