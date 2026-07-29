//! Host-side component. Connects to the enclave over vsock, runs the register -> mint -> affirm
//! workflow, and verifies each proof. The device half runs in `dart-auth-enclave`.

#[cfg(target_os = "linux")]
fn main() -> std::io::Result<()> {
    use polymesh_dart::device::{StreamDevice, run_register_mint_affirm};
    use vsock::VsockStream;

    const PORT: u32 = 5005;
    const VMADDR_CID_LOCAL: u32 = 1;

    // Enclave CID from argv[1]; defaults to loopback (enclave in the same VM).
    let cid = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(VMADDR_CID_LOCAL);

    let stream = VsockStream::connect_with_cid_port(cid, PORT)?;
    let mut device = StreamDevice::new(stream);
    run_register_mint_affirm(&mut device);
    println!("PASS: register/mint/affirm proofs verified over vsock (cid {cid})");
    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("dart-auth-host runs only on Linux (vsock)");
}
