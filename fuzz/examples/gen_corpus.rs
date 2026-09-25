//! Write the SCALE-encoded valid seed requests (and standalone leg encryptions) to
//! `fuzz/corpus/<target>/` so `cargo fuzz run` starts from inputs that reach the verifiers.
//!
//! `cargo run -p polymesh-dart-fuzz --release --example gen_corpus`

use codec::Encode;
use std::fs;
use std::path::PathBuf;

fn main() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("corpus");

    let dir = root.join("verify_request");
    fs::create_dir_all(&dir).unwrap();
    for s in polymesh_dart_fuzz::seeds() {
        let path = dir.join(format!("{}.bin", s.name));
        fs::write(&path, s.encoded()).unwrap();
        println!("wrote {}", path.display());
    }

    let dir = root.join("leg_encrypted");
    fs::create_dir_all(&dir).unwrap();
    for (name, leg) in polymesh_dart_fuzz::leg_encryptions() {
        let path = dir.join(format!("{name}.bin"));
        fs::write(&path, leg.encode()).unwrap();
        println!("wrote {}", path.display());
    }

    let dir = root.join("curve_tree_root");
    fs::create_dir_all(&dir).unwrap();
    for s in polymesh_dart_fuzz::seeds() {
        use polymesh_dart_fuzz::VerifyDartAssetRequest as R;
        let bytes = match &s.request {
            R::MintAsset { root, .. } | R::SenderAffirmation { root, .. } => root.encode(),
            R::CreateSettlement { root, .. } => root.encode(),
            R::FeeAccountTopup { root, .. } => root.encode(),
            _ => continue,
        };
        let path = dir.join(format!("{}.bin", s.name));
        fs::write(&path, bytes).unwrap();
        println!("wrote {}", path.display());
    }
}
