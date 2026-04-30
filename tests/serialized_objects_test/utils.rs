use crate::constants::{ALICE_SEED, BOB_SEED, SEED, V1_DIR};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use codec::{Decode, Encode};
use polymesh_dart::AccountKeys;
use rand_chacha::ChaCha20Rng;
use rand_core::SeedableRng;
use std::fs;

pub fn save_scale<T: Encode>(version_dir: &str, filename: &str, value: &T) {
    let path = format!("{}/{}", version_dir, filename);
    fs::write(&path, value.encode()).unwrap_or_else(|e| panic!("write {path}: {e}"));
}

pub fn load_scale<T: Decode>(version_dir: &str, filename: &str) -> T {
    let path = format!("{}/{}", version_dir, filename);
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    T::decode(&mut bytes.as_slice()).unwrap_or_else(|e| panic!("decode {path}: {e}"))
}

pub fn save_canonical<T: CanonicalSerialize>(version_dir: &str, filename: &str, value: &T) {
    let path = format!("{}/{}", version_dir, filename);
    let mut bytes = Vec::new();
    value
        .serialize_compressed(&mut bytes)
        .unwrap_or_else(|e| panic!("serialize {path}: {e}"));
    fs::write(&path, bytes).unwrap_or_else(|e| panic!("write {path}: {e}"));
}

pub fn load_canonical<T: CanonicalDeserialize>(version_dir: &str, filename: &str) -> T {
    let path = format!("{}/{}", version_dir, filename);
    let bytes = fs::read(&path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    T::deserialize_compressed(&mut bytes.as_slice())
        .unwrap_or_else(|e| panic!("deserialize {path}: {e}"))
}

pub fn save_scale_v1<T: Encode>(filename: &str, value: &T) {
    save_scale(V1_DIR, filename, value);
}

pub fn load_scale_v1<T: Decode>(filename: &str) -> T {
    load_scale(V1_DIR, filename)
}

pub fn save_canonical_v1<T: CanonicalSerialize>(filename: &str, value: &T) {
    save_canonical(V1_DIR, filename, value);
}

pub fn load_canonical_v1<T: CanonicalDeserialize>(filename: &str) -> T {
    load_canonical(V1_DIR, filename)
}

pub fn default_rng() -> ChaCha20Rng {
    ChaCha20Rng::from_seed(SEED)
}

pub fn alice_keys() -> AccountKeys {
    AccountKeys::from_seed(ALICE_SEED).unwrap()
}

pub fn bob_keys() -> AccountKeys {
    AccountKeys::from_seed(BOB_SEED).unwrap()
}
