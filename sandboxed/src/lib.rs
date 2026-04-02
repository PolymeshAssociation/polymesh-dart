#![no_std]

extern crate alloc;
use alloc::vec::Vec;

use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Projective, SWCurveConfig};
use ark_ec::AffineRepr;
use ark_ec_divisors::{util::GeneratorTable, DivisorCurve};
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use bulletproofs::{BulletproofGens, PedersenGens};
use codec::Decode;
use curve_tree_relations::rerandomize::build_tables;
use polymesh_dart::curve_tree::{AccountTreeConfig, CompressedCurveTreeRoot};
use polymesh_dart::{
    curve_tree::{
        get_account_curve_tree_parameters, get_asset_curve_tree_parameters, SingleLayerParameters,
    },
    get_bp_gens, get_pc_gens, PallasA,
};
use polymesh_dart::{
    AccountAssetRegistrationProof, LegEncrypted, SenderAffirmationProof, ACCOUNT_TREE_L,
    ACCOUNT_TREE_M,
};
use rand_core::SeedableRng;

polkavm_derive::min_stack_size!(1);
polkavm_derive::min_stack_size!(1024 * 1024);
polkavm_derive::min_stack_size!(2);

const HEAP_SIZE: usize = 10 * 1024 * 1024;

#[global_allocator]
static mut GLOBAL_ALLOC: picoalloc::Mutex<
    picoalloc::Allocator<picoalloc::ArrayPointer<{ HEAP_SIZE }>>,
> = {
    static mut ARRAY: picoalloc::Array<{ HEAP_SIZE }> = picoalloc::Array([0; HEAP_SIZE]);

    picoalloc::Mutex::new(picoalloc::Allocator::new(unsafe {
        picoalloc::ArrayPointer::new(&raw mut ARRAY)
    }))
};

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    #[cfg(target_family = "wasm")]
    {
        core::arch::wasm32::unreachable();
    }

    #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
    unsafe {
        core::arch::asm!("unimp", options(noreturn));
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe {
        core::arch::asm!("ud2", options(noreturn));
    }
}

static mut CACHE_PC_GENS: Option<PedersenGens<PallasA>> = None;

#[allow(static_mut_refs)]
fn get_cached_pc_gens() -> &'static PedersenGens<PallasA> {
    unsafe {
        if CACHE_PC_GENS.is_none() {
            let pc_gens =
                PedersenGens::<PallasA>::new().expect("Failed to create Pedersen generators");
            CACHE_PC_GENS = Some(pc_gens);
        }
        CACHE_PC_GENS.as_ref().unwrap()
    }
}

static mut CACHE_BP_GENS: Option<BulletproofGens<PallasA>> = None;

#[allow(static_mut_refs)]
fn get_cached_bp_gens() -> &'static BulletproofGens<PallasA> {
    unsafe {
        if CACHE_BP_GENS.is_none() {
            let bp_gens = get_bp_gens();
            CACHE_BP_GENS = Some(bp_gens);
        }
        CACHE_BP_GENS.as_ref().unwrap()
    }
}

#[polkavm_derive::polkavm_import]
extern "C" {
    fn get_third_number() -> u32;
}

#[polkavm_derive::polkavm_export]
pub extern "C" fn init_params() -> u32 {
    let params = get_account_curve_tree_parameters();
    let pc_gens = get_cached_pc_gens();
    let bp_gens = get_cached_bp_gens();
    0
}

#[polkavm_derive::polkavm_export]
pub extern "C" fn get_params() -> u32 {
    let params = get_account_curve_tree_parameters();
    let pc_gens = get_cached_pc_gens();
    let bp_gens = get_cached_bp_gens();
    let mut buf = Vec::new();

    params
        .serialize_compressed(&mut buf)
        .expect("Failed to serialize parameters");

    buf.len() as u32
}

#[polkavm_derive::polkavm_export]
pub extern "C" fn verify_register_account_asset_proof() -> u32 {
    let raw_proof = include_bytes!("../../dart-testing-cli/register-account-proof.dat");
    let params = get_account_curve_tree_parameters();

    let proof =
        AccountAssetRegistrationProof::decode(&mut &raw_proof[..]).expect("Failed to decode proof");

    // Verify the proof
    let signer_name = "investor";
    let mut rng = rand_chacha::ChaChaRng::from_seed([42u8; 32]);
    let res = proof.verify(signer_name.as_bytes(), params, &mut rng);

    if res.is_ok() {
        1
    } else {
        0
    }
}

#[polkavm_derive::polkavm_export]
pub extern "C" fn verify_sender_affirm_proof() -> u32 {
    let raw_proof = include_bytes!("../../dart-testing-cli/sender-affirm-proof.dat");
    let raw_leg_enc = include_bytes!("../../dart-testing-cli/settlement_2_leg_0.bin");
    let raw_account_root =
        include_bytes!("../../dart-testing-cli/block_12_current_account_root.bin");

    let proof = SenderAffirmationProof::<AccountTreeConfig>::decode(&mut &raw_proof[..])
        .expect("Failed to decode proof");
    let leg_enc: LegEncrypted =
        Decode::decode(&mut &raw_leg_enc[..]).expect("Failed to decode leg encryption");
    let root: CompressedCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig> =
        Decode::decode(&mut &raw_account_root[..]).expect("Failed to decode account root");

    // Verify the proof
    let mut rng = rand_chacha::ChaChaRng::from_seed([42u8; 32]);
    let res = proof.verify(&leg_enc, root, &mut rng);

    if res.is_ok() {
        1
    } else {
        0
    }
}
