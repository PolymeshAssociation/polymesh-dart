use bulletproofs::{BulletproofGens, PedersenGens};
use polymesh_dart::{
  curve_tree::get_account_curve_tree_parameters,
  get_pc_gens, get_bp_gens,
  PallasA,
};

const HEAP_SIZE: usize = 10 * 1024 * 1024;

#[global_allocator]
static mut GLOBAL_ALLOC: picoalloc::Mutex<picoalloc::Allocator<picoalloc::ArrayPointer<{ HEAP_SIZE }>>> = {
    static mut ARRAY: picoalloc::Array<{ HEAP_SIZE }> = picoalloc::Array([0; HEAP_SIZE]);

    picoalloc::Mutex::new(picoalloc::Allocator::new(
        unsafe { picoalloc::ArrayPointer::new(&raw mut ARRAY) }
    ))
};

pub fn main() {
  let params = get_account_curve_tree_parameters();
    println!("Test sandboxed program");

    let res = 0u32;
    println!("Result: {res}");
}