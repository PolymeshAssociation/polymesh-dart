use ark_ec::CurveGroup;
use ark_ff::{AdditiveGroup, Zero};
// Use BTreeMap for no_std compatibility
#[cfg(not(feature = "std"))]
use ark_std::collections::BTreeMap as HashMap;
#[cfg(feature = "std")]
use std::collections::HashMap;

pub type PallasP = ark_pallas::Projective;

#[cfg(feature = "large_baby_steps")]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 19;
#[cfg(not(feature = "large_baby_steps"))]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 16;

pub struct BabyStepsTable<G: AdditiveGroup + CurveGroup> {
    pub base_m: G,
    pub base_u32_max: G,
    pub table: HashMap<[u8; 32], u64>,
}

fn group_element_to_bytes<G: AdditiveGroup + CurveGroup>(elem: &G) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    elem.serialize_compressed(&mut bytes[..])
        .expect("Serialization of group element should not fail");
    bytes
}

impl<G: AdditiveGroup + CurveGroup> BabyStepsTable<G> {
    pub fn new(base: G) -> Self {
        let mut table = HashMap::new();
        let base_bytes = group_element_to_bytes(&base);
        table.insert(base_bytes, 1);
        let mut cur = base;
        for i in 2..=MAX_NUM_BABY_STEPS {
            cur = cur + base;
            let cur_bytes = group_element_to_bytes(&cur);
            table.insert(cur_bytes, i);
        }
        Self {
            base_m: cur,
            base_u32_max: base * G::ScalarField::from(u32::MAX as u64),
            table,
        }
    }

    pub fn get(&self, target: &G) -> Option<u64> {
        let target_bytes = group_element_to_bytes(target);
        self.table.get(&target_bytes).cloned()
    }
}

pub struct CacheBabyStepsTable<G: AdditiveGroup + CurveGroup> {
    #[cfg(feature = "std")]
    pub tables: HashMap<[u8; 32], std::sync::Arc<BabyStepsTable<G>>>,
    #[cfg(not(feature = "std"))]
    pub tables: HashMap<[u8; 32], BabyStepsTable<G>>,
}

impl<G: AdditiveGroup + CurveGroup> CacheBabyStepsTable<G> {
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    #[cfg(feature = "std")]
    pub fn get_or_build(&mut self, base: G) -> std::sync::Arc<BabyStepsTable<G>> {
        let base_bytes = group_element_to_bytes(&base);
        self.tables
            .entry(base_bytes)
            .or_insert_with(|| std::sync::Arc::new(BabyStepsTable::new(base)))
            .clone()
    }

    #[cfg(not(feature = "std"))]
    pub fn get_or_build(&mut self, base: G) -> &BabyStepsTable<G> {
        let base_bytes = group_element_to_bytes(&base);
        self.tables
            .entry(base_bytes)
            .or_insert_with(|| BabyStepsTable::new(base))
    }
}

pub type PallasBabyStepsTable = BabyStepsTable<PallasP>;

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    static ref CACHE_BABY_STEPS: std::sync::RwLock<CacheBabyStepsTable<PallasP>> = std::sync::RwLock::new(CacheBabyStepsTable::new());
}

#[cfg(feature = "std")]
fn get_cache_baby_steps(base: PallasP) -> std::sync::Arc<PallasBabyStepsTable> {
    let mut cache = CACHE_BABY_STEPS.write().unwrap();
    cache.get_or_build(base)
}

#[cfg(not(feature = "std"))]
static mut CACHE_BABY_STEPS: Option<CacheBabyStepsTable<PallasP>> = None;

#[allow(static_mut_refs)]
#[cfg(not(feature = "std"))]
fn get_cache_baby_steps(base: PallasP) -> &'static PallasBabyStepsTable {
    let cache = unsafe {
        if CACHE_BABY_STEPS.is_none() {
            CACHE_BABY_STEPS = Some(CacheBabyStepsTable::new());
        }
        CACHE_BABY_STEPS.as_mut().unwrap()
    };

    cache.get_or_build(base)
}

/// Solve discrete log using brute force.
/// `max` is the maximum value of the discrete log and this returns `x` such that `1 <= x <= max` and `base * x = target`
/// if such `x` exists, else return None.
pub fn solve_discrete_log_brute_force(max: u64, base: PallasP, target: PallasP) -> Option<u64> {
    if target == base {
        return Some(1);
    }
    let mut cur = base;
    for j in 2..=max {
        cur += base;
        if cur == target {
            return Some(j);
        }
    }
    None
}

#[cfg(not(feature = "parallel"))]
pub fn solve_discrete_log_bsgs(max: u64, base: PallasP, target: PallasP) -> Option<u64> {
    if base == target {
        return Some(1);
    }
    if target.is_zero() {
        return Some(0);
    }

    let baby_steps = get_cache_baby_steps(base);
    if let Some(b) = baby_steps.get(&target) {
        return Some(b);
    }
    let base_m = baby_steps.base_m;
    let mut cur = target;
    let num_giant_steps = (max + MAX_NUM_BABY_STEPS - 1) / MAX_NUM_BABY_STEPS;
    for i in 0..num_giant_steps {
        if let Some(b) = baby_steps.get(&cur) {
            return Some(i * MAX_NUM_BABY_STEPS + b);
        }
        cur = cur - base_m;
    }
    None
}

fn solve_discrete_log_bsgs_u32(baby_steps: &PallasBabyStepsTable, target: PallasP) -> Option<u64> {
    if let Some(b) = baby_steps.get(&target) {
        return Some(b);
    }
    let base_m = baby_steps.base_m;
    let mut cur = target;
    const NUM_GIANT_STEPS_U32: u64 =
        (u32::MAX as u64 + MAX_NUM_BABY_STEPS - 1) / MAX_NUM_BABY_STEPS;
    for i in 0..NUM_GIANT_STEPS_U32 {
        if let Some(b) = baby_steps.get(&cur) {
            return Some(i * MAX_NUM_BABY_STEPS + b);
        }
        cur = cur - base_m;
    }
    None
}

#[cfg(feature = "parallel")]
pub fn solve_discrete_log_bsgs(max: u64, base: PallasP, target: PallasP) -> Option<u64> {
    use rayon::prelude::*;

    if base == target {
        return Some(1);
    }
    if target.is_zero() {
        return Some(0);
    }

    let baby_steps = get_cache_baby_steps(base);
    // Use a single thread to check the first 0-u32::MAX range.
    if let Some(v) = solve_discrete_log_bsgs_u32(&baby_steps, target) {
        return Some(v);
    }
    let base_u32_max = baby_steps.base_u32_max;
    let mut starting_point = target;
    const CHUNK_SIZE: u64 = u32::MAX as u64;
    let chunk_count = (max + CHUNK_SIZE - 1) / CHUNK_SIZE;
    (1..chunk_count)
        .into_iter()
        .map(|idx| {
            let offset = idx * CHUNK_SIZE;
            starting_point = starting_point - base_u32_max;
            (offset, starting_point)
        })
        .par_bridge()
        .find_map_any(|(offset, starting_point)| {
            solve_discrete_log_bsgs_u32(&baby_steps, starting_point).map(|v| v + offset)
        })
}
