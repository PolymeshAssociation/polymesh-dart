use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::AdditiveGroup;
// Use BTreeMap for no_std compatibility
#[cfg(not(feature = "std"))]
use ark_std::{collections::BTreeMap as HashMap, sync::Arc, vec::Vec};
#[cfg(feature = "std")]
use std::{collections::HashMap, sync::Arc};

#[cfg(feature = "large_baby_steps")]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 21;
#[cfg(not(feature = "large_baby_steps"))]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 17;

/// Lockstep giant steps per normalization window. Amortizes the batch inversion and (in
/// parallel builds) the rayon fork-join overhead of `normalize_batch` over many steps.
const NORMALIZE_STRIDE: u64 = 2048;

pub struct BabyStepsTable {
    pub base_m: [u8; 32],
    pub base_u32_max: [u8; 32],
    pub table: HashMap<[u8; 32], u32>,
}

fn affine_to_bytes<A: AffineRepr>(target: &A) -> Option<[u8; 32]> {
    let mut target_bytes = [0u8; 32];
    target.serialize_compressed(&mut target_bytes[..]).ok()?;
    Some(target_bytes)
}

fn group_element_to_bytes<G: AdditiveGroup + CurveGroup>(elem: &G) -> Option<[u8; 32]> {
    let mut bytes = [0u8; 32];
    elem.serialize_compressed(&mut bytes[..]).ok()?;
    Some(bytes)
}

fn bytes_to_group_element<G: AdditiveGroup + CurveGroup>(bytes: &[u8; 32]) -> G {
    G::deserialize_compressed(&bytes[..]).expect("Deserialization of group element should not fail")
}

impl BabyStepsTable {
    #[cfg(feature = "parallel")]
    pub fn new<G: AdditiveGroup + CurveGroup>(base: G) -> Option<Self> {
        use rayon::prelude::*;

        let chunk_count = 32u64;
        let chunk_size: u64 = MAX_NUM_BABY_STEPS / chunk_count;
        let table = (0..chunk_count)
            .into_iter()
            .map(|chunk_idx| chunk_idx * chunk_size + 1)
            .par_bridge()
            .flat_map(|first_step| {
                let mut starting_point = base * G::ScalarField::from(first_step);
                let mut projective_points = Vec::with_capacity(chunk_size as usize);
                for _ in 0..chunk_size {
                    projective_points.push(starting_point);
                    starting_point = starting_point + base;
                }
                let affines = G::normalize_batch(&projective_points);
                let mut points = Vec::new();
                for (i, affine) in affines.iter().enumerate() {
                    let bytes = affine_to_bytes(affine)
                        .expect("Serialization of group element should not fail");
                    points.push((bytes, (first_step + i as u64) as u32));
                }
                points
            })
            .collect();

        let base_u32_max = base * G::ScalarField::from(u32::MAX as u64);
        Some(Self {
            base_m: group_element_to_bytes(&(base * G::ScalarField::from(MAX_NUM_BABY_STEPS)))?,
            base_u32_max: group_element_to_bytes(&base_u32_max)?,
            table,
        })
    }

    #[cfg(not(feature = "parallel"))]
    pub fn new<G: AdditiveGroup + CurveGroup>(base: G) -> Option<Self> {
        let mut cur = base;
        let mut projective_points = Vec::with_capacity(MAX_NUM_BABY_STEPS as usize);
        for _ in 0..MAX_NUM_BABY_STEPS {
            projective_points.push(cur);
            cur = cur + base;
        }
        let affines = G::normalize_batch(&projective_points);
        let mut table = HashMap::new();
        for (i, affine) in affines.iter().enumerate() {
            let bytes =
                affine_to_bytes(affine).expect("Serialization of group element should not fail");
            table.insert(bytes, (i + 1) as u32);
        }
        let base_u32_max = base * G::ScalarField::from(u32::MAX as u64);
        Some(Self {
            base_m: group_element_to_bytes(&(base * G::ScalarField::from(MAX_NUM_BABY_STEPS)))?,
            base_u32_max: group_element_to_bytes(&base_u32_max)?,
            table,
        })
    }

    pub fn get<G: AdditiveGroup + CurveGroup>(&self, target: &G) -> Option<u64> {
        let target_bytes =
            group_element_to_bytes(target).expect("Serialization of group element should not fail");
        self.table.get(&target_bytes).cloned().map(|v| v as u64)
    }

    pub fn get_affine<A: AffineRepr>(&self, target: &A) -> Option<u64> {
        let mut target_bytes = [0u8; 32];
        target.serialize_compressed(&mut target_bytes[..]).ok()?;
        self.table.get(&target_bytes).cloned().map(|v| v as u64)
    }

    pub fn base_m<G: AdditiveGroup + CurveGroup>(&self) -> G {
        bytes_to_group_element(&self.base_m)
    }

    pub fn base_u32_max<G: AdditiveGroup + CurveGroup>(&self) -> G {
        bytes_to_group_element(&self.base_u32_max)
    }
}

pub struct CacheBabyStepsTable {
    pub tables: HashMap<[u8; 32], Arc<BabyStepsTable>>,
}

impl CacheBabyStepsTable {
    pub fn new() -> Self {
        Self {
            tables: HashMap::new(),
        }
    }

    #[cfg(feature = "std")]
    pub fn get_or_build<G: AdditiveGroup + CurveGroup>(
        &mut self,
        base: G,
    ) -> Option<Arc<BabyStepsTable>> {
        use std::collections::hash_map::Entry;
        let base_bytes = group_element_to_bytes(&base)?;
        let entry = self.tables.entry(base_bytes);
        let o = match entry {
            Entry::Vacant(v) => v.insert_entry(Arc::new(BabyStepsTable::new(base)?)),
            Entry::Occupied(o) => o,
        };
        Some(o.get().clone())
    }

    #[cfg(not(feature = "std"))]
    pub fn get_or_build<'a, G: AdditiveGroup + CurveGroup>(
        &'a mut self,
        base: G,
    ) -> Option<Arc<BabyStepsTable>> {
        use ark_std::collections::btree_map::Entry;
        let base_bytes = group_element_to_bytes(&base)?;
        let entry = self.tables.entry(base_bytes);
        match entry {
            Entry::Vacant(v) => {
                let table = Arc::new(BabyStepsTable::new(base)?);
                v.insert(table.clone());
                Some(table)
            }
            Entry::Occupied(o) => Some(o.get().clone()),
        }
    }
}

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    static ref CACHE_BABY_STEPS: std::sync::RwLock<CacheBabyStepsTable> = std::sync::RwLock::new(CacheBabyStepsTable::new());
}

#[cfg(feature = "std")]
fn get_cache_baby_steps<G: AdditiveGroup + CurveGroup>(base: G) -> Option<Arc<BabyStepsTable>> {
    let mut cache = CACHE_BABY_STEPS.write().unwrap();
    cache.get_or_build(base)
}

#[cfg(not(feature = "std"))]
static mut CACHE_BABY_STEPS: Option<CacheBabyStepsTable> = None;

#[allow(static_mut_refs)]
#[cfg(not(feature = "std"))]
fn get_cache_baby_steps<G: AdditiveGroup + CurveGroup>(base: G) -> Option<Arc<BabyStepsTable>> {
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
pub fn solve_discrete_log_brute_force<G: AdditiveGroup + CurveGroup>(
    max: u64,
    base: G,
    target: G,
) -> Option<u64> {
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

/// Strided giant-step scan of one contiguous range starting at `start`. Returns the value
/// relative to the range start. The points buffer is reused across windows; each window costs
/// one batch inversion via `normalize_batch` instead of one inversion per step.
fn scan_single_strided<G: AdditiveGroup + CurveGroup>(
    baby_steps: &BabyStepsTable,
    base_m: G,
    start: G,
    num_steps: u64,
) -> Option<u64> {
    let mut points: Vec<G> = Vec::with_capacity(NORMALIZE_STRIDE.min(num_steps) as usize);
    let mut cur = start;
    let mut steps_done = 0u64;
    while steps_done < num_steps {
        let n = (num_steps - steps_done).min(NORMALIZE_STRIDE);
        points.clear();
        for _ in 0..n {
            points.push(cur);
            cur = cur - base_m;
        }
        let affines = G::normalize_batch(&points);
        for (j, affine) in affines.iter().enumerate() {
            if let Some(b) = baby_steps.get_affine(affine) {
                return Some((steps_done + j as u64) * MAX_NUM_BABY_STEPS + b);
            }
        }
        steps_done += n;
    }
    None
}

#[cfg(not(feature = "parallel"))]
pub fn solve_discrete_log_bsgs<G: AdditiveGroup + CurveGroup>(
    max: u64,
    base: G,
    target: G,
) -> Option<u64> {
    if base == target {
        return Some(1);
    }
    if target.is_zero() {
        return Some(0);
    }

    let baby_steps = match get_cache_baby_steps(base) {
        Some(b) => b,
        None => return solve_discrete_log_brute_force(max, base, target),
    };
    let num_steps = (max + MAX_NUM_BABY_STEPS - 1) / MAX_NUM_BABY_STEPS;
    scan_single_strided(&baby_steps, baby_steps.base_m(), target, num_steps)
}

#[cfg(feature = "parallel")]
pub fn solve_discrete_log_bsgs<G: AdditiveGroup + CurveGroup>(
    max: u64,
    base: G,
    target: G,
) -> Option<u64> {
    if base == target {
        return Some(1);
    }
    if target.is_zero() {
        return Some(0);
    }

    let baby_steps = match get_cache_baby_steps(base) {
        Some(b) => b,
        None => return solve_discrete_log_brute_force(max, base, target),
    };
    // Use a single thread to check the first 0-u32::MAX range.
    const CHUNK_SIZE: u64 = u32::MAX as u64;
    let first_span = max.min(CHUNK_SIZE);
    let first_steps = (first_span + MAX_NUM_BABY_STEPS - 1) / MAX_NUM_BABY_STEPS;
    let base_m: G = baby_steps.base_m();
    if let Some(v) = scan_single_strided(&baby_steps, base_m, target, first_steps) {
        return Some(v);
    }
    if max <= CHUNK_SIZE {
        return None;
    }
    solve_discrete_log_bsgs_tail(max, &baby_steps, base_m, target)
}

/// Parallel scan of the chunks after the first `0..u32::MAX` range. `target` is the original (unshifted) target.
/// Chunks are produced lazily, so memory stays bounded for large `max`.
#[cfg(feature = "parallel")]
fn solve_discrete_log_bsgs_tail<G: AdditiveGroup + CurveGroup>(
    max: u64,
    baby_steps: &BabyStepsTable,
    base_m: G,
    target: G,
) -> Option<u64> {
    use rayon::prelude::*;

    let base_u32_max: G = baby_steps.base_u32_max();
    let mut starting_point = target;
    const CHUNK_SIZE: u64 = u32::MAX as u64;
    let chunk_count = (max + CHUNK_SIZE - 1) / CHUNK_SIZE;
    (1..chunk_count)
        .into_iter()
        .filter_map(|idx| {
            let offset = idx * CHUNK_SIZE;
            if offset >= max {
                None
            } else {
                starting_point = starting_point - base_u32_max;
                Some((offset, starting_point))
            }
        })
        .par_bridge()
        .find_map_any(|(offset, starting_point)| {
            let span = CHUNK_SIZE.min(max - offset);
            let steps = (span + MAX_NUM_BABY_STEPS - 1) / MAX_NUM_BABY_STEPS;
            scan_single_strided(baby_steps, base_m, starting_point, steps).map(|v| v + offset)
        })
}
