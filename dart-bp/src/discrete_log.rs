use ark_ec::CurveGroup;
use ark_ff::AdditiveGroup;
// Use BTreeMap for no_std compatibility
#[cfg(not(feature = "std"))]
use ark_std::{collections::BTreeMap as HashMap, sync::Arc};
#[cfg(feature = "std")]
use std::{collections::HashMap, sync::Arc};

#[cfg(feature = "large_baby_steps")]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 21;
#[cfg(not(feature = "large_baby_steps"))]
pub const MAX_NUM_BABY_STEPS: u64 = 1 << 16;

pub struct BabyStepsTable {
    pub base_m: [u8; 32],
    pub base_u32_max: [u8; 32],
    pub table: HashMap<[u8; 32], u32>,
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
        let chunk_base = base * G::ScalarField::from(chunk_size);
        let mut starting_point = base;
        let table = (0..chunk_count)
            .into_iter()
            .map(|chunk_idx| {
                let offset = 2 + chunk_idx * chunk_size;
                if chunk_idx > 0 {
                    starting_point = starting_point + chunk_base;
                }
                (offset, starting_point)
            })
            .par_bridge()
            .flat_map(|(offset, starting_point)| {
                let mut points = Vec::new();
                let mut cur = starting_point;
                for i in 0..=chunk_size {
                    cur = cur + base;
                    let cur_bytes = group_element_to_bytes(&cur)
                        .expect("Serialization of group element should not fail");
                    points.push((cur_bytes, (offset + i) as _));
                }
                points
            })
            .collect();
        starting_point = starting_point + chunk_base - base;

        let base_u32_max = base * G::ScalarField::from(u32::MAX as u64);
        Some(Self {
            base_m: group_element_to_bytes(&starting_point)?,
            base_u32_max: group_element_to_bytes(&base_u32_max)?,
            table,
        })
    }

    #[cfg(not(feature = "parallel"))]
    pub fn new<G: AdditiveGroup + CurveGroup>(base: G) -> Option<Self> {
        let mut table = HashMap::new();
        let base_bytes = group_element_to_bytes(&base)?;
        table.insert(base_bytes, 1);
        let mut cur = base;
        for i in 2..=MAX_NUM_BABY_STEPS {
            cur = cur + base;
            let cur_bytes = group_element_to_bytes(&cur)?;
            table.insert(cur_bytes, i);
        }
        let base_u32_max = base * G::ScalarField::from(u32::MAX as u64);
        Some(Self {
            base_m: group_element_to_bytes(&cur)?,
            base_u32_max: group_element_to_bytes(&base_u32_max)?,
            table,
        })
    }

    pub fn get<G: AdditiveGroup + CurveGroup>(&self, target: &G) -> Option<u64> {
        let target_bytes =
            group_element_to_bytes(target).expect("Serialization of group element should not fail");
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
    if let Some(b) = baby_steps.get(&target) {
        return Some(b);
    }
    let base_m: G = baby_steps.base_m();
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

#[cfg(feature = "parallel")]
fn solve_discrete_log_bsgs_u32<G: AdditiveGroup + CurveGroup>(
    max: u64,
    baby_steps: &BabyStepsTable,
    target: G,
) -> Option<u64> {
    if let Some(b) = baby_steps.get(&target) {
        return Some(b);
    }
    let base_m: G = baby_steps.base_m();
    let mut cur = target;
    let mut cur_offset = 0u64;
    const NUM_GIANT_STEPS_U32: u64 =
        (u32::MAX as u64 + MAX_NUM_BABY_STEPS - 1) / MAX_NUM_BABY_STEPS;
    for _ in 0..NUM_GIANT_STEPS_U32 {
        if let Some(b) = baby_steps.get(&cur) {
            return Some(cur_offset + b);
        }
        cur_offset += MAX_NUM_BABY_STEPS;
        if cur_offset >= max {
            break;
        }
        cur = cur - base_m;
    }
    None
}

#[cfg(feature = "parallel")]
pub fn solve_discrete_log_bsgs<G: AdditiveGroup + CurveGroup>(
    max: u64,
    base: G,
    target: G,
) -> Option<u64> {
    use rayon::prelude::*;

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
    if let Some(v) = solve_discrete_log_bsgs_u32(max, &baby_steps, target) {
        return Some(v);
    }
    if max <= u32::MAX as u64 {
        return None;
    }
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
            solve_discrete_log_bsgs_u32(u64::MAX, &baby_steps, starting_point).map(|v| v + offset)
        })
}
