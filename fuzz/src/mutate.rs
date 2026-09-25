//! Byte-level mutators used by the property tests to derive "mutated-valid" inputs from the
//! seed corpus. Coverage-guided fuzzing (`cargo fuzz`) has its own mutators; these are for the
//! deterministic `cargo test` harness.

use rand_core::RngCore;

/// One mutation step. Kept small and structural so a single mutated seed still decodes most of
/// the time (which is what reaches the deep verifier paths).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mutation {
    /// Flip one random bit.
    FlipBit,
    /// Overwrite one byte with a random value.
    SetByte,
    /// Overwrite one byte with an "interesting" value (0, 1, 0x7f, 0x80, 0xff).
    SetInteresting,
    /// Set a random byte to zero (turns points into identity / options into `None`).
    ZeroByte,
    /// Truncate to a random shorter length.
    Truncate,
    /// Append random bytes.
    Extend,
    /// Delete a random byte range.
    DeleteRange,
    /// Duplicate a random byte range in place.
    DuplicateRange,
    /// Overwrite a random 32-byte-aligned window with another 32-byte window from the same
    /// input (swaps curve points / scalars between fields).
    SwapWord32,
    /// Overwrite a SCALE compact length prefix candidate with a large value.
    BigLength,
}

pub const ALL_MUTATIONS: &[Mutation] = &[
    Mutation::FlipBit,
    Mutation::SetByte,
    Mutation::SetInteresting,
    Mutation::ZeroByte,
    Mutation::Truncate,
    Mutation::Extend,
    Mutation::DeleteRange,
    Mutation::DuplicateRange,
    Mutation::SwapWord32,
    Mutation::BigLength,
];

const INTERESTING: &[u8] = &[0x00, 0x01, 0x02, 0x7f, 0x80, 0xfe, 0xff];

fn below(rng: &mut impl RngCore, n: usize) -> usize {
    if n == 0 {
        0
    } else {
        (rng.next_u64() % n as u64) as usize
    }
}

/// Apply `m` to `data` in place.
pub fn apply(m: Mutation, data: &mut Vec<u8>, rng: &mut impl RngCore) {
    if data.is_empty() {
        data.push(rng.next_u32() as u8);
        return;
    }
    let len = data.len();
    match m {
        Mutation::FlipBit => {
            let i = below(rng, len);
            data[i] ^= 1 << below(rng, 8);
        }
        Mutation::SetByte => {
            let i = below(rng, len);
            data[i] = rng.next_u32() as u8;
        }
        Mutation::SetInteresting => {
            let i = below(rng, len);
            data[i] = INTERESTING[below(rng, INTERESTING.len())];
        }
        Mutation::ZeroByte => {
            let i = below(rng, len);
            data[i] = 0;
        }
        Mutation::Truncate => {
            let new_len = below(rng, len);
            data.truncate(new_len);
        }
        Mutation::Extend => {
            let n = 1 + below(rng, 64);
            for _ in 0..n {
                data.push(rng.next_u32() as u8);
            }
        }
        Mutation::DeleteRange => {
            let start = below(rng, len);
            let n = 1 + below(rng, (len - start).min(64));
            data.drain(start..start + n);
        }
        Mutation::DuplicateRange => {
            let start = below(rng, len);
            let n = 1 + below(rng, (len - start).min(64));
            let chunk = data[start..start + n].to_vec();
            let at = below(rng, len + 1);
            data.splice(at..at, chunk);
        }
        Mutation::SwapWord32 => {
            if len >= 64 {
                let words = len / 32;
                let a = below(rng, words) * 32;
                let b = below(rng, words) * 32;
                let src = data[b..b + 32].to_vec();
                data[a..a + 32].copy_from_slice(&src);
            } else {
                let i = below(rng, len);
                data[i] = rng.next_u32() as u8;
            }
        }
        Mutation::BigLength => {
            // SCALE compact: 0b..01 = two-byte mode, 0b..10 = four-byte mode. Write a large
            // 4-byte compact length at a random position.
            let i = below(rng, len);
            let big: u32 = [0xffff_ffff, 0x4000_0000, 0x0010_0000, 0x0000_ffff][below(rng, 4)];
            let enc = ((big << 2) | 0b10).to_le_bytes();
            for (k, b) in enc.iter().enumerate() {
                if i + k < data.len() {
                    data[i + k] = *b;
                } else {
                    data.push(*b);
                }
            }
        }
    }
}

/// Apply `count` random mutations from `ALL_MUTATIONS`.
pub fn mutate_n(data: &mut Vec<u8>, count: usize, rng: &mut impl RngCore) {
    for _ in 0..count {
        let m = ALL_MUTATIONS[below(rng, ALL_MUTATIONS.len())];
        apply(m, data, rng);
    }
}
