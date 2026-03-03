/// Verify a proof using either `RandomizedMultChecker` (batched verification) or direct
/// `verify` (individual verification).
///
/// For proof types with **2 owned-or-ref** arguments (e.g., `PartialPokDiscreteLog`, `PokDiscreteLog`).
///
/// The first 2 args after `$err` are the "switchable" arguments: passed by value to
/// `verify_using_randomized_mult_checker` and by reference to `verify`.
/// Remaining args are passed through unchanged (typically already references like `&challenge`).
///
macro_rules! verify_or_rmc_2 {
    ($rmc:expr, $proof:expr, $err:expr, $o1:expr, $o2:expr $(, $ref_arg:expr)* $(,)?) => {{
        match $rmc.as_mut() {
            Some(__rmc) => {
                $proof.verify_using_randomized_mult_checker($o1, $o2, $($ref_arg,)* __rmc);
            }
            None => {
                if !$proof.verify(&$o1, &$o2, $($ref_arg,)*) {
                    return Err($crate::Error::ProofVerificationError($err.into()));
                }
            }
        }
    }};
}

/// Same as [`verify_or_rmc_2`] but for proof types with **3 owned-or-ref** arguments
/// (e.g., `PartialPokPedersenCommitment`, `PokPedersenCommitment`, `Partial2PokPedersenCommitment`).
macro_rules! verify_or_rmc_3 {
    ($rmc:expr, $proof:expr, $err:expr, $o1:expr, $o2:expr, $o3:expr $(, $ref_arg:expr)* $(,)?) => {{
        match $rmc.as_mut() {
            Some(__rmc) => {
                $proof.verify_using_randomized_mult_checker($o1, $o2, $o3, $($ref_arg,)* __rmc);
            }
            None => {
                if !$proof.verify(&$o1, &$o2, &$o3, $($ref_arg,)*) {
                    return Err($crate::Error::ProofVerificationError($err.into()));
                }
            }
        }
    }};
}

/// Verify a [`SchnorrResponse`] (vector Pedersen commitment) using either
/// `verify_using_randomized_mult_checker` or `is_valid`.
///
/// Both variants return `Result<()>` (propagated with `?`).
/// The bases, commitment point, and t-value are switchable between owned and ref.
macro_rules! verify_schnorr_resp_or_rmc {
    ($rmc:expr, $resp:expr, $bases:expr, $y:expr, $t:expr, $challenge:expr $(,)?) => {{
        match $rmc.as_mut() {
            Some(__rmc) => {
                $resp.verify_using_randomized_mult_checker($bases, $y, $t, $challenge, __rmc)?;
            }
            None => {
                $resp.is_valid(&$bases, &$y, &$t, $challenge)?;
            }
        }
    }};
}

/// Same as [`verify_schnorr_resp_or_rmc!`] but for [`PartialSchnorrResponse`] which additionally
/// takes a `missing_resps` [`BTreeMap`] passed by value to both paths.
macro_rules! verify_partial_schnorr_resp_or_rmc {
    ($rmc:expr, $resp:expr, $bases:expr, $y:expr, $t:expr, $challenge:expr, $missing_resps:expr $(,)?) => {{
        match $rmc.as_mut() {
            Some(__rmc) => {
                $resp.verify_using_randomized_mult_checker(
                    $bases,
                    $y,
                    $t,
                    $challenge,
                    $missing_resps,
                    __rmc,
                )?;
            }
            None => {
                $resp.is_valid(&$bases, &$y, &$t, $challenge, $missing_resps)?;
            }
        }
    }};
}
