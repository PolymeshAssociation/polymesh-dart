use crate::poseidon_impls::utils::{mat_inverse, mat_vec_mul};
use crate::{Error, error::Result};
use ark_ff::PrimeField;
use ark_std::{vec, vec::Vec};

#[derive(Clone, Debug)]
pub struct Poseidon2Params<F: PrimeField> {
    pub state_size: usize,
    /// sbox degree
    pub degree: usize,
    pub rounds_f_beginning: usize,
    pub rounds_p: usize,
    #[allow(dead_code)]
    pub rounds_f_end: usize,
    pub rounds: usize,
    pub mat_internal_diag_m_1: Vec<F>,
    pub _mat_internal: Vec<Vec<F>>,
    pub round_constants: Vec<Vec<F>>,
}

impl<F: PrimeField> Poseidon2Params<F> {
    pub fn new(
        state_size: usize,
        degree: usize,
        rounds_f: usize,
        rounds_p: usize,
        mat_internal_diag_m_1: Vec<F>,
        mat_internal: Vec<Vec<F>>,
        round_constants: Vec<Vec<F>>,
    ) -> Result<Self> {
        // We only need t to be 3 for now. Support for 2 is simple so keeping it
        if state_size != 2 && state_size != 3 {
            return Err(Error::UnexpectedStateSizeForPoseidon2(state_size));
        }
        if degree != 3 && degree != 5 && degree != 7 {
            return Err(Error::UnexpectedDegreeForPoseidon2(degree));
        }
        if rounds_f % 2 == 1 {
            return Err(Error::IncorrectNumberOfFullRoundsForPoseidon2(rounds_f));
        }
        let r = rounds_f / 2;
        let rounds = rounds_f + rounds_p;

        Ok(Poseidon2Params {
            state_size,
            degree,
            rounds_f_beginning: r,
            rounds_p,
            rounds_f_end: r,
            rounds,
            mat_internal_diag_m_1,
            _mat_internal: mat_internal,
            round_constants,
        })
    }

    /// Only for testing purposes
    #[cfg(test)]
    pub fn new_with_randoms<R: rand_core::CryptoRngCore>(
        rng: &mut R,
        state_size: usize,
        degree: usize,
        rounds_f: usize,
        rounds_p: usize,
    ) -> Result<Self> {
        let mat_internal_diag_m_1: Vec<F> = (0..state_size).map(|_| F::rand(rng)).collect();
        let mat_internal: Vec<Vec<F>> = (0..state_size)
            .map(|_| (0..state_size).map(|_| F::rand(rng)).collect())
            .collect();
        let round_constants: Vec<Vec<F>> = (0..(rounds_f + rounds_p))
            .map(|_| (0..state_size).map(|_| F::rand(rng)).collect())
            .collect();

        Self::new(
            state_size,
            degree,
            rounds_f,
            rounds_p,
            mat_internal_diag_m_1,
            mat_internal,
            round_constants,
        )
    }

    #[allow(dead_code)]
    pub fn equivalent_round_constants(
        round_constants: &[Vec<F>],
        mat_internal: &[Vec<F>],
        rounds_f_beginning: usize,
        rounds_p: usize,
    ) -> Vec<Vec<F>> {
        let mut opt = vec![Vec::new(); rounds_p + 1];
        let mat_internal_inv = mat_inverse(mat_internal);

        let p_end = rounds_f_beginning + rounds_p - 1;
        let mut tmp = round_constants[p_end].clone();
        for i in (0..rounds_p - 1).rev() {
            let inv_cip = mat_vec_mul(&mat_internal_inv, &tmp);
            opt[i + 1] = vec![inv_cip[0]];
            tmp = round_constants[rounds_f_beginning + i].clone();
            for i in 1..inv_cip.len() {
                tmp[i] += inv_cip[i];
            }
        }
        opt[0] = tmp;
        opt[rounds_p] = vec![F::zero(); opt[0].len()]; // opt[0].len() = t

        opt
    }
}

/// `temp` is like a scratchpad used for writing the decoded bytes. Its passed to avoid allocating a new array on each call to `from_hex`
fn from_hex<F: PrimeField>(s: &str, temp: &mut [u8]) -> Result<F> {
    hex::decode_to_slice(&s[2..], temp).map_err(|_| Error::InvalidHexString)?;
    let f = F::from_be_bytes_mod_order(temp);
    temp.fill(0);
    Ok(f)
}

pub mod pallas {
    use super::*;
    use ark_ff::{One, Zero};
    use ark_pallas::Fr as PallasFr;
    #[cfg(not(feature = "std"))]
    use ark_std::boxed::Box;
    #[cfg(feature = "std")]
    use ark_std::sync::LazyLock;
    #[cfg(not(feature = "std"))]
    use once_cell::race::OnceBox;

    pub fn get_poseidon2_params_for_2_1_hashing() -> Result<Poseidon2Params<PallasFr>> {
        // NOTE: These numbers are for 2:1 compression and 256 bit group (Table 1 from Poseidon2 paper) and that is the only config we use.
        // These should be changed if we decide to use something else.
        let full_rounds = 8;
        let partial_rounds = 56;
        let degree = 5;

        #[cfg(feature = "std")]
        return Poseidon2Params::<PallasFr>::new(
            3,
            degree,
            full_rounds,
            partial_rounds,
            MAT_DIAG3_M_1.to_vec(),
            MAT_INTERNAL3.to_vec(),
            RC3.as_ref().unwrap().to_vec(),
        );

        #[cfg(not(feature = "std"))]
        return Poseidon2Params::<PallasFr>::new(
            3,
            degree,
            full_rounds,
            partial_rounds,
            init_mat_diag3().clone(),
            init_mat_internal3().clone(),
            init_round_constants()?.clone(),
        );
    }

    #[cfg(feature = "std")]
    pub static MAT_DIAG3_M_1: LazyLock<Vec<PallasFr>> = LazyLock::new(|| get_mat_diag3_m1());

    #[cfg(feature = "std")]
    pub static MAT_INTERNAL3: LazyLock<Vec<Vec<PallasFr>>> = LazyLock::new(|| get_internal3());

    #[cfg(feature = "std")]
    pub static RC3: LazyLock<Result<Vec<Vec<PallasFr>>>> = LazyLock::new(|| get_round_constants());

    #[cfg(not(feature = "std"))]
    pub static MAT_DIAG3_M_1: OnceBox<Vec<PallasFr>> = OnceBox::new();

    #[cfg(not(feature = "std"))]
    pub static MAT_INTERNAL3: OnceBox<Vec<Vec<PallasFr>>> = OnceBox::new();

    #[cfg(not(feature = "std"))]
    pub static RC3: OnceBox<Vec<Vec<PallasFr>>> = OnceBox::new();

    #[cfg(not(feature = "std"))]
    pub fn init_mat_diag3() -> &'static Vec<PallasFr> {
        MAT_DIAG3_M_1.get_or_init(|| Box::new(get_mat_diag3_m1()))
    }

    #[cfg(not(feature = "std"))]
    pub fn init_mat_internal3() -> &'static Vec<Vec<PallasFr>> {
        MAT_INTERNAL3.get_or_init(|| Box::new(get_internal3()))
    }

    #[cfg(not(feature = "std"))]
    pub fn init_round_constants() -> Result<&'static Vec<Vec<PallasFr>>, crate::Error> {
        if let Some(constants) = RC3.get() {
            return Ok(constants);
        }

        // Initialize constants if not already done
        let constants = get_round_constants()?;
        match RC3.set(Box::new(constants)) {
            Ok(()) => Ok(RC3.get().unwrap()),
            Err(_) => {
                // Another thread may have set it already, that's fine
                Ok(RC3.get().unwrap())
            }
        }
    }

    // Parameters taken from https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_pallas.rs

    fn get_mat_diag3_m1() -> Vec<PallasFr> {
        vec![PallasFr::one(), PallasFr::one(), PallasFr::from(2_u64)]
    }

    fn get_internal3() -> Vec<Vec<PallasFr>> {
        vec![
            vec![PallasFr::from(2_u64), PallasFr::one(), PallasFr::one()],
            vec![PallasFr::one(), PallasFr::from(2_u64), PallasFr::one()],
            vec![PallasFr::one(), PallasFr::one(), PallasFr::from(3_u64)],
        ]
    }

    fn get_round_constants() -> Result<Vec<Vec<PallasFr>>> {
        let mut temp = [0u8; 32];
        Ok(vec![
            vec![
                from_hex::<PallasFr>(
                    "0x360d7470611e473d353f628f76d110f34e71162f31003b7057538c2596426303",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x2bab94d7ae222d135dc3c6c5febfaa314908ac2f12ebe06fbdb74213bf63188b",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x150c93fef652fb1c2bf03e1a29aa871fef77e7d736766c5d0939d92753cc5dc8",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3270661e68928b3a955d55db56dc57c103cc0a60141e894e14259dce537782b2",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x073f116f04122e25a0b7afe4e2057299b407c370f2b5a1ccce9fb9ffc345afb3",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x2a32ec5c4ee5b1837affd09c1f53f5fd55c9cd2061ae93ca8ebad76fc71554d8",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x270326ee039df19e651e2cfc740628ca634d24fc6e2559f22d8ccbe292efeead",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x27c6642ac633bc66dc100fe7fcfa54918af895bce012f182a068fc37c182e274",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x1bdfd8b01401c70ad27f57396989129d710e1fb6ab976a459ca18682e26d7ff9",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x162a14c62f9a89b814b9d6a9c84dd678f4f6fb3f9054d373c832d824261a35ea",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x2d193e0f76de586b2af6f79e3127feeaac0a1fc71e2cf0c0f79824667b5b6bec",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x044ca3cc4a85d73b81696ef1104e674f4feff82984990ff85d0bf58dc8a4aa94",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1cbaf2b371dac6a81d0453416d3e235cb8d9e2d4f314f46f6198785f0cd6b9af",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1d5b2777692c205b0e6c49d061b6b5f4293c4ab038fdbbdc343e07610f3fede5",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2e9bdbba3dd34bffaa30535bdd749a7e06a9adb0c1e6f962f60e971b8d73b04f",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2de11886b18011ca8bd5bae36969299fde40fbe26d047b05035a13661f22418b",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2e07de1780b8a70d0d5b4a3f1841dcd82ab9395c449be947bc998884ba96a721",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x0f69f1854d20ca0cbbdb63dbd52dad16250440a99d6b8af3825e4c2bb74925ca",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2eb1b25417fe17670d135dc639fb09a46ce5113507f96de9816c059422dc705e",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x115cd0a0643cfb988c24cb44c3fab48aff36c661d26cc42db8b1bdf4953bd82c",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x26ca293f7b2c462d066d7378b999868bbb57ddf14e0f958ade801612311d04cd",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x17bf1b93c4c7e01a2a830aa162412cd90f160bf9f71e967ff5209d14b24820ca",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x35b41a7ac4f3c571a24f8456369c85dfe03c0354bd8cfd3805c86f2e7dc293c5",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3b1480080523c439435927994849bea964e14d3beb2dddde72ac156af435d09e",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2cc6810031dc1b0d4950856dc907d57508e286442a2d3eb2271618d874b14c6d",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x25bdbbeda1bde8c1059618e2afd2ef999e517aa93b78341d91f318c09f0cb566",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x392a4a8758e06ee8b95f33c25dde8ac02a5ed0a27b61926cc6313487073f7f7b",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x272a55878a08442b9aa6111f4de009485e6a6fd15db89365e7bbcef02eb5866c",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2d5b308b0cf02cdfefa13c4e60e26239a6ebba011694dd129b925b3c5b21e0e2",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x16549fc6af2f3b72dd5d293d72e2e5f244dff42f18b46c56ef38c57c311673ac",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1b10bb7a82afce39fa69c3a2ad52f76d76398265344203119b7126d9b46860df",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x0f1e7505ebd91d2fc79c2df7dc98a3bed1b36968ba0405c090d27f6a00b7dfc8",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2f313faf0d3f6187537a7497a3b43f46797fd6e3f18eb1caff457756b819bb20",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3a5cbb6de450b481fa3ca61c0ed15bc55cad11ebf0f7ceb8f0bc3e732ecb26f6",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3dab54bc9bef688dd92086e253b439d651baa6e20f892b62865527cbca915982",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x06dbfb42b979884de280d31670123f744c24b33b410fefd4368045acf2b71ae3",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x068d6b4608aae810c6f039ea1973a63eb8d2de72e3d2c9eca7fc32d22f18b9d3",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x366ebfafa3ad381c0ee258c9b8fdfccdb868a7d7e1f1f69a2b5dfcc5572555df",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x39678f65512f1ee404db3024f41d3f567ef66d89d044d022e6bc229e95bc76b1",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x21668f016a8063c0d58b7750a3bc2fe1cf82c25f99dc01a4e534c88fe53d85fe",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x39d00994a8a5046a1bc749363e98a768e34dea56439fe1954bef429bc5331608",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1f9dbdc3f84312636b203bbe12fb3425b163d41605d39f99770c956f60d881b3",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x027745a9cddfad95e5f17b9e0ee0cab6be0bc829fe5e66c69794a9f7c336eab2",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1cec0803c504b635788d695c61e932122fa43fe20a45c78d52025657abd8aee0",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x123523d75e9fabc172077448ef87cc6eed5082c8dbf31365d3872a9559a03a73",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1723d1452c9cf02df419b848e5d694bf27feba35975ee7e5001779e3a1d357f4",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1739d180a16010bdfcc0573d7e61369421c3f776f572836d9dab1ee4dcf96622",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x2d4e6354da9cc554acce32391794b627fafa96fbeb0ab89370290452042d048d",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x153ee6142e535e334a869553c9d007f88f3bd43f99260621670bcf6f8b485dcd",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x0c45bfd3a69aaa65635ef7e7a430b486968ad4424af83700d258d2e2b7782172",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x0adfd53b256a6957f2d56aec831446006897ac0a8ffa5ff10e5633d251f73307",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x315d2ac8ebdbac3c8cd1726b7cbab8ee3f87b28f1c1be4bdac9d36a8b7516d63",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x1b8472712d02eef4cfaec23d2b16883fc9bb60d1f6959879299ce44ea423d8e1",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3c1cd07efda6ff24bd0b70fa2255eb6f367d2c54e36928c9c4a5404198adf70c",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x136052d26bb3d373687f4e51b2e1dcd34a16073f738f7e0cbbe523aef9ab107a",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x16c96beef6a0a848c1bdd859a1232a1d7b3cfbb873032681676c36c24ef967dd",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x284b38c57ff65c262ab7fed8f499a9fb012387bab4f1662d067eec7f2d6340c4",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x0c5993d175e81f6639e242198897d17cfc06772c1c0411a6af1dff204c922f86",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x03bf7a3f7bd043dafcda655d1ba9c8f9f24887ad48e17759bbf53f67b1f87b15",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3188fe4ee9f9fafbb0cf999567f00e734c8f9cbe69f0e8279b5cd09e36d8be62",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x171f528ccf6584375a39768c480d61e13af5bf77c1c42652afea99a2ec6c595a",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x12f4175c4ab45afc196e41859b35ef88812c3286ee7000675a0563b9b8e9f1d5",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x3a509e155cb7ebfd8f8fdcf800a9ac697e23e1aabe96cfab0e74d4d369118b79",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x10f2a685df4a27c81a89920e2504c3b3984bc8f2e4c1b69e98712c65678cfd30",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x09e5f49790c8a0e21d8d93d54ab91a0e54573c9333c56321e8a16728cc9d4918",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x352d69bed80ee3e52bf35705d9f84a3442d17ed6ee0fab7e609a740347cf5fea",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x058ee73ba9f3f293491562faf2b190d3c634debd281b76a63a758af6fa84e0e8",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x232f99cc911eddd9cd0f1fc55b1a3250092cb92119bc76be621a132510a43904",
                    &mut temp,
                )?,
                PallasFr::zero(),
                PallasFr::zero(),
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x201beed7b8f3ab8186c22c6c5d4869f0f9efd52ca6bc2961c3b97c1e301bc213",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x1376dce6580030c6a1c9291d58602f5129388842744a1210bf6b3431ba94e9bc",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x1793199e6fd6ba342b3356c38238f761072ba8b02d92e7226454843c5486d7b3",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x22de7a7488dcc7359fee9c20c87a67df3c66160dc62aacac06a3f1d3b433311b",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x3514d5e9066bb160df8ff37fe2d8edf8dbe0b77fae77e1d030d6e3fd516b47a8",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x30cd3006931ad636f919a00dabbf5fa5ff453d6f900f144a19377427137a81c7",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x253d1a5c5293412741f81a5cf613c8df8f9e4b2cae2ebb515b6a74220692b506",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x035b461c02d79d19a35e9613e7f5fe92851b3a59c990fafc73f666cb86a48e8e",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x23a9928079d175bd5bc00eedd56b93e092b1283c2d5fccde7cfbf86a3aa04780",
                    &mut temp,
                )?,
            ],
            vec![
                from_hex::<PallasFr>(
                    "0x13a7785ae134ea92f1594a0763c611abb5e2ea3436eef957f1e4ccd73fa00a82",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x39fce308b7d43c574962ae3c0da17e313889c57863446d88bbf04f5252de4279",
                    &mut temp,
                )?,
                from_hex::<PallasFr>(
                    "0x1aae18833f8e1d3ac0fdf01662f60d22bef00a08c6ed38d23b57e34489b53fad",
                    &mut temp,
                )?,
            ],
        ])
    }
}
