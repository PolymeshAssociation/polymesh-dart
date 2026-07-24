use scale_info::{Path, Type, TypeInfo, build::Fields};

use crate::*;

// The wire-encoding types are shared with the device wire API and live in polymesh-dart-auth.
pub use polymesh_dart_auth::wrapper::{
    ARK_EC_BASE_FIELD_SIZE, ARK_EC_POINT_SIZE, BaseField, BoundedCanonical, CompressedAffine,
    CompressedBaseField, CompressedPoint, WrappedCanonical,
};

impl TypeInfo for DartBPGenerators {
    type Identity = Self;

    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("DartBPGenerators", module_path!()))
            .composite(
                Fields::named()
                    .field(|f| f.name("sig_key_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("enc_key_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("account_comm_key").ty::<AccountCommitmentKey>())
                    .field(|f| f.name("leg_asset_value_gen").ty::<CompressedAffine>()),
            )
    }
}

impl TypeInfo for AccountCommitmentKey {
    type Identity = Self;

    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("AccountCommitmentKey", module_path!()))
            .composite(
                Fields::named()
                    .field(|f| f.name("sk_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("balance_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("counter_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("asset_id_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("rho_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("current_rho_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("randomness_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("current_randomness_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("identity_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("sk_gen").ty::<CompressedAffine>()),
            )
    }
}
