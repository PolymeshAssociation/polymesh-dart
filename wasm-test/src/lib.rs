#[cfg(feature = "sandbox")]
mod sandbox;

use codec::Encode;
use polymesh_dart::curve_tree::*;

pub fn print_tree_params(msg: &str) -> anyhow::Result<()> {
    let params = WrappedCurveTreeParameters::new::<AssetTreeConfig>()?;
    let buf = params.encode();

    println!("{msg}: First 32 bytes of encoded params: {:?}", &buf[..32]);

    Ok(())
}

pub fn run() -> anyhow::Result<()> {
    #[cfg(feature = "sandbox")]
    {
        println!("Running in sandboxed WASI mode.");
        let sandbox = sandbox::WasiAppSandboxed::new()?;
        sandbox.run()?;
    }

    #[cfg(not(target_arch = "wasm32"))]
    {
        println!("Running in native mode.");
        print_tree_params("Native")?;
    }

    #[cfg(target_arch = "wasm32")]
    {
        println!("Running in WASM32 mode.");
        print_tree_params("Wasi")?;
    }
    Ok(())
}
