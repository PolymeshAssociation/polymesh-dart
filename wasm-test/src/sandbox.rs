use anyhow::Result;

use wasmtime::*;
use wasmtime_wasi::sync::WasiCtxBuilder;
use wasmtime_wasi::WasiCtx;

pub struct WasiAppSandboxed {
    engine: Engine,
    instance_pre: InstancePre<WasiCtx>,
}

impl WasiAppSandboxed {
    pub fn new() -> Result<Self> {
        let engine = Engine::default();
        let mut linker = Linker::new(&engine);
        wasmtime_wasi::add_to_linker(&mut linker, |s: &mut WasiCtx| s)?;

        let wasm = include_bytes!("wasi-module.wasm");
        let module = Module::from_binary(&engine, wasm)?;

        log::debug!("Link wasi-component.");
        let instance_pre = linker.instantiate_pre(&module)?;

        Ok(Self {
            engine,
            instance_pre,
        })
    }

    pub fn run(&self) -> Result<()> {
        let wasi = WasiCtxBuilder::new()
            .inherit_stdio()
            .inherit_args()?
            .inherit_env()?
            .build();

        let mut store = Store::new(&self.engine, wasi);

        log::debug!("Run wasi-component.");
        self.instance_pre
            .instantiate(&mut store)?
            .get_typed_func::<(), ()>(&mut store, "_start")?
            .call(&mut store, ())?;

        drop(store);

        Ok(())
    }
}
