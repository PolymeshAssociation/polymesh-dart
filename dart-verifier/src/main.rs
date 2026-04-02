use polkavm::{Config, Engine, InterruptKind, Linker, Module, ProgramBlob, Reg};

fn main() {
    env_logger::init();

    let raw_blob = include_bytes!("../../sandboxed/polymesh-dart-sandboxed.polkavm");
    let blob = ProgramBlob::parse(raw_blob[..].into()).unwrap();

    let config = Config::from_env().unwrap();
    let engine = Engine::new(&config).unwrap();
    let module = Module::from_blob(&engine, &Default::default(), blob).unwrap();

    // High-level API.
    let mut linker: Linker = Linker::new();

    // Define a host function.
    linker
        .define_typed("get_third_number", || -> u32 { 100 })
        .unwrap();

    // Link the host functions with the module.
    let instance_pre = linker.instantiate_pre(&module).unwrap();

    // Instantiate the module.
    let mut instance = instance_pre.instantiate().unwrap();

    // init parameters
    let now = std::time::Instant::now();
    let result = instance
        .call_typed_and_get_result::<u32, ()>(&mut (), "init_params", ())
        .unwrap();
    println!("init_params result: {result}");
    println!("Time taken for init_params: {:?}", now.elapsed());

    // get parameters
    let now = std::time::Instant::now();
    let result = instance
        .call_typed_and_get_result::<u32, ()>(&mut (), "get_params", ())
        .unwrap();
    println!("get_params result: {result}");
    println!("Time taken for get_params: {:?}", now.elapsed());

    for idx in 0..10 {
        let now = std::time::Instant::now();
        // Grab the function and call it.
        println!("{idx}: Calling into the guest program (high level):");
        let result = instance
            .call_typed_and_get_result::<u32, ()>(
                &mut (),
                "verify_register_account_asset_proof",
                (),
            )
            .unwrap();
        println!("{idx}: verify_register_account_asset_proof result: {result}");
        println!("{idx}:   Time taken: {:?}", now.elapsed());
    }
    println!("Finished");

    for idx in 0..10 {
        let now = std::time::Instant::now();
        // Grab the function and call it.
        println!("{idx}: Calling into the guest program (high level):");
        let result = instance
            .call_typed_and_get_result::<u32, ()>(&mut (), "verify_sender_affirm_proof", ())
            .unwrap();
        println!("{idx}: verify_sender_affirm_proof result: {result}");
        println!("{idx}:   Time taken: {:?}", now.elapsed());
    }
    println!("Finished");
}
