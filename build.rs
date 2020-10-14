use std::{
    env, fs,
    path::Path,
    process::{Command, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
};

fn main() {
    if compiles("pub use core::sync::atomic::AtomicUsize;").is_some() {
        println!("cargo:rustc-cfg=target_atomic_usize");
    }

    if compiles("pub use core::sync::atomic::AtomicU8;").is_some() {
        println!("cargo:rustc-cfg=target_atomic_u8");
    }

    if compiles("pub use core::sync::atomic::AtomicBool;").is_some() {
        println!("cargo:rustc-cfg=target_atomic_bool");
    }
}

fn compiles(code: &str) -> Option<()> {
    let rustc = env::var_os("RUSTC")?;
    let out_dir = env::var_os("OUT_DIR")?;

    static PROBES: AtomicUsize = AtomicUsize::new(1);
    let probe_id = PROBES.fetch_add(1, Ordering::SeqCst);

    let file = Path::new(&out_dir).join(format!("probe{}.rs", probe_id));
    let probe = format!("#![no_std]\n#![allow(dead_code)]\n{}\n", code);
    fs::write(&file, probe.as_str()).ok()?;

    match Command::new(rustc)
        .stderr(Stdio::null())
        .arg("--edition=2018")
        .arg(format!("--crate-name=usync_build_{}", probe_id).as_str())
        .arg("--crate-type=lib")
        .arg("--emit=metadata")
        .arg("--out-dir")
        .arg(out_dir)
        .arg(file)
        .status()
        .ok()
    {
        Some(status) if status.success() => Some(()),
        _ => None,
    }
}
