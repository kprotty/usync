fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let santizer_list = std::env::var("CARGO_CFG_SANITIZE").unwrap_or_default();
    if santizer_list.contains("thread") {
        println!("cargo:rustc-cfg=usync_tsan_enabled");
    }
}
