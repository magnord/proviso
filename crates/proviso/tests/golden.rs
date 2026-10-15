//! Runs every golden file under `tests/golden`. Set `PROVISO_BLESS=1` to rewrite the
//! expected `.out` and `.err` files from the actual output.

use std::path::Path;

#[test]
fn golden_files() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/golden");
    let bless = std::env::var_os("PROVISO_BLESS").is_some();
    let report = proviso::golden::run_dir(&root, proviso::IMPLEMENTED_PHASE, bless);
    for name in &report.pending {
        println!("pending  {name}");
    }
    println!(
        "golden: {} passed, {} failed, {} pending (implemented phase {})",
        report.passed.len(),
        report.failed.len(),
        report.pending.len(),
        proviso::IMPLEMENTED_PHASE
    );
    let mut message = String::new();
    for (name, reason) in &report.failed {
        message.push_str(&format!("\n=== {name}\n{reason}\n"));
    }
    assert!(report.failed.is_empty(), "{} golden file(s) failed:{message}", report.failed.len());
    assert!(!report.passed.is_empty(), "no golden files found under {}", root.display());
}
