//! The code catalog in `tests/DIAGNOSTICS.md` and the one the toolchain serves must list the
//! same codes with the same kinds.

use std::collections::BTreeMap;
use std::path::Path;

use proviso_syntax::diag::codes;

#[test]
fn documented_catalog_matches_the_toolchain() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/DIAGNOSTICS.md");
    let text = std::fs::read_to_string(&path).expect("tests/DIAGNOSTICS.md is readable");
    let documented: BTreeMap<String, String> = text
        .lines()
        .filter_map(|line| {
            let mut cells = line.split('|').map(str::trim).skip(1);
            let id = cells.next()?;
            let kind = cells.next()?.trim_matches('`');
            let is_code = id.len() == 5 && id.starts_with('E') && id[1..].chars().all(|c| c.is_ascii_digit());
            is_code.then(|| (id.to_string(), kind.to_string()))
        })
        .collect();
    let served: BTreeMap<String, String> =
        codes::ALL.iter().map(|code| (code.id.to_string(), code.kind.to_string())).collect();
    assert_eq!(documented, served, "tests/DIAGNOSTICS.md and crates/syntax/src/diag.rs disagree");
}

#[test]
fn codes_are_unique_and_in_order() {
    let ids: Vec<&str> = codes::ALL.iter().map(|code| code.id).collect();
    let mut sorted = ids.clone();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(ids, sorted, "codes must be unique and listed in numeric order");
}
