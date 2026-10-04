//! The name manifest `names.toml` against the source and against the hax
//! export.
//!
//! * Every entry names an item of a trait declared in `src/`: a constant for
//!   arity 0, otherwise a method with that many value parameters (`self`
//!   included). A rename or a change of arity in the source fails here.
//! * Every op key is `<family>.<op>` with a known family, and paths and keys
//!   are unique.
//! * When `hax_frontend_export.json` is present (it is not tracked), every
//!   `[[extracted]]` path is a def path of the export and no `[[pending]]`
//!   path is. A pending entry that the export carries has been re-extracted
//!   and moves to `[[extracted]]`.

use std::collections::HashSet;
use std::path::PathBuf;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Section {
    Extracted,
    Pending,
}

#[derive(Debug, Clone)]
struct Entry {
    section: Section,
    path: String,
    arity: usize,
    key: String,
}

const FAMILIES: [&str; 9] = [
    "field", "codec", "modarith", "ec", "ct", "sqrt", "ring", "tower", "gf2",
];

fn crate_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn unquote(v: &str) -> String {
    let v = v.trim();
    assert!(
        v.len() >= 2 && v.starts_with('"') && v.ends_with('"'),
        "names.toml: expected a quoted string, found {v}"
    );
    v[1..v.len() - 1].to_string()
}

/// The entries of `names.toml`, in the subset of TOML the file uses.
fn manifest() -> Vec<Entry> {
    let text = std::fs::read_to_string(crate_dir().join("names.toml")).expect("names.toml");
    let mut out: Vec<Entry> = Vec::new();
    let mut cur: Option<(Section, Option<String>, Option<usize>, Option<String>)> = None;
    let flush = |cur: &mut Option<(Section, Option<String>, Option<usize>, Option<String>)>,
                 out: &mut Vec<Entry>| {
        if let Some((section, path, arity, key)) = cur.take() {
            out.push(Entry {
                section,
                path: path.expect("names.toml: entry without path"),
                arity: arity.expect("names.toml: entry without arity"),
                key: key.expect("names.toml: entry without key"),
            });
        }
    };
    for (n, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[extracted]]" || line == "[[pending]]" {
            flush(&mut cur, &mut out);
            let section = if line == "[[extracted]]" {
                Section::Extracted
            } else {
                Section::Pending
            };
            cur = Some((section, None, None, None));
            continue;
        }
        let (k, v) = line
            .split_once('=')
            .unwrap_or_else(|| panic!("names.toml line {}: not `key = value`", n + 1));
        let entry = cur
            .as_mut()
            .unwrap_or_else(|| panic!("names.toml line {}: a field outside an entry", n + 1));
        match k.trim() {
            "path" => entry.1 = Some(unquote(v)),
            "arity" => entry.2 = Some(v.trim().parse().expect("names.toml: arity")),
            "key" => entry.3 = Some(unquote(v)),
            other => panic!("names.toml line {}: unknown field {other}", n + 1),
        }
    }
    flush(&mut cur, &mut out);
    out
}

/// The text of the trait `name` in `src`: from `pub trait name` to the first
/// closing brace in column 0.
fn trait_block<'a>(src: &'a str, name: &str) -> Option<&'a str> {
    let head = format!("pub trait {name}");
    let mut from = 0;
    while let Some(i) = src[from..].find(&head) {
        let start = from + i;
        let after = src[start + head.len()..].chars().next();
        if matches!(after, Some(':') | Some(' ') | Some('{') | Some('<')) {
            let end = src[start..].find("\n}").map(|j| start + j)?;
            return Some(&src[start..end]);
        }
        from = start + head.len();
    }
    None
}

/// The number of value parameters of `fn name(` in `block`, or `None` if the
/// block declares no such method.
fn method_arity(block: &str, name: &str) -> Option<usize> {
    let head = format!("fn {name}(");
    let i = block.find(&head)?;
    let rest = &block[i + head.len()..];
    let mut depth = 0i32;
    let mut params = 0usize;
    let mut seen = false;
    for c in rest.chars() {
        match c {
            '(' | '<' | '[' => {
                depth += 1;
                seen = true;
            }
            ')' | ']' if depth > 0 => depth -= 1,
            '>' if depth > 0 => depth -= 1,
            ')' => break,
            ',' if depth == 0 => {
                if seen {
                    params += 1;
                }
                seen = false;
            }
            c if !c.is_whitespace() => seen = true,
            _ => {}
        }
    }
    if seen {
        params += 1;
    }
    Some(params)
}

/// The file and trait of a qualified path, and the item name.
fn locate(path: &str) -> (PathBuf, String, String) {
    let segs: Vec<&str> = path.split("::").collect();
    assert_eq!(segs[0], "primeir_hax", "{path}: not a path of the crate");
    let (file, tr, item) = match segs.len() {
        3 => ("lib".to_string(), segs[1], segs[2]),
        4 => (segs[1].to_string(), segs[2], segs[3]),
        _ => panic!("{path}: expected crate::Trait::item or crate::module::Trait::item"),
    };
    (
        crate_dir().join("src").join(format!("{file}.rs")),
        tr.to_string(),
        item.to_string(),
    )
}

#[test]
fn manifest_is_well_formed() {
    let entries = manifest();
    assert!(!entries.is_empty());
    let mut paths = HashSet::new();
    let mut keys = HashSet::new();
    for e in &entries {
        assert!(paths.insert(e.path.clone()), "duplicate path {}", e.path);
        assert!(keys.insert(e.key.clone()), "duplicate key {}", e.key);
        let (family, op) = e
            .key
            .split_once('.')
            .unwrap_or_else(|| panic!("{}: key {} is not family.op", e.path, e.key));
        assert!(FAMILIES.contains(&family), "{}: unknown family {family}", e.path);
        assert!(!op.is_empty(), "{}: empty op in {}", e.path, e.key);
    }
}

#[test]
fn manifest_matches_the_trait_declarations() {
    for e in manifest() {
        let (file, tr, item) = locate(&e.path);
        let src = std::fs::read_to_string(&file)
            .unwrap_or_else(|_| panic!("{}: no source file {}", e.path, file.display()));
        let block = trait_block(&src, &tr)
            .unwrap_or_else(|| panic!("{}: no trait {tr} in {}", e.path, file.display()));
        if e.arity == 0 && item.chars().all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_') {
            assert!(
                block.contains(&format!("const {item}:")),
                "{}: trait {tr} declares no constant {item}",
                e.path
            );
        } else {
            let arity = method_arity(block, &item)
                .unwrap_or_else(|| panic!("{}: trait {tr} declares no method {item}", e.path));
            assert_eq!(arity, e.arity, "{}: arity in the source", e.path);
        }
    }
}

/// The def paths of the crate in the export, as `primeir_hax::a::b`, with a
/// segment without a name written `<Kind>`.
fn export_paths(json: &str) -> HashSet<String> {
    let head = "\"krate\":\"primeir_hax\",\"path\":[";
    let mut out = HashSet::new();
    let mut from = 0;
    while let Some(i) = json[from..].find(head) {
        let start = from + i + head.len();
        let end = start + json[start..].find(']').expect("unterminated path");
        let inner = &json[start..end];
        let mut names: Vec<String> = Vec::new();
        for seg in inner.split("{\"data\":").skip(1) {
            if let Some(rest) = seg.strip_prefix('"') {
                let kind = rest.split('"').next().unwrap_or("");
                names.push(format!("<{kind}>"));
            } else if let Some(rest) = seg.strip_prefix('{') {
                // `"Kind":"name"}` or `"Kind":<non-string>}`.
                let mut parts = rest.splitn(2, ':');
                let kind = parts.next().unwrap_or("").trim_matches('"');
                let val = parts.next().unwrap_or("");
                match val.strip_prefix('"') {
                    Some(v) => names.push(v.split('"').next().unwrap_or("").to_string()),
                    None => names.push(format!("<{kind}>")),
                }
            }
        }
        let mut p = String::from("primeir_hax");
        for n in &names {
            p.push_str("::");
            p.push_str(n);
        }
        out.insert(p);
        from = end;
    }
    out
}

#[test]
fn manifest_matches_the_export() {
    let file = crate_dir().join("hax_frontend_export.json");
    let json = match std::fs::read_to_string(&file) {
        Ok(j) => j,
        Err(_) => {
            eprintln!(
                "names_manifest: {} is absent; the check against the export is skipped",
                file.display()
            );
            return;
        }
    };
    let paths = export_paths(&json);
    assert!(
        paths.contains("primeir_hax::Field::mul"),
        "the export carries no def path primeir_hax::Field::mul; is it an export of this crate?"
    );
    let mut missing = Vec::new();
    let mut arrived = Vec::new();
    for e in manifest() {
        match e.section {
            Section::Extracted if !paths.contains(&e.path) => missing.push(e.path),
            Section::Pending if paths.contains(&e.path) => arrived.push(e.path),
            _ => {}
        }
    }
    assert!(
        missing.is_empty(),
        "[[extracted]] entries absent from the export: {missing:?}"
    );
    assert!(
        arrived.is_empty(),
        "[[pending]] entries present in the export (move them to [[extracted]]): {arrived:?}"
    );
}
