use serde_derive::{Deserialize, Serialize};
use std::path::PathBuf;

#[test]
pub fn top_crates() {
    top_crates_range(0..500)
}

fn get(url: &str) -> reqwest::Result<reqwest::blocking::Response> {
    println!("Getting: {url}");
    reqwest::blocking::ClientBuilder::new()
        .user_agent("Rust Corpus - Top Crates Scrapper")
        .build()?
        .get(url)
        .send()
}

pub fn top_crates_range(range: std::ops::Range<usize>) {
    std::fs::create_dir_all("tmp").unwrap();
    let top_crates = top_crates_by_download_count(range.end - 1);
    for (i, krate) in top_crates.into_iter().enumerate().skip(range.start) {
        let version = krate.version.unwrap_or(krate.newest_version);
        println!("Starting: {i} ({})", krate.name);
        run_on_crate(&krate.name, &version);
    }
}

fn run_on_crate(name: &str, version: &str) {
    let dirname = format!("./tmp/{name}-{version}");
    let filename = format!("{dirname}.crate");
    if !std::path::PathBuf::from(&filename).exists() {
        let dl = format!("https://crates.io/api/v1/crates/{name}/{version}/download");
        let mut resp = get(&dl).expect("Could not fetch top crates");
        let mut file = std::fs::File::create(&filename).unwrap();
        resp.copy_to(&mut file).unwrap();
    }
    println!("Unwrapping: {filename}");
    let status = std::process::Command::new("tar")
        .args(["-xf", &filename, "-C", "./tmp/"])
        .status()
        .unwrap();
    assert!(status.success());
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open(format!("{dirname}/Cargo.toml"))
        .unwrap();
    use std::io::Write;
    writeln!(file, "\n[workspace]").unwrap();
    let cwd = std::env::current_dir().unwrap();
    assert!(
        cfg!(debug_assertions),
        "Must be run in debug mode, to enable full checking"
    );
    let target = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let prusti = cwd.join(
        ["..", "target", target, "cargo-prusti"]
            .iter()
            .collect::<PathBuf>(),
    );
    println!("Running: {prusti:?}");
    let exit = std::process::Command::new(&prusti)
        .env("PRUSTI_TEST_FREE_PCS", "true")
        .env("PRUSTI_TEST_COUPLING_GRAPH", "true")
        .env("PRUSTI_SKIP_UNSUPPORTED_FEATURES", "true")
        // .env("PRUSTI_LOG", "debug")
        .env("PRUSTI_NO_VERIFY_DEPS", "true")
        .env("PRUSTI_CAP_LINTS", "allow")
        .env("PRUSTI_TOP_CRATES", "true")
        .current_dir(&dirname)
        .status()
        .unwrap();
    assert!(exit.success());
    // std::fs::remove_dir_all(dirname).unwrap();
}

/// A create on crates.io.
#[derive(Debug, Deserialize, Serialize)]
struct Crate {
    #[serde(rename = "id")]
    name: String,
    #[serde(rename = "max_stable_version")]
    version: Option<String>,
    #[serde(rename = "newest_version")]
    newest_version: String,
}

/// The list of crates from crates.io
#[derive(Debug, Deserialize)]
struct CratesList {
    crates: Vec<Crate>,
}

/// Create a list of top ``count`` crates.
fn top_crates_by_download_count(mut count: usize) -> Vec<Crate> {
    const PAGE_SIZE: usize = 100;
    let page_count = count / PAGE_SIZE + 2;
    let mut sources = Vec::new();
    for page in 1..page_count {
        let url = format!(
            "https://crates.io/api/v1/crates?page={page}&per_page={PAGE_SIZE}&sort=downloads"
        );
        let resp = get(&url).expect("Could not fetch top crates");
        assert!(
            resp.status().is_success(),
            "Response status: {}",
            resp.status()
        );
        let page_crates: CratesList = match serde_json::from_reader(resp) {
            Ok(page_crates) => page_crates,
            Err(e) => panic!("Invalid JSON {e}"),
        };
        sources.extend(page_crates.crates.into_iter().take(count));
        count -= std::cmp::min(PAGE_SIZE, count);
    }
    sources
}
