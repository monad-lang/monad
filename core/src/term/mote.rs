use std::{
  collections::BTreeMap,
  fmt,
  path::{Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
  pub mote: MoteMeta,
  pub dependencies: BTreeMap<String, Dependency>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MoteMeta {
  pub name: String,
  pub version: String,
  pub edition: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Dependency {
  Registry(String),
  Path(PathBuf),
  Git {
    url: String,
    tag: Option<String>,
    rev: Option<String>,
  },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lockfile {
  pub version: usize,
  pub motes: Vec<LockedMote>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockedMote {
  pub name: String,
  pub version: String,
  pub checksum: String,
  pub source: Option<String>,
  pub modules: Vec<LockedModule>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LockedModule {
  pub path: String,
  pub source_hash: String,
  pub input_hash: Option<String>,
  pub artifact_hash: Option<String>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct RawManifest {
  mote: RawMoteMeta,
  #[serde(default)]
  dependencies: BTreeMap<String, RawDependency>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct RawMoteMeta {
  name: String,
  version: String,
  edition: Option<String>,
}

#[derive(Debug, Clone, serde::Deserialize)]
#[serde(untagged)]
enum RawDependency {
  Version(String),
  Path {
    path: String,
  },
  Git {
    git: String,
    tag: Option<String>,
    rev: Option<String>,
  },
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct RawLockfile {
  version: usize,
  #[serde(default)]
  mote: Vec<RawLockedMote>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct RawLockedMote {
  name: String,
  version: String,
  checksum: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  source: Option<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  modules: Vec<RawLockedModule>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
struct RawLockedModule {
  path: String,
  source_hash: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  input_hash: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  artifact_hash: Option<String>,
}

impl Manifest {
  pub fn discover(start_dir: &Path) -> Option<(PathBuf, Self)> {
    let mut current = start_dir.to_path_buf();
    loop {
      let candidate = current.join("mote.toml");
      if candidate.is_file() {
        return Manifest::parse(&candidate).ok().map(|m| (candidate, m));
      }
      if !current.pop() {
        return None;
      }
    }
  }

  pub fn parse(path: &Path) -> Result<Self, String> {
    let content = std::fs::read_to_string(path)
      .map_err(|e| format!("Failed to read {}: {e}", path.display()))?;
    Self::parse_str(&content)
  }

  pub fn parse_str(content: &str) -> Result<Self, String> {
    let raw: RawManifest =
      toml::from_str(content).map_err(|e| format!("Failed to parse mote.toml: {e}"))?;

    Ok(Self {
      mote: MoteMeta {
        name: raw.mote.name,
        version: raw.mote.version,
        edition: raw.mote.edition,
      },
      dependencies: raw
        .dependencies
        .into_iter()
        .map(|(name, dep)| {
          let dep = match dep {
            RawDependency::Version(v) => Dependency::Registry(v),
            RawDependency::Path { path } => Dependency::Path(PathBuf::from(path)),
            RawDependency::Git { git, tag, rev } => Dependency::Git { url: git, tag, rev },
          };
          (name, dep)
        })
        .collect(),
    })
  }
}

fn validate_checksum(s: &str, field_name: &str) -> Result<(), String> {
  let hex = s
    .strip_prefix("sha256:")
    .ok_or_else(|| format!("invalid {field_name} '{s}': expected 'sha256:<64-char-hex>'"))?;
  validate_hash_hex(hex, field_name)
}

fn validate_hash_hex(s: &str, field_name: &str) -> Result<(), String> {
  if s.len() != 64
    || !s
      .chars()
      .all(|c| c.is_ascii_hexdigit() && !c.is_ascii_uppercase())
  {
    return Err(format!(
      "invalid {field_name} '{s}': expected 64 lowercase hex characters"
    ));
  }
  Ok(())
}

impl Lockfile {
  pub fn parse(path: &Path) -> Result<Self, String> {
    let content = std::fs::read_to_string(path)
      .map_err(|e| format!("Failed to read {}: {e}", path.display()))?;
    Self::parse_str(&content)
  }

  pub fn parse_str(content: &str) -> Result<Self, String> {
    let raw: RawLockfile =
      toml::from_str(content).map_err(|e| format!("Failed to parse mote.lock: {e}"))?;

    let lock = Self {
      version: raw.version,
      motes: raw
        .mote
        .into_iter()
        .map(|rm| LockedMote {
          name: rm.name,
          version: rm.version,
          checksum: rm.checksum,
          source: rm.source,
          modules: rm
            .modules
            .into_iter()
            .map(|rlm| LockedModule {
              path: rlm.path,
              source_hash: rlm.source_hash,
              input_hash: rlm.input_hash,
              artifact_hash: rlm.artifact_hash,
            })
            .collect(),
        })
        .collect(),
    };

    for mote in &lock.motes {
      if !mote.checksum.is_empty() {
        validate_checksum(&mote.checksum, "checksum")?;
      }
      for module in &mote.modules {
        validate_hash_hex(&module.source_hash, "source_hash")?;
        if let Some(ref h) = module.input_hash {
          validate_hash_hex(h, "input_hash")?;
        }
        if let Some(ref h) = module.artifact_hash {
          validate_checksum(h, "artifact_hash")?;
        }
      }
    }

    Ok(lock)
  }

  pub fn save(&self, path: &Path) -> Result<(), String> {
    let content = self.to_string();
    std::fs::write(path, content.as_bytes())
      .map_err(|e| format!("Failed to write {}: {e}", path.display()))
  }

  pub fn from_resolved(deps: &ResolvedDeps) -> Self {
    let mut motes: Vec<LockedMote> = deps
      .motes
      .iter()
      .map(|m| LockedMote {
        name: m.name.clone(),
        version: m.version.clone(),
        checksum: String::new(),
        source: None,
        modules: vec![],
      })
      .collect();
    motes.sort_by(|a, b| a.name.cmp(&b.name).then(a.version.cmp(&b.version)));
    Lockfile { version: 1, motes }
  }

  pub fn serialize(&self) -> String {
    let raw = RawLockfile {
      version: self.version,
      mote: self
        .motes
        .iter()
        .map(|lm| RawLockedMote {
          name: lm.name.clone(),
          version: lm.version.clone(),
          checksum: lm.checksum.clone(),
          source: lm.source.clone(),
          modules: lm
            .modules
            .iter()
            .map(|lmd| RawLockedModule {
              path: lmd.path.clone(),
              source_hash: lmd.source_hash.clone(),
              input_hash: lmd.input_hash.clone(),
              artifact_hash: lmd.artifact_hash.clone(),
            })
            .collect(),
        })
        .collect(),
    };
    toml::to_string_pretty(&raw).unwrap_or_else(|_| String::new())
  }
}

impl fmt::Display for Lockfile {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", self.serialize())
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedDeps {
  pub motes: Vec<ResolvedMote>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedMote {
  pub name: String,
  pub version: String,
  pub source_path: Option<PathBuf>,
  pub dependencies: BTreeMap<String, Dependency>,
}

pub struct Resolver;

impl Resolver {
  pub fn resolve(
    manifest: &Manifest,
    manifest_dir: &Path,
    lockfile: Option<&Lockfile>,
  ) -> Result<ResolvedDeps, String> {
    let locked: BTreeMap<&str, &str> = lockfile
      .map(|lf| {
        lf.motes
          .iter()
          .map(|m| (m.name.as_str(), m.version.as_str()))
          .collect()
      })
      .unwrap_or_default();
    let mut resolved: BTreeMap<String, ResolvedMote> = BTreeMap::new();

    let mut queue: Vec<(String, Dependency, PathBuf)> = manifest
      .dependencies
      .iter()
      .map(|(n, d)| (n.clone(), d.clone(), manifest_dir.to_path_buf()))
      .collect();

    while let Some((dep_name, dependency, dep_manifest_dir)) = queue.pop() {
      match dependency {
        Dependency::Path(path) => {
          let dep_dir = dep_manifest_dir.join(&path).canonicalize().map_err(|e| {
            format!(
              "dependency {dep_name}: path {} does not exist: {e}",
              path.display()
            )
          })?;
          let (_manifest_path, dep_manifest) = Manifest::discover(&dep_dir).ok_or_else(|| {
            format!(
              "dependency {dep_name}: no mote.toml found at {}",
              dep_dir.display()
            )
          })?;

          let deps = dep_manifest.dependencies.clone();

          if let Some(&locked_version) = locked.get(dep_name.as_str()) {
            if dep_manifest.mote.version != locked_version {
              return Err(format!(
                "lockfile conflict for mote '{}': locked at version {} but resolved {} at {}",
                dep_name,
                locked_version,
                dep_manifest.mote.version,
                dep_dir.display()
              ));
            }
          }

          if let Some(existing) = resolved.get(&dep_name) {
            if dep_manifest.mote.version != existing.version {
              return Err(format!(
                "version conflict for mote '{}': version {} at {} conflicts with version {} at {}",
                dep_name,
                existing.version,
                existing
                  .source_path
                  .as_ref()
                  .map(|p| p.display().to_string())
                  .unwrap_or_else(|| "unknown".into()),
                dep_manifest.mote.version,
                dep_dir.display(),
              ));
            }
            continue;
          }

          resolved.insert(
            dep_name.clone(),
            ResolvedMote {
              name: dep_manifest.mote.name.clone(),
              version: dep_manifest.mote.version.clone(),
              source_path: Some(dep_dir.clone()),
              dependencies: deps.clone(),
            },
          );

          for (trans_name, trans_dep) in &deps {
            queue.push((trans_name.clone(), trans_dep.clone(), dep_dir.clone()));
          }
        }
        Dependency::Registry(version_req) => {
          return Err(format!(
            "dependency {dep_name} {version_req}: registry deps not yet supported"
          ));
        }
        Dependency::Git { url, .. } => {
          return Err(format!(
            "dependency {dep_name} from {url}: git deps not yet supported"
          ));
        }
      }
    }

    Ok(ResolvedDeps {
      motes: resolved.into_values().collect(),
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_parse_minimal_mote_toml() {
    let toml_str = r#"
[mote]
name = "my-mote"
version = "0.1.0"
"#;
    let raw: RawManifest = toml::from_str(toml_str).unwrap();
    assert_eq!(raw.mote.name, "my-mote");
    assert_eq!(raw.mote.version, "0.1.0");
    assert!(raw.mote.edition.is_none());
    assert!(raw.dependencies.is_empty());
  }

  #[test]
  fn test_parse_mote_toml_with_edition() {
    let toml_str = r#"
[mote]
name = "my-mote"
version = "0.1.0"
edition = "2026"
"#;
    let raw: RawManifest = toml::from_str(toml_str).unwrap();
    assert_eq!(raw.mote.name, "my-mote");
    assert_eq!(raw.mote.edition.as_deref(), Some("2026"));
  }

  #[test]
  fn test_parse_mote_toml_with_deps() {
    let toml_str = r#"
[mote]
name = "my-app"
version = "0.1.0"

[dependencies]
json = ">=0.2.0"
mylib = { path = "../mylib" }
http = { git = "https://github.com/user/http", tag = "v0.1.0" }
"#;
    let manifest = Manifest::parse_str(toml_str).unwrap();
    let deps = manifest.dependencies;
    assert_eq!(deps.len(), 3);

    match &deps["json"] {
      Dependency::Registry(v) => assert_eq!(v, ">=0.2.0"),
      other => panic!("Expected Registry, got {:?}", other),
    }

    match &deps["mylib"] {
      Dependency::Path(p) => assert_eq!(p, &PathBuf::from("../mylib")),
      other => panic!("Expected Path, got {:?}", other),
    }

    match &deps["http"] {
      Dependency::Git { url, tag, rev } => {
        assert_eq!(url, "https://github.com/user/http");
        assert_eq!(tag.as_deref(), Some("v0.1.0"));
        assert!(rev.is_none());
      }
      other => panic!("Expected Git, got {:?}", other),
    }
  }

  #[test]
  fn test_parse_mote_toml_from_file() {
    let dir = PathBuf::from("/tmp").join(format!("monad-test-mote-parse-{:x}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mote_toml = dir.join("mote.toml");
    let content = r#"
[mote]
name = "test-mote"
version = "1.2.3"
"#;
    std::fs::write(&mote_toml, content).unwrap();

    let manifest = Manifest::parse(&mote_toml).unwrap();
    assert_eq!(manifest.mote.name, "test-mote");
    assert_eq!(manifest.mote.version, "1.2.3");
    assert!(manifest.dependencies.is_empty());

    std::fs::remove_dir_all(&dir).unwrap();
  }

  #[test]
  fn test_discover_finds_in_current_dir() {
    let dir =
      PathBuf::from("/tmp").join(format!("monad-test-discover-cur-{:x}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mote_toml = dir.join("mote.toml");
    std::fs::write(
      &mote_toml,
      r#"[mote]
name = "found-in-root"
version = "0.1.0"
"#,
    )
    .unwrap();

    let (path, manifest) = Manifest::discover(&dir).expect("Should find mote.toml");
    assert_eq!(manifest.mote.name, "found-in-root");
    assert_eq!(path, mote_toml.canonicalize().unwrap());

    std::fs::remove_dir_all(&dir).unwrap();
  }

  #[test]
  fn test_discover_walks_up() {
    let dir =
      PathBuf::from("/tmp").join(format!("monad-test-discover-up-{:x}", std::process::id()));
    let sub = dir.join("a").join("b").join("c");
    std::fs::create_dir_all(&sub).unwrap();
    let mote_toml = dir.join("mote.toml");
    std::fs::write(
      &mote_toml,
      r#"[mote]
name = "walked-up"
version = "0.2.0"
"#,
    )
    .unwrap();

    let (path, manifest) = Manifest::discover(&sub).expect("Should walk up to find mote.toml");
    assert_eq!(manifest.mote.name, "walked-up");
    assert_eq!(path, mote_toml.canonicalize().unwrap());

    std::fs::remove_dir_all(&dir).unwrap();
  }

  #[test]
  fn test_discover_none_when_no_mote_toml() {
    let dir =
      PathBuf::from("/tmp").join(format!("monad-test-discover-none-{:x}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();

    let result = Manifest::discover(&dir);
    assert!(result.is_none());

    std::fs::remove_dir_all(&dir).unwrap();
  }

  #[test]
  fn test_parse_lockfile_empty() {
    let toml_str = "version = 1\n";
    let lock = Lockfile::parse_str(toml_str).unwrap();
    assert_eq!(lock.version, 1);
    assert!(lock.motes.is_empty());
  }

  #[test]
  fn test_parse_lockfile_with_mote_no_source() {
    let toml_str = r#"
version = 1

[[mote]]
name = "json"
version = "0.2.0"
checksum = "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921"
"#;
    let lock = Lockfile::parse_str(toml_str).unwrap();
    assert_eq!(lock.version, 1);
    assert_eq!(lock.motes.len(), 1);
    assert_eq!(lock.motes[0].name, "json");
    assert_eq!(lock.motes[0].version, "0.2.0");
    assert_eq!(
      lock.motes[0].checksum,
      "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921"
    );
    assert!(lock.motes[0].source.is_none());
    assert!(lock.motes[0].modules.is_empty());
  }

  #[test]
  fn test_parse_lockfile_with_source() {
    let toml_str = r#"
version = 1

[[mote]]
name = "http"
version = "0.1.0"
checksum = "sha256:4a0702486331f0fd9bf8f86e2460be96e32cdc3ef9051f0cd6fbd0355e6ce259"
source = "git+https://github.com/user/http?tag=v0.1.0"
"#;
    let lock = Lockfile::parse_str(toml_str).unwrap();
    assert_eq!(lock.motes.len(), 1);
    assert_eq!(
      lock.motes[0].source.as_deref(),
      Some("git+https://github.com/user/http?tag=v0.1.0")
    );
  }

  #[test]
  fn test_parse_lockfile_with_modules() {
    let toml_str = r#"
version = 1

[[mote]]
name = "json"
version = "0.2.0"
checksum = "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921"

[[mote.modules]]
path = "parser"
source_hash = "594f793e8b6d5d761b72f2512d07fd25933ff7483d72b31224d264b4cb77777a"
input_hash = "b6f9ba0467502d6697078623b75f7e2cacf59563d76b0e5b946b27e1f0185cff"
artifact_hash = "sha256:c477bab45dd91f6ccbafed332dcff7503b4bc7e6b87f5a6786c46eb627eb6b7f"

[[mote.modules]]
path = "types"
source_hash = "81fef029a4ab54b8d12f2e2079e8f358d72084225e29062e0232442012d6e901"
"#;
    let lock = Lockfile::parse_str(toml_str).unwrap();
    assert_eq!(lock.motes.len(), 1);
    let modules = &lock.motes[0].modules;
    assert_eq!(modules.len(), 2);

    assert_eq!(modules[0].path, "parser");
    assert_eq!(
      modules[0].source_hash,
      "594f793e8b6d5d761b72f2512d07fd25933ff7483d72b31224d264b4cb77777a"
    );
    assert_eq!(
      modules[0].input_hash.as_deref(),
      Some("b6f9ba0467502d6697078623b75f7e2cacf59563d76b0e5b946b27e1f0185cff")
    );
    assert_eq!(
      modules[0].artifact_hash.as_deref(),
      Some("sha256:c477bab45dd91f6ccbafed332dcff7503b4bc7e6b87f5a6786c46eb627eb6b7f")
    );

    assert_eq!(modules[1].path, "types");
    assert_eq!(
      modules[1].source_hash,
      "81fef029a4ab54b8d12f2e2079e8f358d72084225e29062e0232442012d6e901"
    );
    assert!(modules[1].input_hash.is_none());
    assert!(modules[1].artifact_hash.is_none());
  }

  #[test]
  fn test_lockfile_roundtrip() {
    let lock = Lockfile {
      version: 1,
      motes: vec![
        LockedMote {
          name: "json".into(),
          version: "0.2.0".into(),
          checksum: "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921"
            .into(),
          source: None,
          modules: vec![
            LockedModule {
              path: "parser".into(),
              source_hash: "594f793e8b6d5d761b72f2512d07fd25933ff7483d72b31224d264b4cb77777a"
                .into(),
              input_hash: Some(
                "b6f9ba0467502d6697078623b75f7e2cacf59563d76b0e5b946b27e1f0185cff".into(),
              ),
              artifact_hash: Some(
                "sha256:c477bab45dd91f6ccbafed332dcff7503b4bc7e6b87f5a6786c46eb627eb6b7f".into(),
              ),
            },
            LockedModule {
              path: "types".into(),
              source_hash: "81fef029a4ab54b8d12f2e2079e8f358d72084225e29062e0232442012d6e901"
                .into(),
              input_hash: None,
              artifact_hash: None,
            },
          ],
        },
        LockedMote {
          name: "http".into(),
          version: "0.1.0".into(),
          checksum: "sha256:4a0702486331f0fd9bf8f86e2460be96e32cdc3ef9051f0cd6fbd0355e6ce259"
            .into(),
          source: Some("git+https://github.com/user/http?tag=v0.1.0".into()),
          modules: vec![],
        },
      ],
    };

    let serialized = lock.to_string();
    let parsed = Lockfile::parse_str(&serialized).unwrap();
    assert_eq!(lock, parsed);
  }

  #[test]
  fn test_lockfile_roundtrip_minimal() {
    let lock = Lockfile {
      version: 1,
      motes: vec![],
    };
    let serialized = lock.to_string();
    let parsed = Lockfile::parse_str(&serialized).unwrap();
    assert_eq!(lock, parsed);
  }

  #[test]
  fn test_lockfile_file_roundtrip() {
    let dir = PathBuf::from("/tmp").join(format!("monad-test-lockfile-{:x}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let lock_path = dir.join("mote.lock");

    let lock = Lockfile {
      version: 1,
      motes: vec![LockedMote {
        name: "test".into(),
        version: "1.0.0".into(),
        checksum: "sha256:0bb304d010d2914dafb3c0eb4b419d3de4adfb6833f4bb370f119e4e338e4fd1".into(),
        source: None,
        modules: vec![LockedModule {
          path: "main".into(),
          source_hash: "9e6a36df1bd43a118568af8d84b8332b7f0608e6e27d04097aa54beaad36c668".into(),
          input_hash: None,
          artifact_hash: None,
        }],
      }],
    };

    lock.save(&lock_path).unwrap();
    let parsed = Lockfile::parse(&lock_path).unwrap();
    assert_eq!(lock, parsed);

    std::fs::remove_dir_all(&dir).unwrap();
  }

  #[test]
  fn test_lockfile_display() {
    let lock = Lockfile {
      version: 1,
      motes: vec![LockedMote {
        name: "hello".into(),
        version: "0.1.0".into(),
        checksum: "sha256:5125b47c16687d8b180201118fea1e727a32345ee254a39f40ed9694dbac1591".into(),
        source: None,
        modules: vec![],
      }],
    };
    let s = format!("{lock}");
    assert!(s.contains("version = 1"));
    assert!(s.contains("name = \"hello\""));
    assert!(s.contains(
      "checksum = \"sha256:5125b47c16687d8b180201118fea1e727a32345ee254a39f40ed9694dbac1591\""
    ));
  }

  #[test]
  fn test_empty_lockfile_is_parseable() {
    let lock = Lockfile {
      version: 1,
      motes: vec![],
    };
    let s = lock.to_string();
    let parsed = Lockfile::parse_str(&s).unwrap();
    assert_eq!(parsed.version, 1);
    assert!(parsed.motes.is_empty());
  }

  #[test]
  fn test_reject_invalid_checksum_no_prefix() {
    let toml_str = r#"
version = 1

[[mote]]
name = "bad"
version = "0.1.0"
checksum = "notsha256:594f793e8b6d5d761b72f2512d07fd25933ff7483d72b31224d264b4cb77777a"
"#;
    let err = Lockfile::parse_str(toml_str).unwrap_err();
    assert!(err.contains("invalid checksum"), "got: {err}");
  }

  #[test]
  fn test_reject_invalid_checksum_wrong_length() {
    let toml_str = r#"
version = 1

[[mote]]
name = "bad"
version = "0.1.0"
checksum = "sha256:abc123"
"#;
    let err = Lockfile::parse_str(toml_str).unwrap_err();
    assert!(
      err.contains("expected 64 lowercase hex characters"),
      "got: {err}"
    );
  }

  #[test]
  fn test_reject_invalid_checksum_uppercase() {
    let toml_str = r#"
version = 1

[[mote]]
name = "bad"
version = "0.1.0"
checksum = "sha256:4467C075665950B2AE160A145EBFFDDF7E7876189EF4ADD43D491B48386AB921"
"#;
    let err = Lockfile::parse_str(toml_str).unwrap_err();
    assert!(
      err.contains("expected 64 lowercase hex characters"),
      "got: {err}"
    );
  }

  #[test]
  fn test_reject_invalid_source_hash() {
    let toml_str = r#"
version = 1

[[mote]]
name = "json"
version = "0.2.0"
checksum = "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921"

[[mote.modules]]
path = "parser"
source_hash = "2f3a"
"#;
    let err = Lockfile::parse_str(toml_str).unwrap_err();
    assert!(
      err.contains("expected 64 lowercase hex characters"),
      "got: {err}"
    );
  }

  #[test]
  fn test_reject_invalid_artifact_hash() {
    let toml_str = r#"
version = 1

[[mote]]
name = "json"
version = "0.2.0"
checksum = "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921"

[[mote.modules]]
path = "parser"
source_hash = "594f793e8b6d5d761b72f2512d07fd25933ff7483d72b31224d264b4cb77777a"
artifact_hash = "notsha256:def"
"#;
    let err = Lockfile::parse_str(toml_str).unwrap_err();
    assert!(err.contains("invalid artifact_hash"), "got: {err}");
  }

  // --- Resolver tests ---

  #[test]
  fn test_resolve_empty_manifest() {
    let dir =
      PathBuf::from("/tmp").join(format!("monad-test-resolve-empty-{:x}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mote_toml = dir.join("mote.toml");
    std::fs::write(
      &mote_toml,
      r#"
[mote]
name = "my-app"
version = "0.1.0"
"#,
    )
    .unwrap();

    let manifest = Manifest::parse(&mote_toml).unwrap();
    let resolved = Resolver::resolve(&manifest, &dir, None).unwrap();
    assert!(resolved.motes.is_empty());

    std::fs::remove_dir_all(&dir).unwrap();
  }

  fn setup_mote(
    dir: &Path,
    name: &str,
    version: &str,
    deps: &[(&str, &str)],
  ) -> (Manifest, PathBuf) {
    std::fs::create_dir_all(dir.join("src")).unwrap();
    let mote_toml = dir.join("mote.toml");
    let mut toml_content = format!(
      r#"
[mote]
name = "{}"
version = "{}"
"#,
      name, version
    );
    if !deps.is_empty() {
      toml_content.push_str("\n[dependencies]\n");
      for (dep_name, _dep_version) in deps {
        toml_content.push_str(&format!("{dep_name} = {{ path = \"../{dep_name}\" }}\n"));
      }
    }
    std::fs::write(&mote_toml, &toml_content).unwrap();
    let manifest = Manifest::parse(&mote_toml).unwrap();
    (manifest, dir.to_path_buf())
  }

  #[test]
  fn test_resolve_single_path_dep() {
    let root =
      PathBuf::from("/tmp").join(format!("monad-test-resolve-path-{:x}", std::process::id()));
    let root_dir = root.clone();
    let lib_dir = root.join("motes").join("mylib");

    let manifest = {
      let mote_toml = root_dir.join("mote.toml");
      std::fs::create_dir_all(&root_dir).unwrap();
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "root"
version = "1.0.0"

[dependencies]
mylib = { path = "motes/mylib" }
"#,
      )
      .unwrap();
      Manifest::parse(&mote_toml).unwrap()
    };

    setup_mote(&lib_dir, "mylib", "0.1.0", &[]);

    let resolved = Resolver::resolve(&manifest, &root_dir, None).unwrap();
    assert_eq!(resolved.motes.len(), 1);
    assert_eq!(resolved.motes[0].name, "mylib");
    assert_eq!(resolved.motes[0].version, "0.1.0");

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_resolve_transitive_path_deps() {
    let root =
      PathBuf::from("/tmp").join(format!("monad-test-resolve-trans-{:x}", std::process::id()));
    let lib_a_dir = root.join("motes").join("lib-a");
    let lib_b_dir = root.join("motes").join("lib-b");

    let manifest = {
      let mote_toml = root.join("mote.toml");
      std::fs::create_dir_all(&root).unwrap();
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "root"
version = "1.0.0"

[dependencies]
lib-a = { path = "motes/lib-a" }
"#,
      )
      .unwrap();
      Manifest::parse(&mote_toml).unwrap()
    };

    setup_mote(&lib_a_dir, "lib-a", "0.1.0", &[("lib-b", ">=0.5.0")]);
    setup_mote(&lib_b_dir, "lib-b", "0.5.0", &[]);

    let resolved = Resolver::resolve(&manifest, &root, None).unwrap();
    assert_eq!(resolved.motes.len(), 2);

    let names: Vec<&str> = resolved.motes.iter().map(|m| m.name.as_str()).collect();
    assert!(names.contains(&"lib-a"));
    assert!(names.contains(&"lib-b"));

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_resolve_diamond_conflict() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-resolve-diamond-{:x}",
      std::process::id()
    ));

    let manifest = {
      let mote_toml = root.join("mote.toml");
      std::fs::create_dir_all(&root).unwrap();
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "root"
version = "1.0.0"

[dependencies]
lib-a = { path = "motes/lib-a" }
lib-c = { path = "motes/lib-c" }
"#,
      )
      .unwrap();
      Manifest::parse(&mote_toml).unwrap()
    };

    let lib_a_dir = root.join("motes").join("lib-a");
    let lib_b_dir = root.join("motes").join("lib-b");
    let lib_b_alt_dir = root.join("motes").join("lib-b-alt");
    let lib_c_dir = root.join("motes").join("lib-c");

    setup_mote(&lib_a_dir, "lib-a", "0.1.0", &[("lib-b", ">=1.0.0")]);
    setup_mote(&lib_b_dir, "lib-b", "1.0.0", &[]);
    setup_mote(&lib_b_alt_dir, "lib-b", "2.0.0", &[]);

    {
      let mote_toml = lib_c_dir.join("mote.toml");
      std::fs::create_dir_all(&lib_c_dir).unwrap();
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "lib-c"
version = "2.0.0"

[dependencies]
lib-b = { path = "../lib-b-alt" }
"#,
      )
      .unwrap();
    }

    let err = Resolver::resolve(&manifest, &root, None).unwrap_err();
    assert!(
      err.contains("version conflict for mote 'lib-b'"),
      "got: {err}"
    );
    assert!(err.contains("1.0.0"), "got: {err}");
    assert!(err.contains("2.0.0"), "got: {err}");

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_resolve_lockfile_version_mismatch_detected() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-resolve-lock-mismatch-{:x}",
      std::process::id()
    ));
    let lib_dir = root.join("motes").join("mylib");

    setup_mote(&lib_dir, "mylib", "0.2.0", &[]);

    let manifest = {
      let mote_toml = root.join("mote.toml");
      std::fs::create_dir_all(&root).unwrap();
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "root"
version = "1.0.0"

[dependencies]
mylib = { path = "motes/mylib" }
"#,
      )
      .unwrap();
      Manifest::parse(&mote_toml).unwrap()
    };

    let lockfile = Lockfile {
      version: 1,
      motes: vec![LockedMote {
        name: "mylib".into(),
        version: "0.1.0".into(),
        checksum: "sha256:4467c075665950b2ae160a145ebffddf7e7876189ef4add43d491b48386ab921".into(),
        source: None,
        modules: vec![],
      }],
    };

    let err = Resolver::resolve(&manifest, &root, Some(&lockfile)).unwrap_err();
    assert!(
      err.contains("lockfile conflict for mote 'mylib'"),
      "got: {err}"
    );
    assert!(err.contains("0.1.0"), "got: {err}");
    assert!(err.contains("0.2.0"), "got: {err}");

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_lockfile_from_resolved() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-lock-from-resolved-{:x}",
      std::process::id()
    ));
    let lib_dir = root.join("motes").join("mylib");

    setup_mote(&lib_dir, "mylib", "0.1.0", &[]);

    let manifest = {
      let mote_toml = root.join("mote.toml");
      std::fs::create_dir_all(&root).unwrap();
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "root"
version = "1.0.0"

[dependencies]
mylib = { path = "motes/mylib" }
"#,
      )
      .unwrap();
      Manifest::parse(&mote_toml).unwrap()
    };

    let resolved = Resolver::resolve(&manifest, &root, None).unwrap();
    let lockfile = Lockfile::from_resolved(&resolved);

    assert_eq!(lockfile.version, 1);
    assert_eq!(lockfile.motes.len(), 1);
    assert_eq!(lockfile.motes[0].name, "mylib");
    assert_eq!(lockfile.motes[0].version, "0.1.0");
    assert!(lockfile.motes[0].checksum.is_empty());
    assert!(lockfile.motes[0].source.is_none());
    assert!(lockfile.motes[0].modules.is_empty());

    // Round-trip: serialize and parse
    let serialized = lockfile.to_string();
    let parsed = Lockfile::parse_str(&serialized).unwrap();
    assert_eq!(lockfile.motes, parsed.motes);

    std::fs::remove_dir_all(&root).unwrap();
  }
}
