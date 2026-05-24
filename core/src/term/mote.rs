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

impl Lockfile {
  pub fn parse(path: &Path) -> Result<Self, String> {
    let content = std::fs::read_to_string(path)
      .map_err(|e| format!("Failed to read {}: {e}", path.display()))?;
    Self::parse_str(&content)
  }

  pub fn parse_str(content: &str) -> Result<Self, String> {
    let raw: RawLockfile =
      toml::from_str(content).map_err(|e| format!("Failed to parse mote.lock: {e}"))?;

    Ok(Self {
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
    })
  }

  pub fn save(&self, path: &Path) -> Result<(), String> {
    let content = self.to_string();
    std::fs::write(path, content.as_bytes())
      .map_err(|e| format!("Failed to write {}: {e}", path.display()))
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
checksum = "sha256:abc123"
"#;
    let lock = Lockfile::parse_str(toml_str).unwrap();
    assert_eq!(lock.version, 1);
    assert_eq!(lock.motes.len(), 1);
    assert_eq!(lock.motes[0].name, "json");
    assert_eq!(lock.motes[0].version, "0.2.0");
    assert_eq!(lock.motes[0].checksum, "sha256:abc123");
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
checksum = "sha256:xyz789"
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
checksum = "sha256:abc123"

[[mote.modules]]
path = "parser"
source_hash = "2f3a"
input_hash = "b3e4"
artifact_hash = "sha256:def"

[[mote.modules]]
path = "types"
source_hash = "4b5c"
"#;
    let lock = Lockfile::parse_str(toml_str).unwrap();
    assert_eq!(lock.motes.len(), 1);
    let modules = &lock.motes[0].modules;
    assert_eq!(modules.len(), 2);

    assert_eq!(modules[0].path, "parser");
    assert_eq!(modules[0].source_hash, "2f3a");
    assert_eq!(modules[0].input_hash.as_deref(), Some("b3e4"));
    assert_eq!(modules[0].artifact_hash.as_deref(), Some("sha256:def"));

    assert_eq!(modules[1].path, "types");
    assert_eq!(modules[1].source_hash, "4b5c");
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
          checksum: "sha256:abc".into(),
          source: None,
          modules: vec![
            LockedModule {
              path: "parser".into(),
              source_hash: "2f3a".into(),
              input_hash: Some("b3e4".into()),
              artifact_hash: Some("sha256:def".into()),
            },
            LockedModule {
              path: "types".into(),
              source_hash: "4b5c".into(),
              input_hash: None,
              artifact_hash: None,
            },
          ],
        },
        LockedMote {
          name: "http".into(),
          version: "0.1.0".into(),
          checksum: "sha256:xyz".into(),
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
        checksum: "sha256:deadbeef".into(),
        source: None,
        modules: vec![LockedModule {
          path: "main".into(),
          source_hash: "abcd".into(),
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
        checksum: "sha256:abc".into(),
        source: None,
        modules: vec![],
      }],
    };
    let s = format!("{lock}");
    assert!(s.contains("version = 1"));
    assert!(s.contains("name = \"hello\""));
    assert!(s.contains("checksum = \"sha256:abc\""));
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
}
