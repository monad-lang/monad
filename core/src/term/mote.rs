use std::{
  collections::BTreeMap,
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
}
