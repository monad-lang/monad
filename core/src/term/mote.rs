use std::{
  collections::BTreeMap,
  fmt,
  path::{Path, PathBuf},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
  /// `None` for a virtual workspace root (a manifest with `[workspace]` but no `[mote]`).
  pub mote: Option<MoteMeta>,
  pub dependencies: BTreeMap<String, Dependency>,
  pub workspace: Option<Workspace>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MoteMeta {
  pub name: String,
  pub version: String,
  pub edition: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Workspace {
  /// Member path patterns relative to the manifest's directory, e.g. `"motes/*"` or `"pkgs/engine"`.
  pub members: Vec<String>,
}

impl Workspace {
  /// Expands member patterns into concrete directories containing a `mote.toml`.
  /// Supports exact paths and a single trailing `/*` wildcard (one level deep).
  pub fn resolve_members(&self, root_dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut dirs = Vec::new();
    for pattern in &self.members {
      if let Some(prefix) = pattern.strip_suffix("/*") {
        let parent = root_dir.join(prefix);
        let entries = std::fs::read_dir(&parent).map_err(|e| {
          format!(
            "workspace member pattern '{pattern}': failed to read {}: {e}",
            parent.display()
          )
        })?;
        let mut matched: Vec<PathBuf> = entries
          .filter_map(|e| e.ok())
          .map(|e| e.path())
          .filter(|p| p.is_dir() && p.join("mote.toml").is_file())
          .collect();
        matched.sort();
        dirs.extend(matched);
      } else {
        let dir = root_dir.join(pattern);
        if !dir.join("mote.toml").is_file() {
          return Err(format!(
            "workspace member '{pattern}': no mote.toml found at {}",
            dir.display()
          ));
        }
        dirs.push(dir);
      }
    }
    Ok(dirs)
  }
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
  mote: Option<RawMoteMeta>,
  #[serde(default)]
  dependencies: BTreeMap<String, RawDependency>,
  workspace: Option<RawWorkspace>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct RawMoteMeta {
  name: String,
  version: String,
  edition: Option<String>,
}

#[derive(Debug, Clone, serde::Deserialize)]
struct RawWorkspace {
  #[serde(default)]
  members: Vec<String>,
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

    if raw.mote.is_none() && raw.workspace.is_none() {
      return Err("mote.toml must have a [mote] or [workspace] section".to_string());
    }

    Ok(Self {
      mote: raw.mote.map(|m| MoteMeta {
        name: m.name,
        version: m.version,
        edition: m.edition,
      }),
      workspace: raw.workspace.map(|w| Workspace { members: w.members }),
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

pub struct Installer;

impl Installer {
  pub fn install_dir(project_dir: &Path, name: &str, version: &str) -> PathBuf {
    let motes_dir = project_dir.join("motes");
    mote_install_dir(&motes_dir, name, version)
  }

  pub fn install(
    deps: &ResolvedDeps,
    project_dir: &Path,
    _lockfile: Option<&Lockfile>,
  ) -> Result<(), String> {
    let motes_dir = project_dir.join("motes");
    std::fs::create_dir_all(&motes_dir)
      .map_err(|e| format!("Failed to create motes directory: {e}"))?;

    for mote in &deps.motes {
      let source = mote
        .source_path
        .as_ref()
        .ok_or_else(|| format!("cannot install mote '{}': no source path", mote.name))?;

      let install_dir = mote_install_dir(&motes_dir, &mote.name, &mote.version);

      install_mote(source, &install_dir)?;
    }

    Ok(())
  }
}

static EXCLUDE_DIRS: &[&str] = &[".git", "target", "motes"];
static EXCLUDE_FILES: &[&str] = &["mote.lock"];

fn mote_install_dir(motes_dir: &Path, name: &str, version: &str) -> PathBuf {
  let sanitized_name = name.replace(|c: char| !c.is_alphanumeric() && c != '-' && c != '_', "_");
  let sanitized_version = version
    .split('+')
    .next()
    .unwrap_or(version)
    .replace(|c: char| !c.is_alphanumeric() && c != '.' && c != '-', "_");
  motes_dir.join(format!("{sanitized_name}-{sanitized_version}"))
}

fn install_mote(source: &Path, dest: &Path) -> Result<(), String> {
  if !source.is_dir() {
    return Err(format!("source is not a directory: {}", source.display()));
  }

  if dest.exists() {
    std::fs::remove_dir_all(dest).map_err(|e| {
      format!(
        "Failed to remove existing directory {}: {e}",
        dest.display()
      )
    })?;
  }

  copy_source_tree(source, dest, source)
}

fn copy_source_tree(source: &Path, dest: &Path, root: &Path) -> Result<(), String> {
  std::fs::create_dir_all(dest).map_err(|e| format!("Failed to create {}: {e}", dest.display()))?;

  let entries = std::fs::read_dir(source)
    .map_err(|e| format!("Failed to read directory {}: {e}", source.display()))?;

  for entry in entries {
    let entry = entry.map_err(|e| format!("Failed to read entry: {e}"))?;
    let name = entry.file_name();
    let name_str = name.to_string_lossy();

    if EXCLUDE_DIRS.iter().any(|d| name_str.as_ref() == *d) {
      continue;
    }

    let file_type = entry
      .file_type()
      .map_err(|e| format!("Failed to get file type: {e}"))?;
    let dest_path = dest.join(&name);

    if file_type.is_dir() {
      copy_source_tree(&entry.path(), &dest_path, root)?;
    } else if file_type.is_file() {
      if EXCLUDE_FILES.iter().any(|f| name_str.as_ref() == *f) {
        continue;
      }
      std::fs::copy(&entry.path(), &dest_path)
        .map_err(|e| format!("Failed to copy {}: {e}", entry.path().display()))?;
    }
  }

  Ok(())
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

          let dep_mote = dep_manifest.mote.as_ref().ok_or_else(|| {
            format!(
              "dependency {dep_name}: manifest at {} has no [mote] section (virtual workspace roots cannot be used as dependencies)",
              dep_dir.display()
            )
          })?;

          let deps = dep_manifest.dependencies.clone();

          if let Some(&locked_version) = locked.get(dep_name.as_str()) {
            if dep_mote.version != locked_version {
              return Err(format!(
                "lockfile conflict for mote '{}': locked at version {} but resolved {} at {}",
                dep_name,
                locked_version,
                dep_mote.version,
                dep_dir.display()
              ));
            }
          }

          if let Some(existing) = resolved.get(&dep_name) {
            if dep_mote.version != existing.version {
              return Err(format!(
                "version conflict for mote '{}': version {} at {} conflicts with version {} at {}",
                dep_name,
                existing.version,
                existing
                  .source_path
                  .as_ref()
                  .map(|p| p.display().to_string())
                  .unwrap_or_else(|| "unknown".into()),
                dep_mote.version,
                dep_dir.display(),
              ));
            }
            continue;
          }

          resolved.insert(
            dep_name.clone(),
            ResolvedMote {
              name: dep_mote.name.clone(),
              version: dep_mote.version.clone(),
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
    let mote = raw.mote.unwrap();
    assert_eq!(mote.name, "my-mote");
    assert_eq!(mote.version, "0.1.0");
    assert!(mote.edition.is_none());
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
    let mote = raw.mote.unwrap();
    assert_eq!(mote.name, "my-mote");
    assert_eq!(mote.edition.as_deref(), Some("2026"));
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
    let mote = manifest.mote.unwrap();
    assert_eq!(mote.name, "test-mote");
    assert_eq!(mote.version, "1.2.3");
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
    assert_eq!(manifest.mote.unwrap().name, "found-in-root");
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
    assert_eq!(manifest.mote.unwrap().name, "walked-up");
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
  fn test_install_single_path_dep() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-install-single-{:x}",
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
    Installer::install(&resolved, &root, None).unwrap();

    let installed = root.join("motes").join("mylib-0.1.0");
    assert!(installed.join("mote.toml").is_file());
    assert!(installed.join("src").is_dir());

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_install_excludes_excluded_dirs() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-install-exclude-{:x}",
      std::process::id()
    ));
    let lib_dir = root.join("motes").join("lib-a");

    setup_mote(&lib_dir, "lib-a", "0.1.0", &[]);
    std::fs::create_dir_all(lib_dir.join(".git")).unwrap();
    std::fs::write(lib_dir.join(".git").join("HEAD"), "ref: refs/heads/main").unwrap();
    std::fs::create_dir_all(lib_dir.join("target")).unwrap();
    std::fs::write(lib_dir.join("target").join("artifact.o"), "binary").unwrap();
    std::fs::write(lib_dir.join("mote.lock"), "lock").unwrap();

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

    let resolved = Resolver::resolve(&manifest, &root, None).unwrap();
    Installer::install(&resolved, &root, None).unwrap();

    let installed = root.join("motes").join("lib-a-0.1.0");
    assert!(installed.join("mote.toml").is_file());
    assert!(installed.join("src").is_dir());
    assert!(!installed.join(".git").exists());
    assert!(!installed.join("target").exists());
    assert!(!installed.join("mote.lock").exists());

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_install_transitive_deps() {
    let root =
      PathBuf::from("/tmp").join(format!("monad-test-install-trans-{:x}", std::process::id()));
    let lib_a_dir = root.join("motes").join("lib-a");
    let lib_b_dir = root.join("motes").join("lib-b");

    setup_mote(&lib_a_dir, "lib-a", "0.1.0", &[("lib-b", ">=0.5.0")]);
    setup_mote(&lib_b_dir, "lib-b", "0.5.0", &[]);

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

    let resolved = Resolver::resolve(&manifest, &root, None).unwrap();
    Installer::install(&resolved, &root, None).unwrap();

    assert!(
      root
        .join("motes")
        .join("lib-a-0.1.0")
        .join("mote.toml")
        .is_file()
    );
    assert!(
      root
        .join("motes")
        .join("lib-b-0.5.0")
        .join("mote.toml")
        .is_file()
    );

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_install_missing_source_errors() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-install-missing-{:x}",
      std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();

    let manifest = {
      let mote_toml = root.join("mote.toml");
      std::fs::write(
        &mote_toml,
        r#"
[mote]
name = "root"
version = "1.0.0"

[dependencies]
nonexistent = { path = "motes/nonexistent" }
"#,
      )
      .unwrap();
      Manifest::parse(&mote_toml).unwrap()
    };

    let err = Resolver::resolve(&manifest, &root, None).unwrap_err();
    assert!(
      err.contains("does not exist"),
      "expected 'does not exist' error, got: {err}"
    );

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_install_overwrites_existing() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-install-overwrite-{:x}",
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

    Installer::install(&resolved, &root, None).unwrap();
    let installed = root.join("motes").join("mylib-0.1.0");
    assert!(installed.join("mote.toml").is_file());

    Installer::install(&resolved, &root, None).unwrap();
    assert!(installed.join("mote.toml").is_file());

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_mote_install_dir_sanitizes_version() {
    let tmp = PathBuf::from("/tmp/motes").join(format!("test-sanitize-{:x}", std::process::id()));
    let dir = mote_install_dir(&tmp, "my-lib", "1.0.0+20240101");
    assert_eq!(dir.file_name().unwrap().to_string_lossy(), "my-lib-1.0.0");

    let dir = mote_install_dir(&tmp, "weird name!", "1.0.0-beta.1");
    assert_eq!(
      dir.file_name().unwrap().to_string_lossy(),
      "weird_name_-1.0.0-beta.1"
    );
  }

  // --- Workspace tests ---

  #[test]
  fn test_parse_virtual_workspace_manifest() {
    let toml_str = r#"
[workspace]
members = ["motes/*"]
"#;
    let manifest = Manifest::parse_str(toml_str).unwrap();
    assert!(manifest.mote.is_none());
    let workspace = manifest.workspace.unwrap();
    assert_eq!(workspace.members, vec!["motes/*".to_string()]);
  }

  #[test]
  fn test_parse_mote_with_workspace() {
    let toml_str = r#"
[mote]
name = "root"
version = "1.0.0"

[workspace]
members = ["motes/lib-a", "motes/lib-b"]
"#;
    let manifest = Manifest::parse_str(toml_str).unwrap();
    assert_eq!(manifest.mote.unwrap().name, "root");
    let workspace = manifest.workspace.unwrap();
    assert_eq!(
      workspace.members,
      vec!["motes/lib-a".to_string(), "motes/lib-b".to_string()]
    );
  }

  #[test]
  fn test_manifest_requires_mote_or_workspace() {
    let err = Manifest::parse_str("").unwrap_err();
    assert!(
      err.contains("must have a [mote] or [workspace] section"),
      "got: {err}"
    );
  }

  #[test]
  fn test_workspace_resolve_members_glob() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-workspace-glob-{:x}",
      std::process::id()
    ));
    let lib_a_dir = root.join("motes").join("lib-a");
    let lib_b_dir = root.join("motes").join("lib-b");
    let not_a_mote_dir = root.join("motes").join("not-a-mote");

    setup_mote(&lib_a_dir, "lib-a", "0.1.0", &[]);
    setup_mote(&lib_b_dir, "lib-b", "0.1.0", &[]);
    std::fs::create_dir_all(&not_a_mote_dir).unwrap();

    let workspace = Workspace {
      members: vec!["motes/*".to_string()],
    };
    let mut members = workspace.resolve_members(&root).unwrap();
    members.sort();

    assert_eq!(members, vec![lib_a_dir.clone(), lib_b_dir.clone()]);

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_workspace_resolve_members_exact_path() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-workspace-exact-{:x}",
      std::process::id()
    ));
    let engine_dir = root.join("pkgs").join("engine");
    setup_mote(&engine_dir, "engine", "0.1.0", &[]);

    let workspace = Workspace {
      members: vec!["pkgs/engine".to_string()],
    };
    let members = workspace.resolve_members(&root).unwrap();
    assert_eq!(members, vec![engine_dir]);

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_workspace_resolve_members_missing_exact_path_errors() {
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-workspace-missing-{:x}",
      std::process::id()
    ));
    std::fs::create_dir_all(&root).unwrap();

    let workspace = Workspace {
      members: vec!["pkgs/nonexistent".to_string()],
    };
    let err = workspace.resolve_members(&root).unwrap_err();
    assert!(err.contains("no mote.toml found"), "got: {err}");

    std::fs::remove_dir_all(&root).unwrap();
  }

  #[test]
  fn test_workspace_member_cross_dependency_resolves() {
    // Virtual workspace root with two members; lib-a depends on sibling lib-b via path.
    let root = PathBuf::from("/tmp").join(format!(
      "monad-test-workspace-cross-dep-{:x}",
      std::process::id()
    ));
    let lib_a_dir = root.join("motes").join("lib-a");
    let lib_b_dir = root.join("motes").join("lib-b");

    std::fs::create_dir_all(&root).unwrap();
    std::fs::write(
      root.join("mote.toml"),
      r#"
[workspace]
members = ["motes/*"]
"#,
    )
    .unwrap();

    setup_mote(&lib_a_dir, "lib-a", "0.1.0", &[("lib-b", ">=0.1.0")]);
    setup_mote(&lib_b_dir, "lib-b", "0.1.0", &[]);

    let (_root_path, root_manifest) = Manifest::discover(&root).unwrap();
    assert!(root_manifest.mote.is_none());
    let workspace = root_manifest.workspace.clone().unwrap();
    let member_dirs = workspace.resolve_members(&root).unwrap();
    assert_eq!(member_dirs.len(), 2);

    let lib_a_manifest = Manifest::parse(&lib_a_dir.join("mote.toml")).unwrap();
    let resolved = Resolver::resolve(&lib_a_manifest, &lib_a_dir, None).unwrap();
    assert_eq!(resolved.motes.len(), 1);
    assert_eq!(resolved.motes[0].name, "lib-b");

    std::fs::remove_dir_all(&root).unwrap();
  }
}
