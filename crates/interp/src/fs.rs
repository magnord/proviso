//! The runtime's `Dir`, a directory tree confined to its root (REFERENCE §9.2; OPEN_QUESTIONS
//! Q6, P5).
//!
//! A path names a place under the root. One that is absolute, or whose `..` parts climb above
//! the root, is refused before the file system sees it. `..` is resolved by the text of the
//! path, before any link. Then each existing part is looked up in turn, and a symbolic link
//! is followed only when the place it leads to is under the root too. The operation runs on
//! the path that walk found, which has no links in it. Another process that replaces a part
//! of it with a link between the walk and the operation can still lead it out of the root.

use std::fs;
use std::io::{ErrorKind, Read};
use std::path::{Component, Path, PathBuf};

/// Why an operation failed, as `std.fs`'s `FsError` says it.
#[derive(Debug, PartialEq, Eq)]
pub enum FsFailure {
    NotFound,
    PermissionDenied,
    Other(String),
}

/// The root of a `Dir`. Copies of the capability share it, and so the file system under it.
#[derive(Debug)]
pub struct Root(PathBuf);

impl Root {
    /// A `Dir` rooted at `path`. Its links are resolved once, here, so a place found under it
    /// can be compared with it.
    pub fn new(path: &Path) -> Root {
        Root(fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf()))
    }

    pub fn read_text(&self, path: &str) -> Result<String, FsFailure> {
        let place = self.resolve(path, true)?;
        let mut text = String::new();
        fs::File::open(&place).and_then(|mut file| file.read_to_string(&mut text)).map_err(|e| failure(path, e))?;
        Ok(text)
    }

    /// Replaces the file's text, creating the file if it is missing (Q6).
    pub fn write_text(&self, path: &str, text: &str) -> Result<(), FsFailure> {
        let place = self.resolve(path, true)?;
        fs::write(place, text).map_err(|e| failure(path, e))
    }

    pub fn size(&self, path: &str) -> Result<u64, FsFailure> {
        let place = self.resolve(path, true)?;
        let meta = fs::metadata(place).map_err(|e| failure(path, e))?;
        if meta.is_dir() {
            return Err(other(path, "is a directory"));
        }
        Ok(meta.len())
    }

    /// The paths of the directory's entries, ordered by the bytes of their names, each the
    /// path as its parts are written, then `/` and the entry's name (OPEN_QUESTIONS P5).
    pub fn list(&self, path: &str) -> Result<Vec<String>, FsFailure> {
        let parts = parts(path)?;
        let place = self.resolve(path, true)?;
        let mut names = Vec::new();
        for entry in fs::read_dir(place).map_err(|e| failure(path, e))? {
            let name = entry.map_err(|e| failure(path, e))?.file_name();
            let name = name.into_string().map_err(|_| other(path, "has an entry whose name is not valid UTF-8"))?;
            names.push(name);
        }
        names.sort_unstable();
        let prefix = parts.join("/");
        Ok(names.into_iter().map(|name| if prefix.is_empty() { name } else { format!("{prefix}/{name}") }).collect())
    }

    pub fn create_dir(&self, path: &str) -> Result<(), FsFailure> {
        let place = self.resolve(path, false)?;
        fs::create_dir(place).map_err(|e| failure(path, e))
    }

    /// Removes a file, a link, or an empty directory. A link is removed itself, not what it
    /// leads to. The root isn't the capability's to remove.
    pub fn remove(&self, path: &str) -> Result<(), FsFailure> {
        if parts(path)?.is_empty() {
            return Err(FsFailure::PermissionDenied);
        }
        let place = self.resolve(path, false)?;
        let meta = fs::symlink_metadata(&place).map_err(|e| failure(path, e))?;
        if meta.is_dir() { fs::remove_dir(place) } else { fs::remove_file(place) }.map_err(|e| failure(path, e))
    }

    /// The place `path` names under the root, with each link in it followed, and its last part
    /// followed too when `follow_last` is set. A part that doesn't exist ends the walk, and only
    /// the last part may be missing.
    fn resolve(&self, path: &str, follow_last: bool) -> Result<PathBuf, FsFailure> {
        let parts = parts(path)?;
        let mut place = self.0.clone();
        for (i, part) in parts.iter().enumerate() {
            let last = i + 1 == parts.len();
            let next = place.join(part);
            let meta = match fs::symlink_metadata(&next) {
                Ok(meta) => meta,
                Err(e) if e.kind() == ErrorKind::NotFound && last => return Ok(next),
                Err(e) => return Err(failure(path, e)),
            };
            if meta.file_type().is_symlink() && (follow_last || !last) {
                // A link that leads nowhere can't be shown to stay under the root.
                match fs::canonicalize(&next) {
                    Ok(target) if target.starts_with(&self.0) => place = target,
                    _ => return Err(FsFailure::PermissionDenied),
                }
            } else {
                place = next;
            }
            if !last && !fs::metadata(&place).is_ok_and(|meta| meta.is_dir()) {
                return Err(other(path, "goes through a file"));
            }
        }
        Ok(place)
    }
}

/// The parts of `path` under the root, with `.` dropped and each `..` taking away the part
/// before it. `PermissionDenied` when `path` is absolute or a `..` climbs above the root.
fn parts(path: &str) -> Result<Vec<&str>, FsFailure> {
    let mut parts = Vec::new();
    for component in Path::new(path).components() {
        match component {
            Component::Normal(part) => parts.push(part.to_str().expect("a part of a `str` is one")),
            Component::CurDir => {}
            Component::ParentDir => {
                parts.pop().ok_or(FsFailure::PermissionDenied)?;
            }
            Component::RootDir | Component::Prefix(_) => return Err(FsFailure::PermissionDenied),
        }
    }
    Ok(parts)
}

fn other(path: &str, what: &str) -> FsFailure {
    FsFailure::Other(format!("`{path}` {what}"))
}

/// What the operating system's `error` means for `path`. The messages are the runtime's own,
/// so they read the same on every system, except for kinds of error a `Dir` rarely meets.
fn failure(path: &str, error: std::io::Error) -> FsFailure {
    match error.kind() {
        ErrorKind::NotFound => FsFailure::NotFound,
        ErrorKind::PermissionDenied => FsFailure::PermissionDenied,
        ErrorKind::IsADirectory => other(path, "is a directory"),
        ErrorKind::NotADirectory => other(path, "is not a directory"),
        ErrorKind::AlreadyExists => other(path, "already exists"),
        ErrorKind::DirectoryNotEmpty => other(path, "is not empty"),
        ErrorKind::InvalidData => other(path, "is not valid UTF-8"),
        ErrorKind::InvalidInput | ErrorKind::InvalidFilename => other(path, "is not a valid path"),
        _ => other(path, &format!("failed: {error}")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A new, empty directory, removed when dropped.
    struct Scratch(PathBuf);

    impl Scratch {
        fn new(name: &str) -> Scratch {
            let dir = std::env::temp_dir().join(format!("proviso-fs-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(dir.join("root")).unwrap();
            Scratch(dir)
        }
    }

    impl Drop for Scratch {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn lexical_escapes_are_denied() {
        let scratch = Scratch::new("lexical");
        let root = Root::new(&scratch.0.join("root"));
        for path in ["/etc/hosts", "..", "../x", "a/../../x", "./.."] {
            assert_eq!(root.read_text(path), Err(FsFailure::PermissionDenied), "{path}");
            assert_eq!(root.write_text(path, "x"), Err(FsFailure::PermissionDenied), "{path}");
        }
        assert!(!scratch.0.join("x").exists());
        root.write_text("a/../b", "in").unwrap();
        assert_eq!(fs::read_to_string(scratch.0.join("root/b")).unwrap(), "in");
    }

    #[cfg(unix)]
    #[test]
    fn links_out_of_the_root_are_denied() {
        use std::os::unix::fs::symlink;
        let scratch = Scratch::new("links");
        let root_path = scratch.0.join("root");
        fs::write(scratch.0.join("secret"), "s").unwrap();
        fs::create_dir(scratch.0.join("outside")).unwrap();
        symlink(scratch.0.join("secret"), root_path.join("to_file")).unwrap();
        symlink(scratch.0.join("outside"), root_path.join("to_dir")).unwrap();
        symlink(scratch.0.join("missing"), root_path.join("dangling")).unwrap();
        symlink("..", root_path.join("up")).unwrap();
        fs::write(root_path.join("inside"), "i").unwrap();
        symlink("inside", root_path.join("to_inside")).unwrap();
        let root = Root::new(&root_path);
        for path in ["to_file", "to_dir/x", "dangling", "up/secret"] {
            assert_eq!(root.read_text(path), Err(FsFailure::PermissionDenied), "{path}");
            assert_eq!(root.write_text(path, "x"), Err(FsFailure::PermissionDenied), "{path}");
        }
        assert_eq!(root.list("to_dir"), Err(FsFailure::PermissionDenied));
        assert_eq!(root.create_dir("to_dir/new"), Err(FsFailure::PermissionDenied));
        assert!(!scratch.0.join("missing").exists() && !scratch.0.join("outside/x").exists());
        assert_eq!(fs::read_to_string(scratch.0.join("secret")).unwrap(), "s");
        // A link that stays under the root is followed, and removing a link removes the link.
        assert_eq!(root.read_text("to_inside").unwrap(), "i");
        root.remove("to_file").unwrap();
        assert!(scratch.0.join("secret").exists());
    }
}
