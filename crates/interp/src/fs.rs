//! The runtime's `Dir`, a directory tree confined to its root (REFERENCE §9.2; OPEN_QUESTIONS
//! Q6, P5).
//!
//! A path names a place under the root. One that is absolute, or whose `..` parts climb above
//! the root, is refused before the file system sees it. `..` is resolved by the text of the
//! path, before any link. Then each existing part is looked up in turn, and a symbolic link
//! is followed only when the place it leads to is under the root too. The operation runs on
//! the path that walk found, which has no links in it, except that `create_dir` and `remove`
//! act on a link in the last part rather than on what it leads to. A path that ends in `/` or
//! `/.` names a directory, so `read_text`, `write_text` and `size` refuse it, and the other
//! operations follow a link in its last part. `remove` refuses one that leads to no directory,
//! and any path that leads to the root.
//!
//! Confinement is by path. Another process that replaces a part of the path with a link
//! between the walk and the operation can still lead the operation out of the root. A hard
//! link or a mount that someone else put under the root reaches what it leads to, and
//! following a link shows whether the places it passes through exist.

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
        let place = self.file(path)?;
        let mut text = String::new();
        fs::File::open(&place).and_then(|mut file| file.read_to_string(&mut text)).map_err(|e| failure(path, e))?;
        Ok(text)
    }

    /// Replaces the file's text, creating the file if it is missing (Q6).
    pub fn write_text(&self, path: &str, text: &str) -> Result<(), FsFailure> {
        let place = self.file(path)?;
        fs::write(place, text).map_err(|e| failure(path, e))
    }

    pub fn size(&self, path: &str) -> Result<u64, FsFailure> {
        let place = self.file(path)?;
        fs::metadata(place).map(|meta| meta.len()).map_err(|e| failure(path, e))
    }

    /// The place of the file `path` names, which may be missing. A directory, a path that
    /// names one, and a place that is neither a file nor a directory, such as a pipe that
    /// would block a read, are refused.
    fn file(&self, path: &str) -> Result<PathBuf, FsFailure> {
        // An escape is refused first, as it is for every operation.
        parts(path)?;
        if names_dir(path) {
            return Err(other(path, "names a directory"));
        }
        let place = self.resolve(path, true)?;
        match fs::metadata(&place) {
            Ok(meta) if meta.is_dir() => Err(other(path, "is a directory")),
            Ok(meta) if !meta.is_file() => Err(other(path, "is not a regular file")),
            _ => Ok(place),
        }
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
        let place = self.resolve(path, names_dir(path))?;
        fs::create_dir(place).map_err(|e| failure(path, e))
    }

    /// Removes a file, a link, or an empty directory. A link is removed itself, not what it
    /// leads to, unless the path ends in `/`. The root isn't the capability's to remove, by any
    /// path.
    pub fn remove(&self, path: &str) -> Result<(), FsFailure> {
        let place = self.resolve(path, names_dir(path))?;
        // The path may be empty, or end in a link to the root.
        if place == self.0 {
            return Err(FsFailure::PermissionDenied);
        }
        let meta = fs::symlink_metadata(&place).map_err(|e| failure(path, e))?;
        // A path that names a directory never removes a file, nor a link to one.
        if names_dir(path) && !meta.is_dir() {
            return Err(other(path, "is not a directory"));
        }
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

/// Whether `path` ends in `/` or `/.`, which `Path::components` drops but which names a
/// directory.
fn names_dir(path: &str) -> bool {
    path.ends_with('/') || path.ends_with("/.")
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
        for path in ["/etc/hosts", "/", "..", "../", "../x", "a/../../x", "./..", "../."] {
            assert_eq!(root.read_text(path), Err(FsFailure::PermissionDenied), "{path}");
            assert_eq!(root.write_text(path, "x"), Err(FsFailure::PermissionDenied), "{path}");
        }
        assert!(!scratch.0.join("x").exists());
        root.write_text("a/../b", "in").unwrap();
        assert_eq!(fs::read_to_string(scratch.0.join("root/b")).unwrap(), "in");
    }

    #[test]
    fn a_trailing_slash_names_a_directory() {
        let scratch = Scratch::new("slash");
        let root = Root::new(&scratch.0.join("root"));
        root.write_text("f", "text").unwrap();
        for path in ["f/", "f/.", "new/", "new/."] {
            let names = || other(path, "names a directory");
            assert_eq!(root.read_text(path), Err(names()), "{path}");
            assert_eq!(root.write_text(path, "x"), Err(names()), "{path}");
            assert_eq!(root.size(path), Err(names()), "{path}");
        }
        assert!(!scratch.0.join("root/new").exists());
        root.create_dir("d/").unwrap();
        assert_eq!(root.list("d/."), Ok(Vec::new()));
        root.remove("d/").unwrap();
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
        // A trailing `/` follows a link in the last part, which here leads out, and never
        // removes a file or a link to one.
        assert_eq!(root.remove("to_dir/"), Err(FsFailure::PermissionDenied));
        assert_eq!(root.remove("to_inside/"), Err(other("to_inside/", "is not a directory")));
        assert_eq!(root.remove("inside/."), Err(other("inside/.", "is not a directory")));
        assert_eq!(root.read_text("inside").unwrap(), "i");
        assert!(scratch.0.join("outside").exists());
    }

    #[cfg(unix)]
    #[test]
    fn the_root_is_not_removed_through_a_link() {
        use std::os::unix::fs::symlink;
        let scratch = Scratch::new("root_link");
        let root_path = scratch.0.join("root");
        fs::create_dir(root_path.join("d")).unwrap();
        symlink(".", root_path.join("here")).unwrap();
        symlink("..", root_path.join("d/back")).unwrap();
        let root = Root::new(&root_path);
        for path in ["", ".", "d/..", "here/", "here/.", "d/back/", "d/back/."] {
            assert_eq!(root.remove(path), Err(FsFailure::PermissionDenied), "{path}");
        }
        // Without a trailing `/`, the link itself is removed.
        root.remove("here").unwrap();
        assert!(root_path.exists() && !root_path.join("here").exists());
    }

    #[cfg(unix)]
    #[test]
    fn a_pipe_is_not_read() {
        let scratch = Scratch::new("pipe");
        let root_path = scratch.0.join("root");
        let made = std::process::Command::new("mkfifo").arg(root_path.join("pipe")).status();
        if !made.is_ok_and(|status| status.success()) {
            return;
        }
        let root = Root::new(&root_path);
        assert_eq!(root.read_text("pipe"), Err(other("pipe", "is not a regular file")));
        assert_eq!(root.write_text("pipe", "x"), Err(other("pipe", "is not a regular file")));
    }
}
