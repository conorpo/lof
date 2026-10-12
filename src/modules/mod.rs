//! File-based modules: explicit exports, relative imports, and kernel checking.

use std::{
    collections::BTreeMap,
    fmt, fs,
    path::{Component, Path, PathBuf},
    rc::Rc,
};

use crate::{
    core::{
        environment::Environment,
        kernel::TypeError,
        terms::{GlobalId, Term},
    },
    parse::{self, FrontendError, ParseError, ResolveError},
};

#[derive(Debug)]
pub enum ModuleError {
    Io {
        path: PathBuf,
        source: std::io::Error,
    },
    Parse {
        path: PathBuf,
        source: ParseError,
    },
    Resolve {
        path: PathBuf,
        offset: usize,
        name: String,
        source: ResolveError,
    },
    Type {
        path: PathBuf,
        offset: usize,
        name: String,
        source: TypeError,
    },
    Duplicate {
        path: PathBuf,
        offset: usize,
        name: String,
    },
    InvalidImport {
        path: PathBuf,
        offset: usize,
        message: String,
    },
    Import {
        path: PathBuf,
        offset: usize,
        alias: String,
        source: Box<ModuleError>,
    },
    Cycle {
        paths: Vec<PathBuf>,
    },
    MissingExport {
        path: PathBuf,
        name: String,
    },
}

impl ModuleError {
    pub fn offset(&self) -> usize {
        match self {
            Self::Parse { source, .. } => source.offset,
            Self::Resolve { offset, .. }
            | Self::Type { offset, .. }
            | Self::Duplicate { offset, .. }
            | Self::InvalidImport { offset, .. }
            | Self::Import { offset, .. } => *offset,
            _ => 0,
        }
    }
}

impl fmt::Display for ModuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Parse { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Resolve {
                path, name, source, ..
            } => write!(f, "{}: definition {name}: {source}", path.display()),
            Self::Type {
                path, name, source, ..
            } => write!(f, "{}: definition {name}: {source}", path.display()),
            Self::Duplicate { path, name, .. } => write!(
                f,
                "{}: duplicate definition or import alias {name}",
                path.display()
            ),
            Self::InvalidImport { path, message, .. } => write!(f, "{}: {message}", path.display()),
            Self::Import {
                path,
                alias,
                source,
                ..
            } => write!(f, "{}: import {alias}: {source}", path.display()),
            Self::Cycle { paths } => {
                f.write_str("cyclic import: ")?;
                for (i, path) in paths.iter().enumerate() {
                    if i != 0 {
                        f.write_str(" -> ")?;
                    }
                    write!(f, "{}", path.display())?;
                }
                Ok(())
            }
            Self::MissingExport { path, name } => {
                write!(f, "{}: no export named {name}", path.display())
            }
        }
    }
}

impl std::error::Error for ModuleError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Parse { source, .. } => Some(source),
            Self::Resolve { source, .. } => Some(source),
            Self::Type { source, .. } => Some(source),
            Self::Import { source, .. } => Some(source),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Module {
    path: PathBuf,
    exports: BTreeMap<String, GlobalId>,
    scope: BTreeMap<String, GlobalId>,
}

impl Module {
    /// Print core terms with the source names visible in this module.
    pub fn display<'a>(&'a self, term: &'a Term) -> crate::core::pretty::PrettyTerm<'a> {
        term.display_with_names(&self.scope)
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
    pub fn exports(&self) -> &BTreeMap<String, GlobalId> {
        &self.exports
    }
    pub(crate) fn scope(&self) -> &BTreeMap<String, GlobalId> {
        &self.scope
    }

    pub fn term(&self, name: &str) -> Result<Term, ModuleError> {
        self.exports
            .get(name)
            .cloned()
            .map(Term::constant)
            .ok_or_else(|| ModuleError::MissingExport {
                path: self.path.clone(),
                name: name.to_owned(),
            })
    }

    /// Parse an expression using only this module's public exports.
    pub fn parse(&self, source: &str) -> Result<Term, FrontendError> {
        Ok(parse::parse(source)?.lower_with_globals(&[], &self.exports)?)
    }
}

/// One loading session owns a shared kernel environment and module cache.
/// Create a new session to reload edited source files.
#[derive(Default)]
pub struct ModuleLoader {
    environment: Environment,
    modules: BTreeMap<PathBuf, Rc<Module>>,
    loading: Vec<PathBuf>,
    sources: BTreeMap<PathBuf, String>,
}

impl ModuleLoader {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// An unsaved editor document overrides disk content. Set overrides before
    /// loading modules; caches deliberately retain their original snapshot.
    pub fn set_source(&mut self, path: impl AsRef<Path>, source: String) -> std::io::Result<()> {
        self.sources.insert(absolute_path(path.as_ref())?, source);
        Ok(())
    }

    pub fn load(&mut self, path: impl AsRef<Path>) -> Result<Rc<Module>, ModuleError> {
        let input = path.as_ref();
        let path = absolute_path(input).map_err(|source| ModuleError::Io {
            path: input.to_owned(),
            source,
        })?;
        // Loading is transactional: a rejected module cannot leave declarations
        // behind that interfere with retrying a corrected source file.
        let saved_environment = self.environment.clone();
        let saved_modules = self.modules.clone();
        let result = self.load_inner(path);
        if result.is_err() {
            self.environment = saved_environment;
            self.modules = saved_modules;
        }
        result
    }

    fn load_inner(&mut self, path: PathBuf) -> Result<Rc<Module>, ModuleError> {
        if let Some(module) = self.modules.get(&path) {
            return Ok(module.clone());
        }
        if let Some(start) = self.loading.iter().position(|entry| entry == &path) {
            let mut paths = self.loading[start..].to_vec();
            paths.push(path);
            return Err(ModuleError::Cycle { paths });
        }
        let source = match self.sources.get(&path) {
            Some(source) => source.clone(),
            None => fs::read_to_string(&path).map_err(|source| ModuleError::Io {
                path: path.clone(),
                source,
            })?,
        };
        let syntax = parse::parse_module(&source).map_err(|source| ModuleError::Parse {
            path: path.clone(),
            source,
        })?;
        self.loading.push(path.clone());
        let result = self.check_module(&path, syntax);
        self.loading.pop();
        if let Ok(module) = &result {
            self.modules.insert(path, module.clone());
        }
        result
    }

    fn check_module(
        &mut self,
        path: &Path,
        syntax: parse::ModuleSyntax,
    ) -> Result<Rc<Module>, ModuleError> {
        let mut globals = BTreeMap::new();
        let mut names = std::collections::BTreeSet::new();
        let mut exports = BTreeMap::new();
        for import in syntax.imports {
            if !names.insert(import.alias.clone()) {
                return Err(ModuleError::Duplicate {
                    path: path.to_owned(),
                    offset: import.offset,
                    name: import.alias,
                });
            }
            if import.path.is_empty() || Path::new(&import.path).is_absolute() {
                return Err(ModuleError::InvalidImport {
                    path: path.to_owned(),
                    offset: import.offset,
                    message: "imports require a nonempty relative file path".to_owned(),
                });
            }
            let imported_path = path
                .parent()
                .expect("absolute file path")
                .join(&import.path);
            let imported = absolute_path(&imported_path)
                .map_err(|source| ModuleError::Io {
                    path: imported_path,
                    source,
                })
                .and_then(|path| self.load_inner(path))
                .map_err(|source| ModuleError::Import {
                    path: path.to_owned(),
                    offset: import.offset,
                    alias: import.alias.clone(),
                    source: Box::new(source),
                })?;
            for (name, id) in imported.exports() {
                globals.insert(format!("{}::{name}", import.alias), id.clone());
            }
        }
        for definition in syntax.definitions {
            let name = definition.name;
            if !names.insert(name.clone()) {
                return Err(ModuleError::Duplicate {
                    path: path.to_owned(),
                    offset: definition.offset,
                    name,
                });
            }
            let value = definition
                .value
                .lower_with_globals(&[], &globals)
                .map_err(|source| ModuleError::Resolve {
                    path: path.to_owned(),
                    offset: definition.offset,
                    name: name.clone(),
                    source,
                })?;
            let id = GlobalId::new(format!("{}::{name}", path.display()));
            self.environment
                .define_inferred(id.clone(), value)
                .map_err(|source| ModuleError::Type {
                    path: path.to_owned(),
                    offset: definition.offset,
                    name: name.clone(),
                    source,
                })?;
            globals.insert(name.clone(), id.clone());
            if definition.exported {
                exports.insert(name, id);
            }
        }
        Ok(Rc::new(Module {
            path: path.to_owned(),
            exports,
            scope: globals,
        }))
    }
}

/// Canonical paths deduplicate symlinks and spelling differences. Nonexistent
/// editor files use normalized absolute paths until they are saved.
fn absolute_path(path: &Path) -> std::io::Result<PathBuf> {
    if let Ok(path) = fs::canonicalize(path) {
        return Ok(path);
    }
    let path = if path.is_absolute() {
        path.to_owned()
    } else {
        std::env::current_dir()?.join(path)
    };
    let mut result = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                result.pop();
            }
            component => result.push(component.as_os_str()),
        }
    }
    Ok(result)
}

/// An owned module and the checked environment needed to use its terms.
pub struct LoadedModule {
    loader: ModuleLoader,
    module: Rc<Module>,
}

impl LoadedModule {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, ModuleError> {
        let mut loader = ModuleLoader::new();
        let module = loader.load(path)?;
        Ok(Self { loader, module })
    }
    pub fn environment(&self) -> &Environment {
        self.loader.environment()
    }
    pub fn module(&self) -> &Module {
        &self.module
    }
    pub fn term(&self, name: &str) -> Result<Term, ModuleError> {
        self.module.term(name)
    }
}

/// Load relative to the calling Rust source file, not the process directory.
#[doc(hidden)]
pub fn import_from_rust(
    manifest: &str,
    source_file: &str,
    path: &str,
) -> Result<LoadedModule, ModuleError> {
    let source = Path::new(manifest).join(source_file);
    LoadedModule::load(
        source
            .parent()
            .expect("Rust source file has a parent")
            .join(path),
    )
}

/// Select several exports from one LOF file as statically named Rust fields.
/// Parsing, export lookup, and LOF type checking happen when this executes.
#[macro_export]
macro_rules! import_lof {
    ($path:expr; $($name:ident),+ $(,)?) => {{
        (|| -> ::std::result::Result<_, $crate::modules::ModuleError> {
            struct Imports {
                $(pub $name: $crate::core::terms::Term,)+
                __lof_module: $crate::modules::LoadedModule,
            }
            impl Imports {
                pub fn environment(&self) -> &$crate::core::environment::Environment {
                    self.__lof_module.environment()
                }
                pub fn module(&self) -> &$crate::modules::Module {
                    self.__lof_module.module()
                }
            }
            let loaded = $crate::modules::import_from_rust(env!("CARGO_MANIFEST_DIR"), file!(), $path)?;
            Ok(Imports { $($name: loaded.term(stringify!($name))?,)+ __lof_module: loaded })
        })()
    }};
    ($path:expr) => {
        $crate::modules::import_from_rust(env!("CARGO_MANIFEST_DIR"), file!(), $path)
    };
}

#[cfg(test)]
mod tests;
