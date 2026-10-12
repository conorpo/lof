use super::*;
use crate::core::kernel::Context;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Files(PathBuf);
impl Files {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = std::env::temp_dir().join(format!(
            "lof-modules-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, source: &str) -> PathBuf {
        let path = self.0.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, source).unwrap();
        path
    }
}
impl Drop for Files {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn relative_imports_reexports_and_private_dependencies_use_real_constants() {
    let files = Files::new();
    files.write("lib/values.lof", "let hidden=#1; export let value=hidden;");
    files.write(
        "lib/alias.lof",
        "import \"values.lof\" as V; export let value=V::value;",
    );
    let root = files.write(
        "main.lof",
        "import \"lib/alias.lof\" as V; export let value=V::value;",
    );
    let mut loader = ModuleLoader::new();
    let module = loader.load(&root).unwrap();
    let term = module.term("value").unwrap();
    let Term::Const(id) = &term else {
        panic!("export must retain a constant reference");
    };
    assert!(matches!(
        loader.environment().definition(id).unwrap().value(),
        Term::Const(_)
    ));
    assert_eq!(
        loader.environment().infer(&Context::new(), &term).unwrap(),
        Term::nat()
    );
    assert_eq!(loader.environment().normalize(&term), Term::from(1));
    assert!(module.term("hidden").is_err());
    assert!(module.parse("V::value").is_err()); // imports are not implicitly reexported
    let same = loader.load(files.0.join("lib/../main.lof")).unwrap();
    assert!(Rc::ptr_eq(&module, &same));
}

#[test]
fn aliases_disambiguate_identical_export_names_and_preserve_local_shadowing() {
    let files = Files::new();
    files.write("one.lof", "export let value=#1;");
    files.write("two.lof", "export let value=#2;");
    let root = files.write(
        "main.lof",
        "import \"one.lof\" as One; import \"two.lof\" as Two;
        export let pair=(One::value,Two::value) : Nat*Nat;
        let value=One::value; export let id=λvalue.value : Nat -> Nat;",
    );
    let mut loader = ModuleLoader::new();
    let module = loader.load(root).unwrap();
    assert_eq!(
        loader
            .environment()
            .normalize(&module.term("pair").unwrap()),
        Term::pair(Term::from(1), Term::from(2))
    );
    let application = module.parse("id(#3)").unwrap();
    assert_eq!(loader.environment().normalize(&application), Term::from(3));
}

#[test]
fn inferred_eliminator_types_can_be_registered_without_source_annotations() {
    let files = Files::new();
    let root = files.write("main.lof", "export let value=recNat(Nat,#1,λn.λr.r)(#0);");
    let loaded = LoadedModule::load(root).unwrap();
    assert_eq!(
        loaded
            .environment()
            .normalize(&loaded.term("value").unwrap()),
        Term::from(1)
    );
}

#[test]
fn typed_lambda_exports_infer_without_a_full_annotation_and_use_imported_types() {
    let files = Files::new();
    files.write("types.lof", "export let A=Nat;");
    let root = files.write(
        "main.lof",
        "import \"./types.lof\" as T;
        export let identity=λ(A:U0).λ(x:A).x;
        export let local_id=λ(x:T::A).x;
        export let inv=λ(A:U0).ind_id(A,λx.λy.λp.y=x,λx.refl(x));",
    );
    let loaded = LoadedModule::load(root).unwrap();
    for (source, expected) in [
        ("identity(Nat,#7)", Term::from(7)),
        ("local_id(#3)", Term::from(3)),
        ("inv(Nat,#2,#2,refl(#2))", Term::refl(Term::from(2))),
    ] {
        let application = loaded.module().parse(source).unwrap();
        loaded
            .environment()
            .infer(&Context::new(), &application)
            .unwrap();
        assert_eq!(loaded.environment().normalize(&application), expected);
    }
    for source in [
        "export let bad=λ(x:#0).x;",
        "export let bad=λ(x:Nat).x : 1 -> 1;",
    ] {
        let root = files.write("bad.lof", source);
        assert!(LoadedModule::load(root).is_err(), "accepted {source}");
    }
}

#[test]
fn all_definitions_are_checked_and_forward_or_private_names_are_rejected() {
    let files = Files::new();
    files.write("dep.lof", "let hidden=#0; export let visible=#0;");
    for source in [
        "let bad=Succ(Nat); export let good=#0;",
        "export let first=second; let second=#0;",
        "export let self_ref=self_ref;",
        "import \"dep.lof\" as D; export let value=D::hidden;",
        "import \"dep.lof\" as D; export let value=visible;",
        "export let proof=refl(#0) : #0=#1;",
    ] {
        let root = files.write("bad.lof", source);
        assert!(ModuleLoader::new().load(root).is_err(), "accepted {source}");
    }
}

#[test]
fn duplicate_names_and_invalid_import_paths_are_rejected() {
    let files = Files::new();
    files.write("dep.lof", "export let value=#0;");
    for source in [
        "let value=#0; export let value=#1;",
        "import \"dep.lof\" as D; import \"dep.lof\" as D;",
        "import \"dep.lof\" as D; let D=#0;",
        "import \"\" as D;",
        "import \"/absolute.lof\" as D;",
        "import \"missing.lof\" as D;",
    ] {
        let root = files.write("bad.lof", source);
        assert!(ModuleLoader::new().load(root).is_err(), "accepted {source}");
    }
}

#[test]
fn diamond_dependencies_are_shared_and_cycles_report_the_import_chain() {
    let files = Files::new();
    files.write("base.lof", "export let value=#0;");
    for name in ["left", "right"] {
        files.write(
            &format!("{name}.lof"),
            "import \"base.lof\" as B; export let value=B::value;",
        );
    }
    let root = files.write(
        "root.lof",
        "import \"left.lof\" as L; import \"right.lof\" as R; export let value=L::value;",
    );
    assert!(ModuleLoader::new().load(root).is_ok());
    let a = files.write("a.lof", "import \"b.lof\" as B;");
    files.write("b.lof", "import \"a.lof\" as A;");
    let error = ModuleLoader::new().load(a).unwrap_err().to_string();
    assert!(error.contains("cyclic import") && error.contains("a.lof") && error.contains("b.lof"));
}

#[test]
fn failed_loads_roll_back_and_unsaved_dependency_sources_override_disk() {
    let files = Files::new();
    files.write("dep.lof", "export let value=#0;");
    let root = files.write(
        "root.lof",
        "import \"dep.lof\" as D; let good=D::value; export let bad=missing;",
    );
    let mut loader = ModuleLoader::new();
    assert!(loader.load(&root).is_err());
    files.write(
        "root.lof",
        "import \"dep.lof\" as D; export let value=D::value;",
    );
    loader
        .set_source(files.0.join("dep.lof"), "export let value=#2;".to_owned())
        .unwrap();
    let module = loader.load(root).unwrap();
    assert_eq!(
        loader
            .environment()
            .normalize(&module.term("value").unwrap()),
        Term::from(2)
    );
    let mut fresh = ModuleLoader::new();
    let new = files.0.join("unsaved.lof");
    fresh
        .set_source(&new, "export let value=#3;".to_owned())
        .unwrap();
    assert!(fresh.load(new).is_ok());
}
