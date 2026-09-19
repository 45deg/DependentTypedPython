use deppy_python::{analyze_module, check_module, Target};

#[test]
fn goals_preserve_context_and_never_register_unfinished_definitions() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Eq, hole\n@dependent\ndef unfinished(n: Nat) -> Eq[Nat, n, n]:\n    x: Nat = n\n    return hole('identity')\n";
    let analysis = analyze_module(source, Target::Python314);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    let goal = &analysis.goals[0];
    assert_eq!(goal.name, "identity");
    assert_eq!(goal.expected, "Eq[Nat, n, n]");
    assert_eq!(goal.context[0].name, "n");
    assert_eq!(goal.context[1].name, "x");
    assert_eq!(goal.context[1].value.as_deref(), Some("n"));
    let location = goal.location.as_ref().unwrap();
    assert_eq!(&source[location.start..location.end], "hole('identity')");
    assert!(check_module(source, Target::Python314).is_err());
}

#[test]
fn unused_holes_remain_unfinished_and_untyped_holes_are_rejected() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, hole\n@dependent\ndef unfinished() -> Nat:\n    unused: Nat = hole('unused')\n    return 0\n";
    assert_eq!(analyze_module(source, Target::Python314).goals.len(), 1);
    let untyped = source.replace("unused: Nat", "unused");
    let result = analyze_module(&untyped, Target::Python314);
    assert!(result.goals.is_empty());
    assert!(result.checked.is_none());
    assert!(result.diagnostics[0].message.contains("annotation"));
}

#[test]
fn diagnostics_point_at_expressions_and_imported_sources() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat\n@dependent\ndef wrong() -> Nat:\n    return Nat\n";
    let error = match check_module(source, Target::Python314) {
        Err(e) => e,
        Ok(_) => panic!("expected error"),
    };
    assert_eq!(&source[error.span.start..error.span.end], "Nat");
    assert_eq!(error.details.line, Some(5));
    assert_eq!(error.details.column, Some(12));
    assert_eq!(error.details.expected.as_deref(), Some("Nat"));
    assert_eq!(error.details.actual.as_deref(), Some("Type"));
    assert_eq!(error.details.related.len(), 1);
    let mut resolver = |name: &str| Ok((name == "library").then(|| source.to_owned()));
    let result = deppy_python::analyze_module_with_resolver(
        "from __future__ import annotations\nfrom library import wrong\n",
        Target::Python314,
        &mut resolver,
    );
    assert_eq!(
        result.diagnostics[0].details.source.as_deref(),
        Some("library")
    );
    assert_eq!(result.diagnostics[0].details.line, Some(5));
}

#[test]
fn analysis_collects_independent_goals_with_distinct_ids() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, hole\n@dependent\ndef first() -> Nat:\n    return hole('a')\n@dependent\ndef second() -> Nat:\n    return hole('b')\n@dependent\ndef blocked() -> Nat:\n    return first()\n";
    let analysis = analyze_module(source, Target::Python314);
    assert_eq!(analysis.goals.len(), 2);
    assert_ne!(analysis.goals[0].id, analysis.goals[1].id);
    assert!(analysis.checked.is_none());
    assert!(analysis
        .diagnostics
        .iter()
        .any(|d| d.message.contains("unknown name: first")));
}

#[test]
fn structural_goals_keep_pattern_binder_names() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, Z, S, hole\n@dependent(decreases='n')\ndef count(n: Nat) -> Nat:\n    match n:\n        case Z():\n            return 0\n        case S(k):\n            return hole('step')\n";
    let analysis = analyze_module(source, Target::Python314);
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    assert!(analysis.goals[0]
        .context
        .iter()
        .any(|local| local.name == "k"));
    assert!(analysis.goals[0]
        .context
        .iter()
        .all(|local| !local.name.contains('\0')));
}

#[test]
fn configurable_budgets_fail_closed() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat\n@dependent\ndef value() -> Nat:\n    return 0\n";
    for options in [
        deppy_python::FrontendOptions {
            elaboration_steps: 0,
            ..Default::default()
        },
        deppy_python::FrontendOptions {
            lowering_steps: 0,
            ..Default::default()
        },
    ] {
        assert!(deppy_python::check_module_with_options(source, options).is_err());
    }
    assert!(deppy_python::check_module_with_options(source, Default::default()).is_ok());
}

#[test]
fn goal_diagnostics_share_ids_locations_and_root_identity() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, hole\n@dependent\ndef first() -> Nat:\n    return hole('a')\n@dependent\ndef second() -> Nat:\n    return hole('b')\n";
    let mut analysis = deppy_python::analyze_module_with_options(source, Default::default());
    analysis.set_root_source_name("proof.py");
    assert_eq!(analysis.goals.len(), 2);
    for (id, diagnostic) in analysis.diagnostics.iter().enumerate() {
        assert_eq!(diagnostic.details.goals, vec![analysis.goals[id].clone()]);
        let location = analysis.goals[id].location.as_ref().unwrap();
        assert_eq!(location.source, "proof.py");
        assert_eq!(diagnostic.span.start, location.start);
        assert_eq!(diagnostic.span.end, location.end);
        assert!(diagnostic.to_string().starts_with("proof.py:"));
        assert_eq!(diagnostic.details.related.len(), 1);
        assert_eq!(diagnostic.details.related[0].source, "proof.py");
    }
}

#[test]
fn naming_root_does_not_replace_imported_goal_sources() {
    let library = "from __future__ import annotations\nfrom deppy import dependent, Nat, hole\n@dependent\ndef unfinished() -> Nat:\n    return hole('imported')\n";
    let mut resolver = |name: &str| Ok((name == "library").then(|| library.to_owned()));
    let mut analysis = deppy_python::analyze_module_with_resolver(
        "from library import unfinished\n",
        Target::Python314,
        &mut resolver,
    );
    analysis.set_root_source_name("main.py");
    assert_eq!(analysis.goals.len(), 1);
    assert_eq!(
        analysis.goals[0].location.as_ref().unwrap().source,
        "library"
    );
    assert_eq!(
        analysis.diagnostics[0].details.source.as_deref(),
        Some("library")
    );
    assert_eq!(analysis.diagnostics[0].details.line, Some(5));
    assert_eq!(analysis.diagnostics[0].details.column, Some(12));
}

#[test]
fn annotated_hole_has_expected_type_and_unicode_source_coordinates() {
    let source = "from __future__ import annotations\nfrom deppy import dependent, Nat, hole, ann\n@dependent\ndef proof() -> Nat:\n    証明 = ann(hole('名前'), Nat)\n    return 証明\n";
    let analysis = analyze_module(source, Target::Python314);
    assert!(analysis.checked.is_none());
    assert_eq!(analysis.goals.len(), 1, "{:?}", analysis.diagnostics);
    assert_eq!(analysis.goals[0].expected, "Nat");
    let diagnostic = &analysis.diagnostics[0];
    assert_eq!(diagnostic.details.line, Some(5));
    assert_eq!(diagnostic.details.column, Some(14));
    assert_eq!(
        &source[diagnostic.span.start..diagnostic.span.end],
        "hole('名前')"
    );
}
