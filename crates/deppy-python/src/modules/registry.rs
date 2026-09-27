use super::{Binding, Exports};

const BUILTINS: &[&str] = &[
    "intro",
    "exact",
    "apply",
    "rewrite",
    "rewrite_in",
    "cases",
    "induction",
    "inductive",
    "constructor",
    "Index",
    "induct",
    "absurd",
    "verified",
    "Refined",
    "verified_spec",
    "invariant",
    "decreases",
    "dependent",
    "theorem",
    "hole",
    "axiom",
    "record",
    "Type",
    "Nat",
    "Z",
    "S",
    "Vec",
    "VNil",
    "VCons",
    "Fin",
    "FZ",
    "FS",
    "Eq",
    "refl",
    "J",
    "nat_elim",
    "vec_elim",
    "fin_elim",
    "record_elim",
    "ann",
    "lam",
    "implicit_lam",
    "ImplicitPi",
    "vnil",
    "vcons",
    "pair",
    "fin0_elim",
    "Pi",
    "Sigma",
    "Pair",
];

pub(super) fn is_builtin(name: &str) -> bool {
    BUILTINS.contains(&name)
}

pub(super) fn declares_builtins(module: &str) -> bool {
    matches!(module, "deppy._builtins" | "deppy.tactics")
}

pub(super) fn builtin_exports(module: &str) -> Exports {
    let names: &[&str] = match module {
        "deppy.nat" => &["Nat", "Z", "S", "nat_elim"],
        "deppy.equality" => &["Eq", "refl", "J"],
        "deppy.fin" => &["Fin", "FZ", "FS", "fin_elim", "fin0_elim"],
        "deppy.vectors" => &["Vec", "VNil", "VCons", "vnil", "vcons", "vec_elim"],
        _ => &[],
    };
    names
        .iter()
        .map(|name| ((*name).into(), Binding::builtin(name)))
        .collect()
}

// Python packaging and the static loader share the same public prelude.
const PRELUDE: &str = include_str!("../../stdlib/deppy/__init__.py");

pub(super) fn standard(name: &str) -> Option<&'static str> {
    match name {
        "deppy.tactics" => Some(include_str!("../../stdlib/deppy/tactics.py")),
        "deppy.integer" => Some(include_str!("../../stdlib/deppy/integer.py")),
        "deppy.arithmetic" => Some(include_str!("../../stdlib/deppy/arithmetic.py")),
        "deppy.verified_loop" => Some(include_str!("../../stdlib/deppy/verified_loop.py")),
        "deppy.verified" => Some(include_str!("../../stdlib/deppy/verified.py")),
        "deppy.indexed" => Some(include_str!("../../stdlib/deppy/indexed.py")),
        "deppy.data" => Some(include_str!("../../stdlib/deppy/data.py")),
        "deppy.bool" => Some(include_str!("../../stdlib/deppy/bool.py")),
        "deppy.nat_bool" => Some(include_str!("../../stdlib/deppy/nat_bool.py")),
        "deppy.lists" => Some(include_str!("../../stdlib/deppy/lists.py")),
        "deppy.finite" => Some(include_str!("../../stdlib/deppy/finite.py")),
        "deppy.functions" => Some(include_str!("../../stdlib/deppy/functions.py")),
        "deppy.permutations" => Some(include_str!("../../stdlib/deppy/permutations.py")),
        "deppy.nat_order" => Some(include_str!("../../stdlib/deppy/nat_order.py")),
        "deppy" => Some(PRELUDE),
        "deppy._builtins" => Some(include_str!("../../stdlib/deppy/_builtins.py")),
        "deppy.nat" => Some(include_str!("../../stdlib/deppy/nat.py")),
        "deppy.vectors" => Some(include_str!("../../stdlib/deppy/vectors.py")),
        "deppy.fin" => Some(include_str!("../../stdlib/deppy/fin.py")),
        "deppy.equality" => Some(include_str!("../../stdlib/deppy/equality.py")),
        _ => None,
    }
}
