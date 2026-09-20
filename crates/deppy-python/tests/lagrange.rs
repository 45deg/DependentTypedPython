use deppy_python::{check_module, Target};

const SOURCE: &str = include_str!("../examples/lagrange.py");

// The proof's nested dependent terms need more stack than the test harness's
// small worker stack. This does not change the elaboration or kernel budgets.
fn with_proof_stack(check: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(check)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn finite_group_lagrange_and_instances_are_axiom_free() {
    with_proof_stack(|| {
        let module = check_module(SOURCE, Target::Python314).unwrap();
        for name in [
            "uniform_partition",
            "coset_size",
            "lagrange",
            "lagrange_trivial_example",
            "lagrange_whole_example",
        ] {
            assert!(module.interface.exports().contains_key(name), "{name}");
            assert!(module.axiom_dependencies[name].is_empty(), "{name}");
        }
        assert!(module.axiom_dependencies.values().all(Vec::is_empty));
    });
}

#[test]
fn lagrange_rejects_wrong_divisibility_and_unproved_partition() {
    with_proof_stack(|| {
        for (before, after) in [
            (
                "def lagrange_whole_example() -> Divisible(2, 2):",
                "def lagrange_whole_example() -> Divisible(3, 2):",
            ),
            (
                "return partition_fuel(dec, laws, h, length(xs))(xs)(le_refl(length(xs)))(uniform)",
                "return Pair(0, refl(length(xs)))",
            ),
        ] {
            assert_eq!(SOURCE.matches(before).count(), 1);
            let invalid = SOURCE.replace(before, after);
            let error = check_module(&invalid, Target::Python314).err().unwrap();
            assert!(!error.message.contains("budget"), "{}", error.message);
        }
    });
}
