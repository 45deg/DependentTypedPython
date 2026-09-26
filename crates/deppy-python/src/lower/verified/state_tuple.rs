//! The dependent product used to pass verified locals through loop and flow proofs.
use super::*;

pub(super) fn pack(names: &[String], state: &State) -> E {
    names
        .iter()
        .rev()
        .fold(E::name("deppy.data.MkUnit"), |tail, name| {
            E::pair(E::name(state.scope.aliases.get(name).unwrap_or(name)), tail)
        })
}

pub(super) fn state_type(names: &[String], state: &State) -> E {
    names
        .iter()
        .rev()
        .fold(E::name("deppy.data.Unit"), |tail, name| {
            E::sigma("$field", state.types[name].expr(), tail)
        })
}

pub(super) fn project(names: &[String], state: &State, value: E) -> (State, Vec<(String, E, E)>) {
    let mut state = state.clone();
    let mut bindings = vec![];
    let mut tail = value;
    for (i, name) in names.iter().enumerate() {
        let fresh = format!("$state_field{i}");
        bindings.push((fresh.clone(), state.types[name].expr(), tail.clone().fst()));
        state.scope.aliases.insert(name.clone(), fresh);
        tail = tail.snd();
    }
    (state, bindings)
}

pub(super) fn lets(bindings: &[(String, E, E)], mut body: E) -> E {
    for (name, ty, value) in bindings.iter().rev() {
        body = E::let_in(name, Some(ty.clone()), value.clone(), body);
    }
    body
}
