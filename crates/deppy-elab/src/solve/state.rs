use super::*;

#[derive(Clone)]
pub(crate) struct Local {
    pub(super) id: Id,
    pub(super) name: String,
    pub(super) ty: T,
    pub(super) value: Option<T>,
}

pub(crate) type Context = Vec<Local>;

#[derive(Clone)]
pub(super) struct Meta {
    pub(super) telescope: Context,
    pub(super) expected: T,
    pub(super) solution: Option<T>,
}

pub(crate) struct State {
    pub(super) user_goals: Vec<(usize, String, Option<crate::SourceLocation>, Context, T)>,
    pub(super) location: Option<crate::SourceLocation>,
    pub(super) kernel: Kernel,
    pub(crate) globals: HashMap<String, deppy_core::DefId>,
    pub(crate) records: HashMap<deppy_core::InductiveId, crate::Record>,
    pub(super) next_id: Id,
    pub(super) remaining: usize,
    pub(super) metas: Vec<Meta>,
}

impl State {
    pub(crate) fn new(remaining: usize) -> Self {
        Self {
            user_goals: Vec::new(),
            location: None,
            kernel: Kernel::new(remaining),
            globals: HashMap::new(),
            records: HashMap::new(),
            next_id: 0,
            remaining,
            metas: vec![],
        }
    }

    pub(crate) fn with_kernel(remaining: usize, kernel: Kernel) -> Self {
        Self {
            kernel,
            ..Self::new(remaining)
        }
    }

    pub(super) fn tick(&mut self) -> Result<(), Error> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Error::BudgetExceeded)?;
        Ok(())
    }

    pub(super) fn fresh(&mut self) -> Id {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    pub(super) fn meta(&mut self, ctx: &Context, expected: T) -> T {
        let id = self.metas.len();
        self.metas.push(Meta {
            telescope: ctx.iter().filter(|x| x.value.is_none()).cloned().collect(),
            expected,
            solution: None,
        });
        Term::Meta(
            id,
            ctx.iter()
                .filter(|x| x.value.is_none())
                .map(|x| Term::Local(x.id).arc())
                .collect(),
        )
        .arc()
    }

    pub(super) fn bind(&mut self, ctx: &Context, name: &str, ty: T) -> (Context, Id) {
        let id = self.fresh();
        let mut ctx = ctx.clone();
        ctx.push(Local {
            id,
            name: name.to_owned(),
            ty,
            value: None,
        });
        (ctx, id)
    }
}

pub(super) fn display_name(name: &str) -> String {
    if name.starts_with('\0') {
        name.split_once(':')
            .map(|(_, original)| original.to_owned())
            .unwrap_or_else(|| name.trim_start_matches('\0').to_owned())
    } else {
        name.to_owned()
    }
}

impl State {
    pub(super) fn describe(&self, term: &T, ctx: &Context) -> String {
        let show = |t: &T| self.describe(t, ctx);
        match term.as_ref() {
            Term::Local(id) => ctx
                .iter()
                .find(|l| l.id == *id)
                .map(|l| display_name(&l.name))
                .unwrap_or_else(|| format!("v{id}")),
            Term::Global(id) => self
                .globals
                .iter()
                .find(|(_, value)| **value == *id)
                .map(|(name, _)| name.clone())
                .unwrap_or_else(|| format!("global#{id}")),
            Term::Universe(0) => "Type".into(),
            Term::Universe(n) => format!("Type[{n}]"),
            Term::Nat => "Nat".into(),
            Term::Zero => "0".into(),
            Term::Succ(n) => format!("S({})", show(n)),
            Term::Eq { ty, left, right } => {
                format!("Eq[{}, {}, {}]", show(ty), show(left), show(right))
            }
            Term::Vec { ty, len } => format!("Vec[{}, {}]", show(ty), show(len)),
            Term::Fin { bound } => format!("Fin[{}]", show(bound)),
            Term::App(f, a) => format!("{}({})", show(f), show(a)),
            Term::Meta(id, _) => format!("?{id}"),
            Term::Pi {
                id, domain, body, ..
            } => format!("(v{id}: {}) -> {}", show(domain), show(body)),
            Term::Sigma { id, domain, body } => {
                format!("Sigma(v{id}: {}, {})", show(domain), show(body))
            }
            _ => format!("{term:?}"),
        }
    }
}
