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
