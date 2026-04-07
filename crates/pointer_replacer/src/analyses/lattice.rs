// SmallVec lattice impls removed to avoid requiring const_smallvec support.

pub trait Lattice: Eq + HasBottom + HasTop {
    #[allow(unused)]
    fn join(&mut self, other: &Self) -> bool;
    #[allow(unused)]
    fn meet(&mut self, other: &Self) -> bool;
}

pub trait HasBottom {
    const BOTTOM: Self;
}

pub trait HasTop {
    const TOP: Self;
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[allow(unused)]
pub enum FlatSet<T> {
    Bottom,
    Elem(T),
    Top,
}

impl<T> HasBottom for FlatSet<T> {
    const BOTTOM: Self = FlatSet::Bottom;
}

impl<T> HasTop for FlatSet<T> {
    const TOP: Self = FlatSet::Top;
}

impl<T> Lattice for FlatSet<T>
where T: Clone + Copy + Eq
{
    fn meet(&mut self, other: &Self) -> bool {
        let result = match (&*self, other) {
            (Self::Bottom, _) | (_, Self::Top) => return false,
            (Self::Elem(a), Self::Elem(b)) if a == b => return false,

            (Self::Top, Self::Elem(x)) => Self::Elem(*x),

            _ => Self::Bottom,
        };

        *self = result;
        true
    }

    fn join(&mut self, other: &Self) -> bool {
        let result = match (&*self, other) {
            (Self::Top, _) | (_, Self::Bottom) => return false,
            (Self::Elem(a), Self::Elem(b)) if a == b => return false,

            (Self::Bottom, Self::Elem(x)) => Self::Elem(*x),

            _ => Self::Top,
        };

        *self = result;
        true
    }
}

impl HasBottom for bool {
    const BOTTOM: Self = false;
}

impl HasTop for bool {
    const TOP: Self = true;
}

impl Lattice for bool {
    fn join(&mut self, other: &Self) -> bool {
        if let (false, true) = (*self, *other) {
            *self = true;
            return true;
        }

        false
    }

    fn meet(&mut self, other: &Self) -> bool {
        if let (true, false) = (*self, *other) {
            *self = false;
            return true;
        }

        false
    }
}
