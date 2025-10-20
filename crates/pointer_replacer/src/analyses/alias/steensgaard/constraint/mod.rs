pub mod generation;
pub mod watcher;

pub type Constraint =
    crate::analyses::alias::constraint::Constraint<super::location::AbstractLocation>;
