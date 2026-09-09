//! Independent cursor preparation. Not registered in the production decision
//! module until the W3B integration gate. These leaf operations do not admit
//! analysis slots or establish reference formation/aliasing evidence.

#[path = "cursor/index.rs"]
pub(crate) mod index;

#[path = "cursor/carrier.rs"]
pub(crate) mod carrier;

#[path = "cursor/transaction.rs"]
pub(crate) mod transaction;
