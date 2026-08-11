//! **Type-directed seam adapters** at mismatched argument positions.
//!
//! S3.6-1 converts a callee's parameter and the caller's binding *jointly* where
//! the co-conversion class links them. Where the class graph has no edge, the
//! two ends convert independently and the argument position is left ill-typed —
//! measured at 2,950 positions, **100 % `E0308`**, which is the whole of the
//! 95.7 % revert load.
//!
//! A seam adapter is one expression of glue at that position, bridging the form
//! the caller supplies to the form the callee now expects.
//!
//! # Two families, and the exposure the reborrow one carries
//!
//! - **Safe** — `Some(x)`, `x.unwrap()`, `slice::from_mut/from_ref`, `&mut x[0]`
//!   and their compositions. No `unsafe`, compiler-checked end to end.
//! - **Reborrow** — `&mut *p` / `&*p`. One expression, borrow scoped to the
//!   call.
//!
//! **The reborrow family is placed exactly where the compiler stops checking
//! aliasing** (`-1` micro-plan §5a, the inversion finding): `two_mut(&mut v,
//! &mut v)` on a real local is `E0499`, but through a raw base it compiles with
//! zero diagnostics. That is why the site gates — `duplicate-place-root` and P2
//! `BlindOnly` — apply to adapter-generated arguments **exactly as to converted
//! ones**, with no bypass. A gate that skipped glue would move the argument from
//! the checked region into the unchecked one and book it as yield.
//!
//! # Slice seams are length-gated, and no length is ever fabricated
//!
//! `*mut T → &[T]` needs a length. `slice::from_raw_parts` with an oversized
//! `len` is **UB at construction** by its own safety contract — not on first
//! out-of-bounds read — so a guessed constant is unsound the moment it is built.
//! Those positions gate under [`SeamBlock::LengthUnknown`] until a length source
//! is proven. **65.7 % of the measured market sits behind that gate**, which is
//! why it is a first-class outcome here rather than a `None`.

use rustc_span::Span;

/// The pointer-ish form a value has at an argument position.
///
/// `Raw` carries no mutability: the glue's mutability follows the **expected**
/// side. `&*p` is well-formed on a `*mut T` and `&mut *p` is not obtainable from
/// a `*const T` at all, so reading the raw side's constness would only let a
/// caller ask for something the callee's own converted type already forbids.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Form {
    Raw,
    Ref { mutable: bool },
    Slice { mutable: bool },
    Opt { mutable: bool, slice: bool },
}

/// Why a position could not be adapted. **A first-class outcome**, never a
/// silent skip — an unadapted position is a revert, and a revert with no reason
/// is a yield number nobody can attribute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SeamBlock {
    /// A slice form is expected and the argument is raw: a length is needed and
    /// **none may be invented**. Ruling item 4.
    LengthUnknown,
    /// `&mut T` expected, a shared borrow supplied. Not upgradable.
    SharedToMut,
    /// The argument's expression is not one this slice can name — a bare cast, a
    /// null literal, a call result, arithmetic.
    UnnameableOperand,
}

impl SeamBlock {
    pub(crate) fn key(self) -> &'static str {
        match self {
            SeamBlock::LengthUnknown => "seam-len-unknown",
            SeamBlock::SharedToMut => "seam-shared-to-mut",
            SeamBlock::UnnameableOperand => "seam-unnameable-operand",
        }
    }
}

/// Which family a placed adapter came from. Reported in the artifacts' seam
/// column so the reborrow population — the one carrying the aliasing exposure —
/// stays countable on its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SeamFamily {
    Safe,
    Reborrow,
}

/// One placed adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SeamEdit {
    /// The **argument expression's** span, in the CALLER's file.
    pub span: Span,
    pub replacement: String,
    /// The callee subject whose conversion justifies this edit — the revert key.
    /// The edit lands in the caller's file and is owned by the callee, which is
    /// the divergence `plan`'s `owner_fn` doc was written for.
    pub owner_fn: String,
    pub family: SeamFamily,
}

/// `&mut ` or `&`.
fn amp(mutable: bool) -> &'static str {
    if mutable { "&mut " } else { "&" }
}

/// Unwrap an optional **without consuming it**.
///
/// `Option<&T>` is `Copy`, so a plain `.unwrap()` leaves the binding usable.
/// **`Option<&mut T>` is not**, and `.unwrap()` MOVES it — a caller that passes
/// the same optional to two calls would compile before the rewrite and fail
/// `E0382` after, which is a rewrite that breaks a working program.
///
/// `.as_mut().unwrap()` yields `&mut &mut T`, which deref-coerces to `&mut T` at
/// the argument position and borrows rather than moves.
///
/// **Compile-verified on the pinned toolchain, twice-in-one-body**, because the
/// single-use spelling passes and the defect only appears on the second use.
/// The moving form was written first and caught by compiling, not by review.
fn unwrap_expr(text: &str, mutable: bool) -> String {
    if mutable {
        format!("{text}.as_mut().unwrap()")
    } else {
        format!("{text}.unwrap()")
    }
}

/// The glue that turns a value of `found` into one of `expected`.
///
/// - `Ok(None)` — the forms already agree, or coerce. **No edit.**
/// - `Ok(Some(text))` — the adapter expression.
/// - `Err(block)` — this position cannot be adapted, with its reason.
///
/// `text` is the argument's own source, already peeled of any cast the caller
/// resolved, and is substituted verbatim: the seam never re-renders an
/// expression it did not author.
pub(crate) fn glue(
    expected: Form,
    found: Form,
    text: &str,
) -> Result<Option<(String, SeamFamily)>, SeamBlock> {
    use Form::*;
    // A shared borrow can never satisfy a `&mut` position, whatever the shapes
    // either side. Checked first so every arm below may assume mutability is
    // obtainable.
    let shared_to_mut = |want: bool, have: bool| want && !have;

    Ok(match (expected, found) {
        // ---- identities and coercions: no edit ----
        (Ref { mutable: w }, Ref { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            None // `&mut T` coerces to `&T`
        }
        (Slice { mutable: w }, Slice { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            None
        }
        (
            Opt {
                mutable: w,
                slice: ws,
            },
            Opt {
                mutable: h,
                slice: hs,
            },
        ) if ws == hs => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            None
        }

        // ---- reborrow family: a raw base becomes a reference ----
        (Ref { mutable }, Raw) => Some((format!("{}*{text}", amp(mutable)), SeamFamily::Reborrow)),
        (
            Opt {
                mutable,
                slice: false,
            },
            Raw,
        ) => Some((
            format!("Some({}*{text})", amp(mutable)),
            SeamFamily::Reborrow,
        )),

        // ---- slice seams: LENGTH-GATED, never fabricated ----
        (Slice { .. }, Raw) | (Opt { slice: true, .. }, Raw) => {
            return Err(SeamBlock::LengthUnknown);
        }

        // ---- safe family ----
        (Slice { mutable: w }, Ref { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            // `from_ref` accepts a `&mut T` by coercion, which is what makes the
            // measured `&mut T → &[T]` row (30 positions) a safe one rather than
            // a gap.
            let ctor = if w { "from_mut" } else { "from_ref" };
            Some((format!("core::slice::{ctor}({text})"), SeamFamily::Safe))
        }
        (Ref { mutable: w }, Slice { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((format!("{}{text}[0]", amp(w)), SeamFamily::Safe))
        }
        (
            Opt {
                mutable: w,
                slice: false,
            },
            Ref { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((format!("Some({text})"), SeamFamily::Safe))
        }
        (
            Opt {
                mutable: w,
                slice: true,
            },
            Ref { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            let ctor = if w { "from_mut" } else { "from_ref" };
            Some((
                format!("Some(core::slice::{ctor}({text}))"),
                SeamFamily::Safe,
            ))
        }
        (
            Opt {
                mutable: w,
                slice: false,
            },
            Slice { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((format!("Some({}{text}[0])", amp(w)), SeamFamily::Safe))
        }
        // The FAT twin of the arm above: the slice is already the payload, so
        // this is a bare wrap. Found by the exhaustiveness guard rather than by
        // enumeration — the arms were written from the measured census, and the
        // census has no `Slice → Option<&[T]>` row because nothing has reached
        // that position yet.
        (
            Opt {
                mutable: w,
                slice: true,
            },
            Slice { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((format!("Some({text})"), SeamFamily::Safe))
        }

        // ---- the null-panic convention (-3), inherited rather than reinvented ----
        //
        // `-3` settled that an optional subject's null case PANICS rather than
        // being silently dropped. `.unwrap()` is that same contract at the seam,
        // and citing it is the point: a seam that chose its own null behaviour
        // would give one program two answers to the same question.
        (Ref { mutable: w }, Opt { mutable: h, slice }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            let inner = unwrap_expr(text, h);
            Some(if slice {
                (format!("{}{inner}[0]", amp(w)), SeamFamily::Safe)
            } else {
                (inner, SeamFamily::Safe)
            })
        }
        (Slice { mutable: w }, Opt { mutable: h, slice }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            let inner = unwrap_expr(text, h);
            Some(if slice {
                (inner, SeamFamily::Safe)
            } else {
                let ctor = if w { "from_mut" } else { "from_ref" };
                (format!("core::slice::{ctor}({inner})"), SeamFamily::Safe)
            })
        }
        (
            Opt {
                mutable: w,
                slice: ws,
            },
            Opt { mutable: h, .. },
        ) => {
            // Differing fat/thin twins: unwrap, adjust, re-wrap.
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            let inner = unwrap_expr(text, h);
            Some(if ws {
                let ctor = if w { "from_mut" } else { "from_ref" };
                (
                    format!("Some(core::slice::{ctor}({inner}))"),
                    SeamFamily::Safe,
                )
            } else {
                (format!("Some({}{inner}[0])", amp(w)), SeamFamily::Safe)
            })
        }

        // A raw position needs no adapter: `&mut T` coerces to `*mut T` at a
        // call. Measured, and it is why E3b predicts no counter movement here.
        (Raw, _) => None,
    })
}

#[cfg(test)]
mod tests {
    use Form::*;

    use super::*;

    const T: &str = "p";

    fn g(expected: Form, found: Form) -> Result<Option<(String, SeamFamily)>, SeamBlock> {
        glue(expected, found, T)
    }

    fn text(expected: Form, found: Form) -> String {
        g(expected, found)
            .unwrap_or_else(|b| panic!("blocked: {b:?}"))
            .unwrap_or_else(|| panic!("no edit"))
            .0
    }

    /// **Reborrow, BOTH SIDES.** `*mut T → &mut T` needs glue; the reverse needs
    /// none, because a reference coerces to a raw pointer at a call.
    ///
    /// A witness on one direction witnesses half a table: an implementation that
    /// emitted `&mut *p` in *both* directions would pass a one-sided test and
    /// produce `&mut *(&mut x)` at every raw position.
    #[test]
    fn reborrow_is_directional() {
        assert_eq!(text(Ref { mutable: true }, Raw), "&mut *p");
        assert_eq!(text(Ref { mutable: false }, Raw), "&*p");
        assert_eq!(g(Raw, Ref { mutable: true }), Ok(None), "reverse: coercion");
        assert_eq!(g(Raw, Slice { mutable: true }), Ok(None));
    }

    /// **Optional, BOTH SIDES.** `Some(..)` one way, `.unwrap()` the other —
    /// the latter on `-3`'s null-panic convention.
    #[test]
    fn optional_wraps_one_way_and_unwraps_the_other() {
        assert_eq!(
            text(
                Opt {
                    mutable: true,
                    slice: false
                },
                Ref { mutable: true }
            ),
            "Some(p)"
        );
        assert_eq!(
            text(
                Ref { mutable: true },
                Opt {
                    mutable: true,
                    slice: false
                }
            ),
            "p.as_mut().unwrap()",
            "a MUTABLE optional must not be CONSUMED by the seam"
        );
        // The shared twin IS `Copy`, so the plain spelling is correct there and
        // the two must not be unified — `.as_mut()` on a `&T` optional would
        // need a `mut` binding the caller may not have.
        assert_eq!(
            text(
                Ref { mutable: false },
                Opt {
                    mutable: false,
                    slice: false
                }
            ),
            "p.unwrap()"
        );
    }

    /// **Optional over a raw base composes both families**, and the composition
    /// is `Some(&mut *p)` — not `&mut *Some(p)`, which does not parse as a
    /// pointer operation at all.
    #[test]
    fn optional_over_raw_composes_reborrow_inside_some() {
        let (t, fam) = g(
            Opt {
                mutable: true,
                slice: false,
            },
            Raw,
        )
        .unwrap()
        .unwrap();
        assert_eq!(t, "Some(&mut *p)");
        assert_eq!(fam, SeamFamily::Reborrow, "the raw base carries the family");
    }

    /// **Slice, BOTH SIDES**, and the measured table amendment.
    ///
    /// `&mut T → &[T]` (30 positions) is SAFE: `from_ref` takes a `&mut T` by
    /// coercion. The census found it; the ratified table did not have it.
    #[test]
    fn slice_construction_and_projection_are_both_safe() {
        assert_eq!(
            text(Slice { mutable: true }, Ref { mutable: true }),
            "core::slice::from_mut(p)"
        );
        assert_eq!(
            text(Slice { mutable: false }, Ref { mutable: false }),
            "core::slice::from_ref(p)"
        );
        // THE AMENDMENT: shared slice expected, mutable reference supplied.
        assert_eq!(
            text(Slice { mutable: false }, Ref { mutable: true }),
            "core::slice::from_ref(p)"
        );
        // The reverse projection.
        assert_eq!(
            text(Ref { mutable: true }, Slice { mutable: true }),
            "&mut p[0]"
        );
        assert_eq!(
            text(Ref { mutable: false }, Slice { mutable: false }),
            "&p[0]"
        );
    }

    /// **The length gate — 65.7 % of the measured market.**
    ///
    /// Every raw→slice direction blocks, thin and fat alike. No constant is ever
    /// produced: `from_raw_parts` with an oversized `len` is UB at construction,
    /// so a fabricated length is unsound the moment it is built.
    #[test]
    fn every_raw_to_slice_direction_is_length_gated() {
        for expected in [
            Slice { mutable: true },
            Slice { mutable: false },
            Opt {
                mutable: true,
                slice: true,
            },
            Opt {
                mutable: false,
                slice: true,
            },
        ] {
            assert_eq!(
                g(expected, Raw),
                Err(SeamBlock::LengthUnknown),
                "raw → {expected:?} must gate, never fabricate a length"
            );
        }
    }

    /// **A shared borrow never satisfies a `&mut` position**, in every pair that
    /// can express the mismatch.
    ///
    /// *Mutation-tested:* drop the `shared_to_mut` guard from any arm and the
    /// corresponding row here fails — the glue would compile-fail at `E0596`
    /// instead of degrading with a reason, turning an attributable gate into a
    /// revert.
    #[test]
    fn a_shared_borrow_never_satisfies_a_mut_position() {
        let shared = Ref { mutable: false };
        for expected in [
            Ref { mutable: true },
            Slice { mutable: true },
            Opt {
                mutable: true,
                slice: false,
            },
            Opt {
                mutable: true,
                slice: true,
            },
        ] {
            assert_eq!(
                g(expected, shared),
                Err(SeamBlock::SharedToMut),
                "{expected:?} from a shared borrow must gate"
            );
        }
        // ... and the same-form case, which has its own arm.
        assert_eq!(
            g(Slice { mutable: true }, Slice { mutable: false }),
            Err(SeamBlock::SharedToMut)
        );
    }

    /// Matching forms produce **no edit at all** — the 58.6 % of positions §4
    /// measured as needing no caller-side text.
    #[test]
    fn matching_forms_need_no_edit() {
        for f in [
            Ref { mutable: true },
            Slice { mutable: false },
            Opt {
                mutable: true,
                slice: false,
            },
        ] {
            assert_eq!(g(f, f), Ok(None), "{f:?} against itself must need no glue");
        }
        // `&mut T` supplied where `&T` is wanted: coercion, still no edit.
        assert_eq!(g(Ref { mutable: false }, Ref { mutable: true }), Ok(None));
    }
}
