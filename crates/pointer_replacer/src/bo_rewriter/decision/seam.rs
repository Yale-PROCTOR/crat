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
    /// Two positions at one call site may borrow the same place, and at least
    /// one wants `&mut`. **The gate applies to adapter-generated arguments
    /// exactly as to converted ones** (ruling item 3, 2026-08-11): glue may not
    /// bypass it, because the reborrow family places its borrow precisely where
    /// §5a measured borrowck as blind.
    SiteOverlap,
}

impl SeamBlock {
    pub(crate) fn key(self) -> &'static str {
        match self {
            SeamBlock::LengthUnknown => "seam-len-unknown",
            SeamBlock::SharedToMut => "seam-shared-to-mut",
            SeamBlock::UnnameableOperand => "seam-unnameable-operand",
            SeamBlock::SiteOverlap => "seam-site-overlap",
        }
    }
}

/// What the callee's own signature says about a companion length.
///
/// Measured on the SIGNATURE rather than the call site, because the C idiom
/// this is looking for — `void f(int *buf, size_t len)` — is a property of the
/// declaration: every caller of such a function supplies the length in the same
/// position, so the signature answers for all of them at once.
///
/// **Adjacency is evidence, not proof.** `f(dst, src, n)` has an integer in the
/// position after `src` that is the length of BOTH pointers, and `f(p, flags)`
/// has one that is a length of nothing. This enum records what was seen; it
/// does not certify a length, and no seam is placed from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LenEvidence {
    /// An integer-typed parameter immediately AFTER the pointer — the dominant
    /// C spelling.
    Following,
    /// An integer-typed parameter immediately BEFORE it.
    Preceding,
    /// An integer parameter exists somewhere in the signature, but not adjacent.
    Elsewhere,
    /// The signature carries no integer parameter at all. **A length cannot come
    /// from the call site**, so such a position can only ever be served by
    /// certified `approx-len` (U-2') or stay gated.
    None,
}

impl LenEvidence {
    pub(crate) fn key(self) -> &'static str {
        match self {
            LenEvidence::Following => "len-following",
            LenEvidence::Preceding => "len-preceding",
            LenEvidence::Elsewhere => "len-elsewhere",
            LenEvidence::None => "len-absent",
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
    /// **Which adjacency arm licensed this slice seam's length** (ruling B,
    /// 2026-08-11). `None` for every non-slice seam, which needs no length.
    ///
    /// Carried NOW rather than added when the bound-verification follow-up runs:
    /// that check certifies or corrects each selection, and it can only be
    /// surgical if it can tell a `following` selection from a `preceding` one
    /// without re-deriving the choice.
    pub len_arm: Option<LenEvidence>,
    /// **The adapter, DESCRIBED** — option A's carried interface (2026-08-13).
    ///
    /// [`Self::replacement`] is `spec.render(<the argument's source text>)`, so
    /// the two are redundant *by construction* and the span layer keeps reading
    /// the string. The AST layer reads this instead, because it cannot rebuild a
    /// wrapper from a rendered string without re-parsing the argument it was
    /// told to keep as a subtree.
    pub spec: GlueSpec,
    /// **The span whose TEXT the replacement was built from** — which is NOT
    /// always [`Self::span`].
    ///
    /// `span` is the whole argument and is what the span layer overwrites. For
    /// the two cast shapes (`AddrOfCast`, `CastOfLocal`) the decision layer
    /// builds the replacement from the cast's OPERAND (`ArgShape`'s `inner`),
    /// so the surviving subtree is nested one level inside the replaced node.
    ///
    /// Carried rather than re-derived: an AST layer that peeled casts by
    /// pattern would be guessing at exactly the point where the span layer
    /// already knows, and a `Paren` between the cast and its operand would make
    /// the guess silently wrong.
    pub arg_span: Span,
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

/// **THE GLUE SPEC — the reification ruled at the arm-3 boundary (2026-08-13).**
///
/// Glue used to be manufactured as TEXT here and consumed as text downstream.
/// The AST application layer cannot build a node from a rendered string without
/// re-parsing the argument it was told to keep as a subtree — the round-trip
/// arm 1 declined — so the shape the decision layer already knew is now
/// CARRIED rather than re-derived.
///
/// **Reification only.** No decision, gate, family or position-walk change: the
/// spec is computed at exactly the sites that already computed the string, and
/// [`GlueSpec::render`] reproduces that string byte-for-byte. That equality is
/// GATED, not asserted — see `render_is_byte_identical_to_the_frozen_glue_text`.
///
/// The dependency arrow runs application→decision: this type lives here, and
/// the AST layer consumes it. The import denylist is untouched.
///
/// Every arm of [`glue`] is one point in a small algebra —
/// `[Some(] core([unwrap(] text [)]) [)]` — which is why five cores suffice for
/// all fourteen emitting arms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum GlueCore {
    /// `X` — the argument unchanged (the payload already fits).
    Bare,
    /// `&mut *X` / `&*X`
    Reborrow,
    /// `&mut X[0]` / `&X[0]`
    Index0,
    /// `core::slice::from_raw_parts{_mut}(X, (LEN) as usize)`
    FromRawParts,
    /// `core::slice::from_mut(X)` / `core::slice::from_ref(X)`
    FromRefMut,
}

/// One adapter, described rather than rendered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GlueSpec {
    pub core: GlueCore,
    /// The EXPECTED side's mutability — selects `&`/`&mut` and
    /// `from_ref`/`from_mut`.
    pub mutable: bool,
    /// The unwrap that precedes the core when the FOUND side is optional.
    /// `Some(true)` is `.as_mut().unwrap()`, `Some(false)` is `.unwrap()` —
    /// the distinction `unwrap_expr` exists for, carried rather than inferred.
    pub unwrap: Option<bool>,
    /// The length's source text, `FromRawParts` only.
    ///
    /// **Still `None`-means-refused**: the seam never invents a length, and the
    /// held fabricated-length slice inserts HERE rather than at a string
    /// substitution.
    pub len: Option<String>,
    /// Wrap the result in `Some(...)`.
    pub optional: bool,
}

impl GlueSpec {
    pub(crate) fn core(core: GlueCore, mutable: bool) -> Self {
        Self {
            core,
            mutable,
            unwrap: None,
            len: None,
            optional: false,
        }
    }

    pub(crate) fn with_unwrap(mut self, found_mutable: bool) -> Self {
        self.unwrap = Some(found_mutable);
        self
    }

    pub(crate) fn with_len(mut self, len: &str) -> Self {
        self.len = Some(len.to_owned());
        self
    }

    pub(crate) fn wrapped(mut self) -> Self {
        self.optional = true;
        self
    }

    /// **The census's `glue_shape`, CARRIED rather than inferred** — condition 5
    /// of the option-A ruling.
    ///
    /// `seam_tsv` used to recover the shape by testing PREFIXES of the rendered
    /// replacement. Same column, same ten-word vocabulary, strictly better
    /// provenance — but it IS a schema semantics change, because the prefix test
    /// reads a string the argument's own text contributes to and this reads the
    /// decision.
    ///
    /// **Two inherited quirks are reproduced deliberately, not repaired here.**
    /// The classifier tested `.contains(".unwrap()")` BEFORE the `Some(` tests,
    /// so an unwrap under a wrapper reported `unwrap`/`as_mut_unwrap` rather
    /// than the wrapper's shape; and `Some(&X[0])` fell through the
    /// `Some(&mut *`/`Some(&*` test to `some_wrap`. Both are kept so this
    /// function is provably zero-delta wherever the classifier was right, and
    /// the places it was NOT right are the measured movement rather than a
    /// change of vocabulary mixed in with it.
    pub(crate) fn shape_key(&self) -> &'static str {
        if let Some(found_mutable) = self.unwrap {
            return if found_mutable {
                "as_mut_unwrap"
            } else {
                "unwrap"
            };
        }
        match (self.optional, &self.core) {
            (true, GlueCore::FromRawParts) => "some_from_raw_parts",
            (true, GlueCore::Reborrow) => "some_reborrow",
            (true, GlueCore::FromRefMut) => "some_from_ref_mut",
            // `Some(&X[0])` matches neither `Some(&mut *` nor `Some(&*`.
            (true, GlueCore::Bare | GlueCore::Index0) => "some_wrap",
            (false, GlueCore::FromRawParts) => "from_raw_parts",
            (false, GlueCore::Reborrow) => "reborrow",
            (false, GlueCore::FromRefMut) => "from_ref_mut",
            // `index` is the classifier's FALLBACK arm, and the two cores that
            // land in it are **not** in the same position — a distinction this
            // comment previously got wrong, in the direction this track calls
            // its founding failure class.
            //
            // - `Index0` here is REACHABLE and REAL: `glue`'s `(Ref, Slice)`
            //   arm builds exactly `core(Index0, w)` with no unwrap and no
            //   wrapper, rendering `&w X[0]`, which the retired classifier fell
            //   through to `index`. It is corpus-ZERO on the frozen corpus, and
            //   corpus-zero is not unreachable.
            // - `Bare` here is genuinely unreachable: with neither an unwrap
            //   nor a wrapper it renders the argument unchanged, and `glue`
            //   returns `Ok(None)` for every pairing that would need it.
            //
            // Both are matched together because the classifier gave both the
            // same answer; only the reachability claim differed.
            (false, GlueCore::Bare | GlueCore::Index0) => "index",
        }
    }

    /// Render the spec as the span layer's text. **Byte-identical to the
    /// pre-reification `format!` set, and gated as such.**
    ///
    /// `None` when a length-bearing core carries no length. **This used to
    /// substitute an empty string**, printing
    /// `core::slice::from_raw_parts(p, () as usize)` — not merely invalid Rust
    /// but a *silent length substitution*, in the one place this milestone's
    /// hardest invariant says none may ever happen, while [`Self::len`]'s own
    /// doc promised `None`-means-refused. Prose asserting a check the code did
    /// not have, on the exact socket the HELD fabricated-length slice is
    /// designed to plug into. The AST builder already refused this input and
    /// counted it (`len_absent`); the renderer did not. Found by the
    /// adversarial review.
    ///
    /// Unreachable through [`glue`], which returns [`SeamBlock::LengthUnknown`]
    /// first — so this is fail-closed structure rather than a live path, and it
    /// moves no corpus line.
    pub(crate) fn render(&self, text: &str) -> Option<String> {
        let base = match self.unwrap {
            None => text.to_owned(),
            Some(found_mutable) => unwrap_expr(text, found_mutable),
        };
        let inner = match self.core {
            GlueCore::Bare => base,
            GlueCore::Reborrow => format!("{}*{base}", amp(self.mutable)),
            GlueCore::Index0 => format!("{}{base}[0]", amp(self.mutable)),
            GlueCore::FromRawParts => {
                let ctor = if self.mutable {
                    "from_raw_parts_mut"
                } else {
                    "from_raw_parts"
                };
                let len = self.len.as_deref()?;
                format!("core::slice::{ctor}({base}, ({len}) as usize)")
            }
            GlueCore::FromRefMut => {
                let ctor = if self.mutable { "from_mut" } else { "from_ref" };
                format!("core::slice::{ctor}({base})")
            }
        };
        Some(if self.optional {
            format!("Some({inner})")
        } else {
            inner
        })
    }
}

/// The glue that turns a value of `found` into one of `expected`.
///
/// - `Ok(None)` — the forms already agree, or coerce. **No edit.**
/// - `Ok(Some(spec))` — the adapter, DESCRIBED.
/// - `Err(block)` — this position cannot be adapted, with its reason.
///
/// # Half 2 of the option-A reification (2026-08-13)
///
/// Every arm used to `format!` its answer over the argument's source text.
/// It now names a [`GlueSpec`], and the caller renders that spec over the same
/// text — so `spec.render(text)` is the string this function used to return,
/// **byte for byte**, and the argument no longer reaches this function at all.
///
/// That the text is not a parameter here is the substance of the change rather
/// than a tidy-up: an adapter is a shape, the argument is a subtree, and the
/// AST layer needs the first without being handed a rendering of the second.
///
/// **Reification only** — no arm's `(expected, found)` pattern, guard, family
/// or `Err` moved. Each `format!` became the spec that renders to it.
pub(crate) fn glue(
    expected: Form,
    found: Form,
    len: Option<&str>,
) -> Result<Option<(GlueSpec, SeamFamily)>, SeamBlock> {
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
        (Ref { mutable }, Raw) => Some((
            GlueSpec::core(GlueCore::Reborrow, mutable),
            SeamFamily::Reborrow,
        )),
        (
            Opt {
                mutable,
                slice: false,
            },
            Raw,
        ) => Some((
            GlueSpec::core(GlueCore::Reborrow, mutable).wrapped(),
            SeamFamily::Reborrow,
        )),

        // ---- slice seams: a length from the CALL SITE, or gated ----
        //
        // Ruling B (2026-08-11): both adjacency arms license the companion
        // argument as the length. `len` is that argument's own source text,
        // substituted verbatim and cast — the seam never invents a length, and
        // `None` here still gates rather than guessing (ruling item 4 stands).
        //
        // `as usize` unconditionally: the C spelling is `size_t`, `c_int` or
        // `c_ulong` depending on the header, and `from_raw_parts` takes `usize`.
        // Parenthesised because the companion may be an arbitrary expression.
        (Slice { mutable }, Raw) => {
            let Some(len) = len else {
                return Err(SeamBlock::LengthUnknown);
            };
            Some((
                GlueSpec::core(GlueCore::FromRawParts, mutable).with_len(len),
                SeamFamily::Reborrow,
            ))
        }
        (
            Opt {
                mutable,
                slice: true,
            },
            Raw,
        ) => {
            let Some(len) = len else {
                return Err(SeamBlock::LengthUnknown);
            };
            Some((
                GlueSpec::core(GlueCore::FromRawParts, mutable)
                    .with_len(len)
                    .wrapped(),
                SeamFamily::Reborrow,
            ))
        }

        // ---- safe family ----
        (Slice { mutable: w }, Ref { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            // `from_ref` accepts a `&mut T` by coercion, which is what makes the
            // measured `&mut T → &[T]` row (30 positions) a safe one rather than
            // a gap.
            Some((GlueSpec::core(GlueCore::FromRefMut, w), SeamFamily::Safe))
        }
        (Ref { mutable: w }, Slice { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((GlueSpec::core(GlueCore::Index0, w), SeamFamily::Safe))
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
            Some((
                GlueSpec::core(GlueCore::Bare, w).wrapped(),
                SeamFamily::Safe,
            ))
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
            Some((
                GlueSpec::core(GlueCore::FromRefMut, w).wrapped(),
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
            Some((
                GlueSpec::core(GlueCore::Index0, w).wrapped(),
                SeamFamily::Safe,
            ))
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
            Some((
                GlueSpec::core(GlueCore::Bare, w).wrapped(),
                SeamFamily::Safe,
            ))
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
            let core = if slice {
                GlueCore::Index0
            } else {
                GlueCore::Bare
            };
            Some((GlueSpec::core(core, w).with_unwrap(h), SeamFamily::Safe))
        }
        (Slice { mutable: w }, Opt { mutable: h, slice }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            let core = if slice {
                GlueCore::Bare
            } else {
                GlueCore::FromRefMut
            };
            Some((GlueSpec::core(core, w).with_unwrap(h), SeamFamily::Safe))
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
            let core = if ws {
                GlueCore::FromRefMut
            } else {
                GlueCore::Index0
            };
            Some((
                GlueSpec::core(core, w).with_unwrap(h).wrapped(),
                SeamFamily::Safe,
            ))
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

    /// **THE RENDERER PARITY ORACLE — every emitting arm of [`glue`], by hand.**
    ///
    /// Condition 2 of the option-A ruling: spec + renderer must reproduce
    /// today's text byte-identically. This pins the RENDERER half of that gate
    /// now, before any arm is converted, so the conversion lands against a
    /// fixed target rather than co-evolving with it.
    ///
    /// Each row is `(spec, expected text)` transcribed from the corresponding
    /// `format!` in `glue`. The algebra is `[Some(] core([unwrap(] X [)]) [)]`,
    /// and these fourteen rows are every composition `glue` can emit.
    ///
    /// *Mutation-tested:* dropping the parens in the `FromRawParts` cast, or
    /// swapping `from_ref`/`from_mut`, fails here.
    #[test]
    fn render_reproduces_every_emitting_glue_arm_byte_for_byte() {
        let cases: Vec<(GlueSpec, &str)> = vec![
            // (Ref, Raw) and its optional twin
            (GlueSpec::core(GlueCore::Reborrow, true), "&mut *p"),
            (GlueSpec::core(GlueCore::Reborrow, false), "&*p"),
            (
                GlueSpec::core(GlueCore::Reborrow, true).wrapped(),
                "Some(&mut *p)",
            ),
            // (Slice, Raw) and its optional twin
            (
                GlueSpec::core(GlueCore::FromRawParts, true).with_len("n"),
                "core::slice::from_raw_parts_mut(p, (n) as usize)",
            ),
            (
                GlueSpec::core(GlueCore::FromRawParts, false).with_len("n"),
                "core::slice::from_raw_parts(p, (n) as usize)",
            ),
            (
                GlueSpec::core(GlueCore::FromRawParts, true)
                    .with_len("n")
                    .wrapped(),
                "Some(core::slice::from_raw_parts_mut(p, (n) as usize))",
            ),
            // safe family
            (
                GlueSpec::core(GlueCore::FromRefMut, true),
                "core::slice::from_mut(p)",
            ),
            (
                GlueSpec::core(GlueCore::FromRefMut, false),
                "core::slice::from_ref(p)",
            ),
            (GlueSpec::core(GlueCore::Index0, true), "&mut p[0]"),
            (GlueSpec::core(GlueCore::Bare, false).wrapped(), "Some(p)"),
            (
                GlueSpec::core(GlueCore::FromRefMut, false).wrapped(),
                "Some(core::slice::from_ref(p))",
            ),
            (
                GlueSpec::core(GlueCore::Index0, false).wrapped(),
                "Some(&p[0])",
            ),
            // the null-panic convention: unwrap under each core
            (
                GlueSpec::core(GlueCore::Bare, false).with_unwrap(false),
                "p.unwrap()",
            ),
            (
                GlueSpec::core(GlueCore::Index0, true).with_unwrap(true),
                "&mut p.as_mut().unwrap()[0]",
            ),
        ];
        for (spec, expected) in cases {
            assert_eq!(
                spec.render(T).expect("every emitting spec renders"),
                expected,
                "renderer must be byte-identical to the arm it replaces: {spec:?}"
            );
        }
    }

    fn g(expected: Form, found: Form) -> Result<Option<(GlueSpec, SeamFamily)>, SeamBlock> {
        glue(expected, found, None)
    }

    /// The glue's TEXT — `glue` names a spec and the caller renders it, which is
    /// exactly what `seams` does in production. These assertions therefore still
    /// read the string the span layer writes, over the same argument, and they
    /// are the reason half 2 could not quietly change one.
    fn text(expected: Form, found: Form) -> String {
        rendered(g(expected, found), T)
    }

    fn rendered(got: Result<Option<(GlueSpec, SeamFamily)>, SeamBlock>, arg: &str) -> String {
        got.unwrap_or_else(|b| panic!("blocked: {b:?}"))
            .unwrap_or_else(|| panic!("no edit"))
            .0
            .render(arg)
            .expect("an emitting spec always renders")
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

    /// **THE UNWRAP SPELLING FOLLOWS THE *FOUND* SIDE — witnessed OFF THE
    /// DIAGONAL.**
    ///
    /// [`unwrap_expr`]'s whole reason for existing is that `Option<&mut T>` is
    /// not `Copy` and `.unwrap()` MOVES it, so the seam must spell that case
    /// `.as_mut().unwrap()`. Which spelling applies is therefore a fact about
    /// the value the caller HAS, never about the position it is going into.
    ///
    /// [`optional_wraps_one_way_and_unwraps_the_other`] pins both spellings but
    /// only where the two sides agree, so it is blind to a `glue` that read the
    /// EXPECTED side's mutability — the two are equal on the diagonal, which is
    /// the shape this module's own reborrow test warns about ("a witness on one
    /// direction witnesses half a table"). Found by mutation (M26): passing `w`
    /// where `h` belongs left the entire suite green.
    ///
    /// A shared position fed from a mutable optional is the discriminating
    /// case, and it is not exotic: `&T` is exactly what a read-only callee
    /// parameter converts to.
    #[test]
    fn the_unwrap_spelling_is_the_found_sides_and_not_the_expected_sides() {
        assert_eq!(
            text(
                Ref { mutable: false },
                Opt {
                    mutable: true,
                    slice: false
                }
            ),
            "p.as_mut().unwrap()",
            "a MUTABLE optional stays borrowed even into a SHARED position — \
             reading the expected side here would move it, and `E0382` would \
             appear only at a second use"
        );
        // The other off-diagonal pairing cannot occur: `shared_to_mut` blocks a
        // `&mut` position fed from a shared optional before any spec is built.
        // Asserted so the pair above is not mistaken for half a table in turn.
        assert_eq!(
            g(
                Ref { mutable: true },
                Opt {
                    mutable: false,
                    slice: false
                }
            ),
            Err(SeamBlock::SharedToMut)
        );
    }

    /// **The `Slice`-expected-from-`Opt`-found arm, BOTH fat/thin twins.**
    ///
    /// The arm picks its core on the FOUND optional's fatness: a fat optional
    /// already carries the slice and needs only the unwrap, while a thin one
    /// yields a reference that must be widened by `from_ref`/`from_mut`.
    /// Swapping the two produces glue that is well-formed and wrong in both
    /// directions — `core::slice::from_ref` applied to a slice, and a slice
    /// position handed a bare reference.
    ///
    /// Unwitnessed until mutation M25 swapped them and the suite stayed green.
    #[test]
    fn a_slice_position_widens_a_thin_optional_and_only_unwraps_a_fat_one() {
        assert_eq!(
            text(
                Slice { mutable: false },
                Opt {
                    mutable: false,
                    slice: true
                }
            ),
            "p.unwrap()",
            "a FAT optional is already the slice"
        );
        assert_eq!(
            text(
                Slice { mutable: true },
                Opt {
                    mutable: true,
                    slice: false
                }
            ),
            "core::slice::from_mut(p.as_mut().unwrap())",
            "a THIN optional yields a reference, which must be widened"
        );
        // The same split under the optional-expected arm, whose core selection
        // reads the EXPECTED side's fatness instead — the mirror choice, and
        // the reason the two arms cannot share one rule.
        assert_eq!(
            text(
                Opt {
                    mutable: false,
                    slice: true
                },
                Opt {
                    mutable: false,
                    slice: false
                }
            ),
            "Some(core::slice::from_ref(p.unwrap()))"
        );
        assert_eq!(
            text(
                Opt {
                    mutable: false,
                    slice: false
                },
                Opt {
                    mutable: false,
                    slice: true
                }
            ),
            "Some(&p.unwrap()[0])"
        );
    }

    /// **Optional over a raw base composes both families**, and the composition
    /// is `Some(&mut *p)` — not `&mut *Some(p)`, which does not parse as a
    /// pointer operation at all.
    #[test]
    fn optional_over_raw_composes_reborrow_inside_some() {
        let (spec, fam) = g(
            Opt {
                mutable: true,
                slice: false,
            },
            Raw,
        )
        .unwrap()
        .unwrap();
        assert_eq!(spec.render(T).unwrap(), "Some(&mut *p)");
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

    /// **Ruling B — a companion length turns the gate into a seam.**
    ///
    /// The same pair that gates with no length produces `from_raw_parts` with
    /// one, and the length is the caller's own text, cast rather than rendered.
    ///
    /// *Mutation-tested:* drop the `as usize` cast and the emitted call fails to
    /// type-check against `from_raw_parts`, whose length is a `usize` while the
    /// C spelling is `size_t`/`c_int`/`c_ulong` depending on the header.
    #[test]
    fn a_companion_length_converts_the_gate_into_a_slice_seam() {
        assert_eq!(
            rendered(glue(Slice { mutable: true }, Raw, Some("n")), "p"),
            "core::slice::from_raw_parts_mut(p, (n) as usize)"
        );
        assert_eq!(
            rendered(glue(Slice { mutable: false }, Raw, Some("len")), "p"),
            "core::slice::from_raw_parts(p, (len) as usize)"
        );
        // The fat optional composes the wrap around it.
        assert_eq!(
            rendered(
                glue(
                    Opt {
                        mutable: true,
                        slice: true
                    },
                    Raw,
                    Some("n")
                ),
                "p"
            ),
            "Some(core::slice::from_raw_parts_mut(p, (n) as usize))"
        );
        // **The gate still holds without one** — ruling item 4 stands, and B
        // widened which positions HAVE a length, never whether one may be
        // invented.
        assert_eq!(
            glue(Slice { mutable: true }, Raw, None),
            Err(SeamBlock::LengthUnknown)
        );
    }

    /// The length is a **raw base**, so a slice seam is REBORROW family however
    /// safe its constructor name reads.
    ///
    /// `from_raw_parts` is `unsafe` and carries the pointer-validity obligation;
    /// filing it under `Safe` would put the corpus's largest adapter population
    /// in the column that means "compiler-checked end to end".
    #[test]
    fn a_slice_seam_over_a_raw_base_is_reborrow_family() {
        assert_eq!(
            glue(Slice { mutable: true }, Raw, Some("n"))
                .unwrap()
                .unwrap()
                .1,
            SeamFamily::Reborrow
        );
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

    /// **THE CAST PEEL, at the side that decides it.**
    ///
    /// [`text_span_of`] is the whole of the decision layer's answer to *which
    /// subtree survives inside the adapter*, and getting it wrong is silent: the
    /// span layer replaces the whole argument either way, so a `&mut *(q as *mut
    /// u8)` would differ from the span layer's `&mut *q` only in the corpus
    /// differential, and only if this corpus places a seam on a cast at all.
    ///
    /// Mutation M28 collapsed the two cast arms onto the argument span and the
    /// entire suite stayed green — because the mapping lived inside a loop that
    /// needs a `TyCtxt`, a call site and a decision map to run. Lifting it out
    /// is what makes it witnessable.
    ///
    /// The `None` arms matter as much as the `Some` ones: a default of
    /// `arg.span` for an unnameable operand would hand the AST layer a subtree
    /// the replacement was never built from.
    #[test]
    fn the_replacement_text_comes_from_the_cast_operand_and_nowhere_else() {
        rustc_span::create_default_session_globals_then(|| {
            let whole = Span::with_root_ctxt(rustc_span::BytePos(100), rustc_span::BytePos(120));
            let operand = Span::with_root_ctxt(rustc_span::BytePos(100), rustc_span::BytePos(101));
            let hir = HirId::INVALID;

            // The shapes that read their OWN span.
            assert_eq!(text_span_of(ArgShape::BareLocal(hir), whole), Some(whole));
            assert_eq!(
                text_span_of(
                    ArgShape::AddrOf {
                        mutable: true,
                        base: None,
                        through_deref: false
                    },
                    whole
                ),
                Some(whole)
            );

            // The two that read the cast's OPERAND, which is strictly inside.
            assert_eq!(
                text_span_of(
                    ArgShape::AddrOfCast {
                        mutable: true,
                        inner: operand
                    },
                    whole
                ),
                Some(operand),
                "the replacement is built from the operand's snippet, so the \
                 operand is the subtree that must survive"
            );
            assert_eq!(
                text_span_of(
                    ArgShape::CastOfLocal {
                        binding: hir,
                        inner: operand
                    },
                    whole
                ),
                Some(operand)
            );
            assert_ne!(
                operand, whole,
                "the assertions above only mean anything if the two spans differ"
            );

            // And the shapes with no nameable operand answer NOTHING rather
            // than defaulting.
            assert_eq!(text_span_of(ArgShape::NullLit, whole), None);
            assert_eq!(text_span_of(ArgShape::Cast { inner: operand }, whole), None);
            assert_eq!(text_span_of(ArgShape::Other, whole), None);
        });
    }

    /// **THE RETIRED CLASSIFIER, kept as this test's oracle.**
    ///
    /// A verbatim transcription of the ten prefix tests `seam_tsv` ran over
    /// `edit.replacement` before condition 5 replaced them with
    /// [`GlueSpec::shape_key`]. Kept here and nowhere else: the census must
    /// carry the shape, and the only remaining question is *where the carried
    /// answer differs from the inferred one*, which needs both.
    fn inferred_shape(r: &str) -> &'static str {
        if r.starts_with("core::slice::from_raw_parts") {
            "from_raw_parts"
        } else if r.starts_with("Some(core::slice::from_raw_parts") {
            "some_from_raw_parts"
        } else if r.contains(".as_mut().unwrap()") {
            "as_mut_unwrap"
        } else if r.contains(".unwrap()") {
            "unwrap"
        } else if r.starts_with("Some(&mut *") || r.starts_with("Some(&*") {
            "some_reborrow"
        } else if r.starts_with("Some(core::slice::from_") {
            "some_from_ref_mut"
        } else if r.starts_with("Some(") {
            "some_wrap"
        } else if r.starts_with("&mut *") || r.starts_with("&*") {
            "reborrow"
        } else if r.starts_with("core::slice::from_") {
            "from_ref_mut"
        } else {
            "index"
        }
    }

    /// **Every spec `glue` can name agrees with the retired classifier — over a
    /// WELL-BEHAVED argument.** Condition 5's "same column" as a measurement.
    ///
    /// The argument is a bare identifier here deliberately, because that is the
    /// case in which the prefix classifier was *right*. The cases in which it
    /// was not are the next test, and they are the schema movement.
    #[test]
    fn the_carried_shape_agrees_with_the_retired_classifier() {
        for spec in every_emitting_spec() {
            assert_eq!(
                spec.shape_key(),
                inferred_shape(&spec.render("p").expect("emitting spec renders")),
                "carried and inferred shapes must agree on a bare argument: {spec:?}"
            );
        }
    }

    /// **THE RENDERER REFUSES A LENGTH-LESS SLICE ADAPTER.**
    ///
    /// It used to substitute an empty string and print
    /// `core::slice::from_raw_parts(p, () as usize)`. That is not merely
    /// "invalid Rust the compiler catches" — it is a **silent length
    /// substitution**, produced by the layer whose own field doc promises
    /// `None`-means-refused, at the socket the HELD fabricated-length slice
    /// plugs into. The AST builder refused the same input and counted it
    /// (`len_absent`), so the two halves of one contract disagreed and only the
    /// half with a witness was right.
    ///
    /// Unreachable through [`glue`] — asserted below — so this is fail-closed
    /// structure rather than a behaviour change, and it moves no corpus line.
    #[test]
    fn the_renderer_refuses_a_slice_adapter_with_no_length() {
        let lengthless = GlueSpec::core(GlueCore::FromRawParts, false);
        assert_eq!(
            lengthless.render("p"),
            None,
            "a length-bearing core with no length must REFUSE, never render \
             `() as usize` around an empty string"
        );
        assert_eq!(
            lengthless.wrapped().render("p"),
            None,
            "and the `Some` wrapper must not launder it either"
        );
        // With a length it renders normally, so the refusal is the missing
        // length rather than the shape.
        assert_eq!(
            GlueSpec::core(GlueCore::FromRawParts, false)
                .with_len("n")
                .render("p")
                .as_deref(),
            Some("core::slice::from_raw_parts(p, (n) as usize)")
        );
        // The gate is UPSTREAM: `glue` never names the refusing shape, which is
        // what makes this structure rather than a live path.
        assert_eq!(
            glue(Slice { mutable: false }, Raw, None),
            Err(SeamBlock::LengthUnknown)
        );
        assert!(
            every_emitting_spec()
                .iter()
                .all(|s| s.render("p").is_some()),
            "and every spec `glue` CAN name must still render, or the corpus \
             would move"
        );
    }

    /// **`index` IS REACHABLE, and `Bare`-without-a-wrapper is not** — the two
    /// halves of `shape_key`'s fallback arm, separated by measurement.
    ///
    /// The doc on that arm originally called the whole pairing unreachable
    /// "matched only to keep the function total". That is true of `Bare` and
    /// **false of `Index0`**: `glue`'s `(Ref, Slice)` arm builds exactly
    /// `core(Index0, w)`, which renders `&w X[0]` and classifies `index`. It is
    /// corpus-zero on the frozen corpus — and corpus-zero is not unreachable,
    /// which is the distinction this project has had to re-learn by name.
    ///
    /// Found by the maintainability reviewer at the arm-3 boundary. The code
    /// was right; the prose was not, so this is the witness the corrected prose
    /// needed rather than a second correction of it.
    #[test]
    fn the_index_shape_is_reachable_and_the_bare_one_is_not() {
        let (spec, family) = glue(Ref { mutable: true }, Slice { mutable: true }, None)
            .expect("a mutable reference from a mutable slice is adaptable")
            .expect("and it needs an edit");
        assert_eq!(
            spec.shape_key(),
            "index",
            "reached through `glue`, not by hand"
        );
        assert_eq!(spec.render("p").unwrap(), "&mut p[0]");
        assert_eq!(family, SeamFamily::Safe);
        assert!(
            !spec.optional && spec.unwrap.is_none(),
            "and with neither wrapper nor unwrap, so it lands in the fallback \
             arm rather than in a `some_*` one: {spec:?}"
        );

        // The other half: no pairing `glue` accepts produces a bare core with
        // neither an unwrap nor a wrapper. Asserted over the SAME enumeration
        // the agreement test uses, so the claim is checked rather than argued.
        assert!(
            every_emitting_spec()
                .iter()
                .all(|s| !(matches!(s.core, GlueCore::Bare) && !s.optional && s.unwrap.is_none())),
            "a bare core with no wrapper renders the argument unchanged; `glue` \
             returns `Ok(None)` for every pairing that would need it"
        );
        // ...and `index` really is corpus-zero, which is why the distinction
        // was invisible until now.
        assert!(
            every_emitting_spec()
                .iter()
                .any(|s| s.shape_key() == "index"),
            "the enumeration must actually reach `index`, or the assertion \
             above is vacuous"
        );
    }

    /// **Where the two DISAGREE, and why that is the point of carrying it.**
    ///
    /// The classifier reads a string the argument's own text contributes to, so
    /// an argument that happens to start with `*` or contain `.unwrap()` moves
    /// the inferred label while the decision is unchanged. These rows are the
    /// schema semantics change condition 5 requires to be recorded — *strictly
    /// better provenance*, stated as a witness rather than as a claim.
    #[test]
    fn the_classifier_was_argument_text_sensitive_and_the_carried_shape_is_not() {
        // An `Index0` wrap over an argument spelled `*q` renders `Some(&*q[0])`,
        // whose prefix is `Some(&*` — the classifier called that `some_reborrow`.
        let index0_wrapped = GlueSpec::core(GlueCore::Index0, false).wrapped();
        assert_eq!(index0_wrapped.render("*q").unwrap(), "Some(&*q[0])");
        assert_eq!(
            inferred_shape(&index0_wrapped.render("*q").unwrap()),
            "some_reborrow"
        );
        assert_eq!(index0_wrapped.shape_key(), "some_wrap");

        // An argument that is itself an `.unwrap()` call captured rule 4, which
        // sits ABOVE every `Some(` test.
        let some_wrap = GlueSpec::core(GlueCore::Bare, false).wrapped();
        assert_eq!(
            inferred_shape(&some_wrap.render("o.unwrap()").unwrap()),
            "unwrap"
        );
        assert_eq!(some_wrap.shape_key(), "some_wrap");

        // And the carried answer does not move with the argument at all — the
        // property that makes the column mean the decision.
        for arg in ["p", "*q", "o.unwrap()", "(*s).ptr", "&mut *raw"] {
            assert_eq!(
                some_wrap.shape_key(),
                "some_wrap",
                "the carried shape must not depend on the argument text ({arg})"
            );
        }
    }

    /// Every `(spec, family)` `glue` can return, enumerated by driving `glue`
    /// over the whole `(expected, found)` product rather than by transcribing
    /// the arms a second time.
    ///
    /// Transcription is what the renderer oracle does, and doing it twice would
    /// make both copies agree with each other instead of with the function.
    fn every_emitting_spec() -> Vec<GlueSpec> {
        let forms = [
            Raw,
            Ref { mutable: true },
            Ref { mutable: false },
            Slice { mutable: true },
            Slice { mutable: false },
            Opt {
                mutable: true,
                slice: false,
            },
            Opt {
                mutable: false,
                slice: false,
            },
            Opt {
                mutable: true,
                slice: true,
            },
            Opt {
                mutable: false,
                slice: true,
            },
        ];
        let mut out = Vec::new();
        for expected in forms {
            for found in forms {
                if let Ok(Some((spec, _))) = glue(expected, found, Some("n")) {
                    out.push(spec);
                }
            }
        }
        // **THE EXACT CARDINALITY, not a floor.** This read `>= 14`, which is
        // the RED-weakening shape: an entire arm can stop emitting — the
        // `Opt`/`Opt` arm alone is 6 of these pairs — while a floor of 14 stays
        // green. 44 is derived from the 9×9 product minus the identity/coercion
        // arms and the `SharedToMut` blocks, and it is pinned so a lost arm
        // fails HERE rather than showing up as a quiet corpus movement.
        assert_eq!(
            out.len(),
            44,
            "the product must reach every emitting arm exactly; got {}",
            out.len()
        );
        out
    }
}

// ---------------------------------------------------------------------------
// The call-site walk
// ---------------------------------------------------------------------------

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{Decision, DecisionTable, Subject, SubjectKind, emitability::ArgShape};

/// What the walk produced: placed adapters, and every position it refused with
/// the reason it refused it.
///
/// **Blocked positions are carried, not dropped.** The ledger rule this module
/// exists under: an unadapted position becomes a revert, and a revert with no
/// reason is a yield number nobody can attribute.
#[derive(Clone, Debug, Default)]
pub(crate) struct SeamPlan {
    pub edits: Vec<SeamEdit>,
    /// `(caller, callee, argument span, reason)`.
    ///
    /// **The callee rides here because the CALLER is the wrong axis for
    /// pricing** (2026-08-12). A refused seam costs the *callee's* conversion —
    /// [`SeamEdit::owner_fn`] is the callee for exactly that reason, so that a
    /// reverted callee takes its seams with it — while this row named only the
    /// caller. Anything asking *"which functions would gain if this refusal
    /// went away"* was therefore answerable only on the axis that does not
    /// revert.
    ///
    /// Two names rather than one, because they are two different functions and
    /// collapsing them is what made the question unanswerable.
    pub blocked: Vec<(LocalDefId, LocalDefId, Span, SeamBlock)>,
    /// **Ruling item 4a — companion-length coverage**, one row per
    /// length-gated position: `(callee path, pointer param index, evidence)`.
    ///
    /// MEASUREMENT ONLY. Nothing branches on it and no seam is placed from it:
    /// the ruling sequences the instrument ahead of the decision, so this
    /// answers *whether a length exists* without yet claiming which expression
    /// it is.
    pub length_evidence: Vec<(String, usize, LenEvidence)>,
    /// Pairs that fired with **no row in the measured census** — rule 1
    /// (2026-08-11): coverage derives from the type-level matrix, and the census
    /// is a prioritization overlay. A pair appearing here is not an error; it is
    /// the overlay being incomplete, which is expected and must be visible.
    pub uncensused: Vec<(Form, Form)>,
}

/// The form a decision emits.
fn form_of(decision: &Decision) -> Form {
    match decision {
        Decision::Ref { mutable } => Form::Ref { mutable: *mutable },
        Decision::Slice { mutable, .. } => Form::Slice { mutable: *mutable },
        Decision::Opt { mutable, slice, .. } => Form::Opt {
            mutable: *mutable,
            slice: *slice,
        },
        // A degraded subject keeps its raw pointer type.
        Decision::Degraded(_) => Form::Raw,
    }
}

/// The 17 `(found, expected)` rows the 2026-08-11 census measured. **Not a
/// coverage bound** — see [`SeamPlan::uncensused`].
fn in_census(found: Form, expected: Form) -> bool {
    use Form::*;
    matches!(
        (found, expected),
        (Raw, Ref { .. })
            | (Raw, Slice { .. })
            | (Raw, Opt { slice: false, .. })
            | (Raw, Opt { slice: true, .. })
            | (Ref { .. }, Opt { slice: false, .. })
            | (Ref { .. }, Slice { .. })
            | (Ref { .. }, Raw)
    )
}

/// Compute every seam adapter the crate needs.
///
/// Driven by the **type-level matrix**: the walk asks [`glue`] about every
/// `(expected, found)` pair it meets and the `match` there is exhaustive, so a
/// pair with no census row is adapted rather than skipped. The census only says
/// which pairs are *common*.
pub(crate) fn synthesize(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    subjects: &[Subject],
    table: &DecisionTable,
) -> SeamPlan {
    let sm = tcx.sess.source_map();
    let mut plan = SeamPlan::default();

    // subject key -> decision, and (fn, param index) -> subject key.
    let mut decision_of: FxHashMap<(LocalDefId, HirId), &Decision> = FxHashMap::default();
    for (subject, decision) in &table.entries {
        decision_of.insert((subject.fn_did, subject.hir_id), decision);
    }
    let mut param_key: FxHashMap<(LocalDefId, usize), (LocalDefId, HirId)> = FxHashMap::default();
    for subject in subjects {
        if let SubjectKind::Param { hir_index } = subject.kind {
            param_key.insert(
                (subject.fn_did, hir_index),
                (subject.fn_did, subject.hir_id),
            );
        }
    }

    // Deterministic callee order: `FxHashMap` iteration permutes between runs,
    // and D19 makes a report whose order permutes non-comparable.
    let mut callees: Vec<&LocalDefId> = facts.call_args.keys().collect();
    callees.sort_unstable_by_key(|d| d.local_def_index.as_u32());

    for callee in callees {
        for site in &facts.call_args[callee] {
            // ---- pass 1: what each position will look like after conversion ----
            //
            // Computed for the WHOLE site before any edit is emitted, because
            // the overlap gate below is a within-site question and cannot be
            // answered one argument at a time.
            //
            // A named struct rather than a tuple: `positions` deliberately does
            // NOT align with `site.args` (raw and unnameable positions are
            // dropped), so every field a later pass needs must be carried here.
            // Recovering the span by re-searching `site.args` was the first
            // shape and it reconstructed an alignment this list does not have.
            struct Pos {
                span: Span,
                /// The CALLEE's parameter index — item 4a asks about the
                /// signature, so the position must carry which parameter it is.
                index: usize,
                expected: Form,
                found: Form,
                text: Option<String>,
                /// **Where `text` was read from.** Equal to `span` for every
                /// shape except the two cast shapes, whose snippet comes from
                /// the cast's OPERAND while the replaced range is the whole
                /// argument. Carried because the AST layer must keep that
                /// operand as its subtree, and only this side knows which it
                /// was.
                text_span: Span,
                root: Option<HirId>,
                blind: bool,
            }
            let mut positions: Vec<Pos> = Vec::new();
            for arg in &site.args {
                let expected = param_key
                    .get(&(*callee, arg.index))
                    .and_then(|k| decision_of.get(k))
                    .map_or(Form::Raw, |d| form_of(d));
                // A raw parameter needs nothing: a reference coerces to a raw
                // pointer at a call, so every found form satisfies it.
                if matches!(expected, Form::Raw) {
                    continue;
                }
                // The third element is the span `text` is read from — carried
                // out of this match rather than reconstructed below, because
                // the two cast shapes read the OPERAND's snippet while every
                // other shape reads the argument's own.
                let (found, text, blind) = match arg.shape {
                    ArgShape::BareLocal(hir) => (
                        decision_of
                            .get(&(site.caller, hir))
                            .map_or(Form::Raw, |d| form_of(d)),
                        sm.span_to_snippet(arg.span).ok(),
                        false,
                    ),
                    ArgShape::AddrOf {
                        mutable,
                        base,
                        through_deref,
                    } => {
                        // §5a: a borrow rooted through a RAW deref is invisible
                        // to borrowck. Blind exactly when the base does not
                        // itself convert.
                        let blind = match (base, through_deref) {
                            (None, _) => true,
                            (Some(b), true) => !decision_of
                                .get(&(site.caller, b))
                                .is_some_and(|d| !matches!(d, Decision::Degraded(_))),
                            (Some(_), false) => false,
                        };
                        (
                            Form::Ref { mutable },
                            sm.span_to_snippet(arg.span).ok(),
                            blind,
                        )
                    }
                    ArgShape::AddrOfCast { mutable, inner } => {
                        (Form::Ref { mutable }, sm.span_to_snippet(inner).ok(), true)
                    }
                    ArgShape::CastOfLocal { binding, inner } => (
                        decision_of
                            .get(&(site.caller, binding))
                            .map_or(Form::Raw, |d| form_of(d)),
                        sm.span_to_snippet(inner).ok(),
                        false,
                    ),
                    // Not an expression this slice can name.
                    ArgShape::NullLit | ArgShape::Cast { .. } | ArgShape::Other => {
                        plan.blocked.push((
                            site.caller,
                            *callee,
                            arg.span,
                            SeamBlock::UnnameableOperand,
                        ));
                        continue;
                    }
                };
                // The two reads are kept in step by CONSTRUCTION: `text` is
                // the snippet of exactly this span, so a shape whose operand
                // moves moves both or neither.
                let Some(text_span) = text_span_of(arg.shape, arg.span) else {
                    // Unreachable — the shapes with no nameable operand are
                    // blocked above. Fail-closed rather than defaulting to
                    // `arg.span`, which would hand the AST layer a subtree the
                    // replacement was not built from.
                    plan.blocked.push((
                        site.caller,
                        *callee,
                        arg.span,
                        SeamBlock::UnnameableOperand,
                    ));
                    continue;
                };
                positions.push(Pos {
                    span: arg.span,
                    index: arg.index,
                    expected,
                    found,
                    text,
                    text_span,
                    root: arg.shape.place_root(),
                    blind,
                });
            }

            // ---- pass 2: THE SITE GATES, applied to adapter-generated
            // arguments exactly as to converted ones (ruling item 3) ----
            //
            // No bypass. The reborrow family puts its borrow in the region §5a
            // measured borrowck as blind in, so this gate is the only thing
            // standing between a seam and silent UB.
            let is_mut = |f: &Form| {
                matches!(
                    f,
                    Form::Ref { mutable: true }
                        | Form::Slice { mutable: true }
                        | Form::Opt { mutable: true, .. }
                )
            };
            let mut refused: Vec<usize> = Vec::new();
            for i in 0..positions.len() {
                for j in (i + 1)..positions.len() {
                    // Two SHARED borrows of one place are legal, so a conflict
                    // needs at least one `&mut`.
                    if !is_mut(&positions[i].expected) && !is_mut(&positions[j].expected) {
                        continue;
                    }
                    let same_root = !matches!(
                        (positions[i].root, positions[j].root),
                        (Some(x), Some(y)) if x != y
                    );
                    if same_root || positions[i].blind || positions[j].blind {
                        refused.push(i);
                        refused.push(j);
                    }
                }
            }

            // ---- pass 3: emit ----
            for (idx, pos) in positions.iter().enumerate() {
                if refused.contains(&idx) {
                    plan.blocked
                        .push((site.caller, *callee, pos.span, SeamBlock::SiteOverlap));
                    continue;
                }
                let Some(text) = pos.text.as_deref() else {
                    plan.blocked.push((
                        site.caller,
                        *callee,
                        pos.span,
                        SeamBlock::UnnameableOperand,
                    ));
                    continue;
                };
                // **Ruling B — the companion length, resolved at the CALL
                // SITE.** The evidence arm comes from the callee's signature
                // (which parameter is the integer); the TEXT comes from this
                // caller's argument in that position. Both are needed: the
                // signature says where to look, only the site says what is
                // actually passed.
                let wants_len = matches!(
                    (pos.expected, pos.found),
                    (Form::Slice { .. }, Form::Raw) | (Form::Opt { slice: true, .. }, Form::Raw)
                );
                let (len_text, len_arm) = if wants_len {
                    let arm = length_evidence(tcx, *callee, pos.index);
                    let companion = match arm {
                        LenEvidence::Following => Some(pos.index + 1),
                        LenEvidence::Preceding => pos.index.checked_sub(1),
                        // Ruling B licenses ADJACENCY ONLY. `Elsewhere` and
                        // `Absent` stay gated — 93 of the 370 — because a
                        // non-adjacent integer is not evidence of anything.
                        LenEvidence::Elsewhere | LenEvidence::None => None,
                    };
                    let text = companion
                        .and_then(|i| site.args.iter().find(|a| a.index == i))
                        .and_then(|a| sm.span_to_snippet(a.span).ok());
                    // The arm is recorded only when a length was actually
                    // FOUND: an arm with no text placed no seam, and tagging it
                    // would make the follow-up's population wrong.
                    (text.clone(), text.map(|_| arm))
                } else {
                    (None, None)
                };
                match glue(pos.expected, pos.found, len_text.as_deref()) {
                    Ok(None) => {}
                    Ok(Some((spec, family))) => {
                        // Rule 1 (2026-08-11): the census is a prioritization
                        // overlay, so a pair with no row is REPORTED, not
                        // refused.
                        if !in_census(pos.found, pos.expected) {
                            plan.uncensused.push((pos.found, pos.expected));
                        }
                        // **The rendering happens HERE**, over exactly the text
                        // the arms used to receive. `pos.text_span` is the span
                        // that text was read from, and it is carried beside the
                        // string so the AST layer can find the same subtree
                        // rather than re-deriving which part of the argument the
                        // span layer kept.
                        //
                        // A refusing render blocks under the EXISTING
                        // `LengthUnknown` key — the same outcome `glue` would
                        // have produced, so this is not new refusal vocabulary
                        // (STOP 4). Unreachable today; it exists so that no
                        // future producer of a spec can route a length-less
                        // slice adapter into a file.
                        let Some(replacement) = spec.render(text) else {
                            plan.blocked.push((
                                site.caller,
                                *callee,
                                pos.span,
                                SeamBlock::LengthUnknown,
                            ));
                            continue;
                        };
                        plan.edits.push(SeamEdit {
                            span: pos.span,
                            replacement,
                            owner_fn: tcx.def_path_str(callee.to_def_id()),
                            family,
                            len_arm,
                            spec,
                            arg_span: pos.text_span,
                        });
                    }
                    Err(block) => {
                        // Item 4a: price the length question where it is asked,
                        // so the coverage number is per BLOCKED POSITION rather
                        // than per signature — one signature serves many calls.
                        if block == SeamBlock::LengthUnknown {
                            plan.length_evidence.push((
                                tcx.def_path_str(callee.to_def_id()),
                                pos.index,
                                length_evidence(tcx, *callee, pos.index),
                            ));
                        }
                        plan.blocked.push((site.caller, *callee, pos.span, block));
                    }
                }
            }
        }
    }
    plan
}

/// **Where an argument's REPLACEMENT TEXT is read from**, which is not always
/// the argument's own span.
///
/// The two cast shapes build from the cast's OPERAND while the replaced range
/// stays the whole argument, so the surviving subtree is nested one level inside
/// the node the span layer overwrites. Everything else reads its own span.
///
/// A free function rather than three lines inside the position loop, because
/// that loop needs a `TyCtxt`, a call site and a decision map to run at all —
/// and a mapping that only a corpus sweep can exercise is a mapping with no
/// witness. Mutation M28 collapsed it onto `arg.span` and the entire suite
/// stayed green.
///
/// `None` for the shapes that carry no nameable operand; those positions are
/// already blocked as `UnnameableOperand` before any text is read.
fn text_span_of(shape: ArgShape, arg_span: Span) -> Option<Span> {
    match shape {
        ArgShape::BareLocal(_) | ArgShape::AddrOf { .. } => Some(arg_span),
        ArgShape::AddrOfCast { inner, .. } | ArgShape::CastOfLocal { inner, .. } => Some(inner),
        ArgShape::NullLit | ArgShape::Cast { .. } | ArgShape::Other => None,
    }
}

/// **Ruling item 4a — is there a companion length in the callee's signature?**
///
/// Reads the RESOLVED signature, on the `ptr_params` precedent: a C2Rust alias
/// lowers to a path, so a syntactic test would miss exactly the parameters this
/// corpus is made of.
pub(crate) fn length_evidence(tcx: TyCtxt<'_>, callee: LocalDefId, index: usize) -> LenEvidence {
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    let inputs = sig.inputs();
    let is_int = |i: usize| {
        inputs.get(i).is_some_and(|ty| {
            matches!(
                ty.kind(),
                rustc_middle::ty::TyKind::Int(_) | rustc_middle::ty::TyKind::Uint(_)
            )
        })
    };
    if index + 1 < inputs.len() && is_int(index + 1) {
        LenEvidence::Following
    } else if index > 0 && is_int(index - 1) {
        LenEvidence::Preceding
    } else if (0..inputs.len()).any(is_int) {
        LenEvidence::Elsewhere
    } else {
        LenEvidence::None
    }
}
