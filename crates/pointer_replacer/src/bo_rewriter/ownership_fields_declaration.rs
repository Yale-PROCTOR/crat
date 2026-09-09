//! One structural renderer for field declaration consequences. Captured spans
//! and AST trait/generic lists come from the integration adapter. Source text
//! is checked before every splice so a recovered plan cannot patch stale text.
use std::collections::BTreeMap;

use super::{FieldClassId, OwnerId, transaction::StructInterface};

#[derive(Clone, Debug)]
pub struct CapturedSpan {
    pub lo: usize,
    pub hi: usize,
    pub text: String,
}
#[derive(Clone, Debug)]
pub struct GenericSite {
    pub span: CapturedSpan,
    pub parameters: Vec<String>,
}
#[derive(Clone, Debug)]
pub struct DeriveSite {
    pub span: CapturedSpan,
    pub traits: Vec<String>,
}
#[derive(Clone, Debug)]
pub struct Declaration {
    pub owner: OwnerId,
    pub fields: BTreeMap<FieldClassId, CapturedSpan>,
    pub generics: GenericSite,
    pub derives: Vec<DeriveSite>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclarationHold {
    FieldIdentity,
    StaleSpan,
    Overlap,
    MissingCopyDerive,
}

pub fn render_declaration(
    source: &str,
    declaration: &Declaration,
    interface: &StructInterface,
) -> Result<String, DeclarationHold> {
    if declaration.fields.keys().ne(interface.field_types.keys())
        || declaration
            .fields
            .keys()
            .any(|f| f.owner != declaration.owner)
    {
        return Err(DeclarationHold::FieldIdentity);
    }
    let mut edits: Vec<(&CapturedSpan, String)> = declaration
        .fields
        .iter()
        .map(|(field, span)| (span, interface.field_types[field].clone()))
        .collect();
    if !interface.lifetimes.is_empty() {
        let mut parameters: Vec<_> = interface
            .lifetimes
            .iter()
            .map(|lt| format!("'{lt}"))
            .collect();
        parameters.extend(declaration.generics.parameters.iter().cloned());
        edits.push((
            &declaration.generics.span,
            format!("<{}>", parameters.join(", ")),
        ));
    }
    if interface.remove_copy_clone {
        let mut found = false;
        for derive in &declaration.derives {
            let retained: Vec<_> = derive
                .traits
                .iter()
                .filter(|name| !matches!(name.as_str(), "Copy" | "Clone"))
                .cloned()
                .collect();
            if retained.len() != derive.traits.len() {
                found = true;
                let replacement = if retained.is_empty() {
                    String::new()
                } else {
                    format!("#[derive({})]", retained.join(", "))
                };
                edits.push((&derive.span, replacement));
            }
        }
        if !found {
            return Err(DeclarationHold::MissingCopyDerive);
        }
    }
    for (span, _) in &edits {
        if source.get(span.lo..span.hi) != Some(span.text.as_str()) {
            return Err(DeclarationHold::StaleSpan);
        }
    }
    edits.sort_by_key(|(span, _)| (span.lo, span.hi));
    for pair in edits.windows(2) {
        let (a, b) = (pair[0].0, pair[1].0);
        if a.hi > b.lo || a.lo == b.lo {
            return Err(DeclarationHold::Overlap);
        }
    }
    let mut rendered = source.to_owned();
    for (span, replacement) in edits.into_iter().rev() {
        rendered.replace_range(span.lo..span.hi, &replacement);
    }
    Ok(rendered)
}
