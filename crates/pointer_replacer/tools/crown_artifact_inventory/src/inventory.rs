use std::collections::{BTreeMap, BTreeSet};

use rustc_ast::{
    ast::{
        AngleBracketedArg, AssocItem, AssocItemKind, Crate, Expr, ExprKind, FieldDef, Fn, FnRetTy,
        GenericArg, GenericArgs, Item, ItemKind, Local, Mutability, Pat, PatKind, StmtKind, Ty,
        TyKind,
    },
    visit::{self, AssocCtxt, Visitor},
};
use rustc_parse::{new_parser_from_source_str, DEFAULT_LOCALE_RESOURCE};
use rustc_session::parse::ParseSess;
use rustc_span::{create_session_if_not_set_then, edition::Edition, FileName};

const STATISTIC_KEYS: [&str; 9] = [
    "num_unsafe_ptrs",
    "num_non_arr_unsafe_ptrs",
    "num_mut_unsafe_ptrs",
    "num_non_arr_mut_unsafe_ptrs",
    "num_unsafe_usages",
    "num_non_arr_unsafe_usages",
    "num_mut_unsafe_usages",
    "num_non_arr_mut_unsafe_usages",
    "num_owning_ptrs_detected",
];

#[derive(Debug, Default, PartialEq, Eq)]
pub struct TypePositionCounts {
    pub local_box: u64,
    pub local_option_box: u64,
    pub param_box: u64,
    pub param_option_box: u64,
    pub return_box: u64,
    pub return_option_box: u64,
    pub field_box: u64,
    pub field_option_box: u64,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct DeclarationPositionCounts {
    pub local_raw_mut: u64,
    pub local_raw_const: u64,
    pub local_ref: u64,
    pub local_mut_ref: u64,
    pub local_option_ref: u64,
    pub local_option_mut_ref: u64,
    pub param_raw_mut: u64,
    pub param_raw_const: u64,
    pub param_ref: u64,
    pub param_mut_ref: u64,
    pub param_option_ref: u64,
    pub param_option_mut_ref: u64,
    pub return_raw_mut: u64,
    pub return_raw_const: u64,
    pub return_ref: u64,
    pub return_mut_ref: u64,
    pub return_option_ref: u64,
    pub return_option_mut_ref: u64,
    pub field_raw_mut: u64,
    pub field_raw_const: u64,
    pub field_ref: u64,
    pub field_mut_ref: u64,
    pub field_option_ref: u64,
    pub field_option_mut_ref: u64,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct RustCounts {
    pub types: TypePositionCounts,
    pub declarations: DeclarationPositionCounts,
    pub box_function_slot_keys: BTreeSet<String>,
    pub reference_function_slot_keys: BTreeSet<String>,
    pub inferred_box_local_slots: u64,
    pub box_new_calls: u64,
    pub box_new_local_initializers: u64,
    pub box_new_assignment_rhs: u64,
    pub box_from_raw_calls: u64,
    pub box_into_raw_calls: u64,
    pub malloc_calls: u64,
    pub calloc_calls: u64,
    pub realloc_calls: u64,
    pub free_calls: u64,
    pub drop_calls: u64,
}

impl RustCounts {
    pub fn merge(&mut self, other: Self) {
        self.types.local_box += other.types.local_box;
        self.types.local_option_box += other.types.local_option_box;
        self.types.param_box += other.types.param_box;
        self.types.param_option_box += other.types.param_option_box;
        self.types.return_box += other.types.return_box;
        self.types.return_option_box += other.types.return_option_box;
        self.types.field_box += other.types.field_box;
        self.types.field_option_box += other.types.field_option_box;
        self.declarations.merge(other.declarations);
        self.box_function_slot_keys
            .extend(other.box_function_slot_keys);
        self.reference_function_slot_keys
            .extend(other.reference_function_slot_keys);
        self.inferred_box_local_slots += other.inferred_box_local_slots;
        self.box_new_calls += other.box_new_calls;
        self.box_new_local_initializers += other.box_new_local_initializers;
        self.box_new_assignment_rhs += other.box_new_assignment_rhs;
        self.box_from_raw_calls += other.box_from_raw_calls;
        self.box_into_raw_calls += other.box_into_raw_calls;
        self.malloc_calls += other.malloc_calls;
        self.calloc_calls += other.calloc_calls;
        self.realloc_calls += other.realloc_calls;
        self.free_calls += other.free_calls;
        self.drop_calls += other.drop_calls;
    }

    pub fn box_type_positions(&self) -> u64 {
        self.types.local_box
            + self.types.local_option_box
            + self.types.param_box
            + self.types.param_option_box
            + self.types.return_box
            + self.types.return_option_box
            + self.types.field_box
            + self.types.field_option_box
    }

    pub fn allocation_calls(&self) -> u64 {
        self.malloc_calls + self.calloc_calls + self.realloc_calls
    }

    pub fn raw_pointer_type_positions(&self) -> u64 {
        self.declarations.raw_pointer_type_positions()
    }

    pub fn reference_family_type_positions(&self) -> u64 {
        self.declarations.reference_family_type_positions()
    }

    pub fn reference_function_slots(&self) -> u64 {
        self.reference_function_slot_keys.len() as u64
    }

    pub fn box_expression_evidence(&self) -> u64 {
        self.box_new_local_initializers + self.box_new_assignment_rhs
    }

    pub fn box_function_slots(&self) -> u64 {
        self.box_function_slot_keys.len() as u64
    }
}

impl DeclarationPositionCounts {
    fn merge(&mut self, other: Self) {
        self.local_raw_mut += other.local_raw_mut;
        self.local_raw_const += other.local_raw_const;
        self.local_ref += other.local_ref;
        self.local_mut_ref += other.local_mut_ref;
        self.local_option_ref += other.local_option_ref;
        self.local_option_mut_ref += other.local_option_mut_ref;
        self.param_raw_mut += other.param_raw_mut;
        self.param_raw_const += other.param_raw_const;
        self.param_ref += other.param_ref;
        self.param_mut_ref += other.param_mut_ref;
        self.param_option_ref += other.param_option_ref;
        self.param_option_mut_ref += other.param_option_mut_ref;
        self.return_raw_mut += other.return_raw_mut;
        self.return_raw_const += other.return_raw_const;
        self.return_ref += other.return_ref;
        self.return_mut_ref += other.return_mut_ref;
        self.return_option_ref += other.return_option_ref;
        self.return_option_mut_ref += other.return_option_mut_ref;
        self.field_raw_mut += other.field_raw_mut;
        self.field_raw_const += other.field_raw_const;
        self.field_ref += other.field_ref;
        self.field_mut_ref += other.field_mut_ref;
        self.field_option_ref += other.field_option_ref;
        self.field_option_mut_ref += other.field_option_mut_ref;
    }

    fn raw_pointer_type_positions(&self) -> u64 {
        self.local_raw_mut
            + self.local_raw_const
            + self.param_raw_mut
            + self.param_raw_const
            + self.return_raw_mut
            + self.return_raw_const
            + self.field_raw_mut
            + self.field_raw_const
    }

    fn reference_family_type_positions(&self) -> u64 {
        self.local_ref
            + self.local_mut_ref
            + self.local_option_ref
            + self.local_option_mut_ref
            + self.param_ref
            + self.param_mut_ref
            + self.param_option_ref
            + self.param_option_mut_ref
            + self.return_ref
            + self.return_mut_ref
            + self.return_option_ref
            + self.return_option_mut_ref
            + self.field_ref
            + self.field_mut_ref
            + self.field_option_ref
            + self.field_option_mut_ref
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct JsonClaimCounts {
    pub ownership_fn: BTreeMap<String, u64>,
    pub ownership_struct: BTreeMap<String, u64>,
    pub ownership_fn_by_depth: Vec<BTreeMap<String, u64>>,
    pub ownership_struct_by_depth: Vec<BTreeMap<String, u64>>,
    pub mutability_fn: BTreeMap<String, u64>,
    pub mutability_struct: BTreeMap<String, u64>,
    pub mutability_fn_by_depth: Vec<BTreeMap<String, u64>>,
    pub mutability_struct_by_depth: Vec<BTreeMap<String, u64>>,
    pub fatness_fn: BTreeMap<String, u64>,
    pub fatness_struct: BTreeMap<String, u64>,
    pub fatness_fn_by_depth: Vec<BTreeMap<String, u64>>,
    pub fatness_struct_by_depth: Vec<BTreeMap<String, u64>>,
    pub statistics: BTreeMap<String, u64>,
    pub fn_d0_mut_ptr: u64,
    pub fn_d0_mut_ptr_keys: BTreeSet<String>,
    pub max_depth: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OfficialEvaluation {
    pub declaration_before: u64,
    pub declaration_after: u64,
    pub declaration_rate: String,
    pub usage_before: u64,
    pub usage_after: u64,
    pub usage_rate: String,
}

pub fn parse_official_evaluation(
    source: &str,
) -> Result<BTreeMap<String, OfficialEvaluation>, String> {
    const HEADER: &str =
        "Benchmark Name,#Unsafe Mutable Non-Array Pointers,,,#Unsafe Mutable Non-Array Usages,,";
    let mut lines = source.lines();
    if lines.next() != Some(HEADER) {
        return Err("evaluation.tsv: unexpected header".to_owned());
    }
    let mut rows = BTreeMap::new();
    for (index, line) in lines.enumerate() {
        let values: Vec<_> = line.split(',').collect();
        if values.len() != 7 {
            return Err(format!("evaluation.tsv:{}: expected 7 columns", index + 2));
        }
        let parse_count = |column: usize| -> Result<u64, String> {
            values[column].parse().map_err(|_| {
                format!(
                    "evaluation.tsv:{}: column {} must be a non-negative integer",
                    index + 2,
                    column + 1
                )
            })
        };
        let row = OfficialEvaluation {
            declaration_before: parse_count(1)?,
            declaration_after: parse_count(2)?,
            declaration_rate: values[3].to_owned(),
            usage_before: parse_count(4)?,
            usage_after: parse_count(5)?,
            usage_rate: values[6].to_owned(),
        };
        validate_official_rate(
            index + 2,
            "declaration",
            row.declaration_before,
            row.declaration_after,
            &row.declaration_rate,
        )?;
        validate_official_rate(
            index + 2,
            "usage",
            row.usage_before,
            row.usage_after,
            &row.usage_rate,
        )?;
        if rows.insert(values[0].to_owned(), row).is_some() {
            return Err(format!(
                "evaluation.tsv:{}: duplicate program {}",
                index + 2,
                values[0]
            ));
        }
    }
    let before: u64 = rows.values().map(|row| row.declaration_before).sum();
    let after: u64 = rows.values().map(|row| row.declaration_after).sum();
    if (before, after) != (2_414, 1_711) {
        return Err(format!(
            "evaluation.tsv: declaration totals must be 2414/1711, got {before}/{after}"
        ));
    }
    Ok(rows)
}

fn validate_official_rate(
    line: usize,
    metric: &str,
    before: u64,
    after: u64,
    actual: &str,
) -> Result<(), String> {
    let expected = if before == 0 {
        "NaN%".to_owned()
    } else {
        format!(
            "{:.1}%",
            (before.saturating_sub(after)) as f64 * 100.0 / before as f64
        )
    };
    if actual != expected {
        return Err(format!(
            "evaluation.tsv:{line}: {metric} rate {actual} does not match {expected}"
        ));
    }
    Ok(())
}

pub fn analyze_rust_source(source: &str) -> Result<RustCounts, String> {
    analyze_rust_sources(&[source])
}

pub fn analyze_rust_sources(sources: &[&str]) -> Result<RustCounts, String> {
    let named: Vec<_> = sources.iter().map(|source| ("", *source)).collect();
    analyze_named_rust_sources(&named)
}

pub fn analyze_named_rust_sources(sources: &[(&str, &str)]) -> Result<RustCounts, String> {
    create_session_if_not_set_then(Edition::Edition2018, |_| {
        analyze_named_rust_sources_in_session(sources)
    })
}

fn analyze_named_rust_sources_in_session(sources: &[(&str, &str)]) -> Result<RustCounts, String> {
    let files: Vec<_> = sources
        .iter()
        .map(|(module, source)| parse_rust_source(module, source).map(|file| (*module, file)))
        .collect::<Result<_, _>>()?;
    let mut box_environment = BoxExpressionEnvironment::default();
    for (_, file) in &files {
        box_environment.visit_crate(file);
    }
    let mut total = RustCounts::default();
    for (module, file) in &files {
        total.merge(analyze_rust_file(module, file, &box_environment));
    }
    Ok(total)
}

fn parse_rust_source(module: &str, source: &str) -> Result<Crate, String> {
    let mut parse_sess = ParseSess::new(vec![DEFAULT_LOCALE_RESOURCE]);
    parse_sess.dcx().make_silent();
    parse_sess.edition = Edition::Edition2018;
    let name = if module.is_empty() {
        "input.rs"
    } else {
        module
    };
    let mut parser = new_parser_from_source_str(
        &parse_sess,
        FileName::Custom(name.to_owned()),
        source.to_owned(),
    )
    .map_err(|errors| {
        for error in errors {
            error.cancel();
        }
        "failed to initialize rustc parser".to_owned()
    })?;
    let krate = parser.parse_crate_mod().map_err(|error| {
        error.cancel();
        "invalid Rust syntax".to_owned()
    })?;
    drop(parser);
    if parse_sess.dcx().has_errors().is_some() {
        Err("invalid Rust syntax".to_owned())
    } else {
        Ok(krate)
    }
}

fn analyze_rust_file(
    module: &str,
    file: &Crate,
    box_environment: &BoxExpressionEnvironment,
) -> RustCounts {
    let declaration_aliases = collect_declaration_aliases(file);
    let inferred_box_function_slot_keys = infer_box_local_slots(module, file, box_environment);
    let mut visitor = RustInventoryVisitor {
        counts: RustCounts {
            inferred_box_local_slots: inferred_box_function_slot_keys.len() as u64,
            box_function_slot_keys: inferred_box_function_slot_keys,
            ..RustCounts::default()
        },
        declaration_aliases: &declaration_aliases,
        current_function: None,
        module,
    };
    visitor.visit_crate(file);
    visitor.counts
}

pub fn analyze_json_claims(
    ownership: &str,
    statistics: &str,
    mutability: &str,
    fatness: &str,
) -> Result<JsonClaimCounts, String> {
    let ownership = parse_json_document("ownership.json", ownership)?;
    let statistics = parse_json_document("statistics.json", statistics)?;
    let mutability = parse_json_document("mutability.json", mutability)?;
    let fatness = parse_json_document("fatness.json", fatness)?;

    let mut counts = JsonClaimCounts::default();
    count_qualifier_scope(
        "ownership.json",
        &ownership,
        "fn_data",
        &["Owning", "Transient", "Unknown"],
        &mut counts.ownership_fn,
        &mut counts.ownership_fn_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "ownership.json",
        &ownership,
        "struct_data",
        &["Owning", "Transient", "Unknown"],
        &mut counts.ownership_struct,
        &mut counts.ownership_struct_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "mutability.json",
        &mutability,
        "fn_data",
        &["Mut", "Imm"],
        &mut counts.mutability_fn,
        &mut counts.mutability_fn_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "mutability.json",
        &mutability,
        "struct_data",
        &["Mut", "Imm"],
        &mut counts.mutability_struct,
        &mut counts.mutability_struct_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "fatness.json",
        &fatness,
        "fn_data",
        &["Arr", "Ptr"],
        &mut counts.fatness_fn,
        &mut counts.fatness_fn_by_depth,
        &mut counts.max_depth,
    )?;
    count_qualifier_scope(
        "fatness.json",
        &fatness,
        "struct_data",
        &["Arr", "Ptr"],
        &mut counts.fatness_struct,
        &mut counts.fatness_struct_by_depth,
        &mut counts.max_depth,
    )?;
    counts.fn_d0_mut_ptr_keys =
        joint_fn_d0_keys("mutability.json", &mutability, "fatness.json", &fatness)?;
    counts.fn_d0_mut_ptr = counts.fn_d0_mut_ptr_keys.len() as u64;
    let statistics = statistics
        .as_object()
        .ok_or_else(|| "statistics.json: root must be an object".to_owned())?;
    for key in STATISTIC_KEYS {
        let value = statistics
            .get(key)
            .ok_or_else(|| format!("statistics.json: missing {key}"))?
            .as_u64()
            .ok_or_else(|| format!("statistics.json: {key} must be a non-negative integer"))?;
        counts.statistics.insert(key.to_owned(), value);
    }
    if let Some(unexpected) = statistics
        .keys()
        .find(|key| !STATISTIC_KEYS.contains(&key.as_str()))
    {
        return Err(format!(
            "statistics.json: unexpected summary counter {unexpected}"
        ));
    }
    Ok(counts)
}

fn joint_fn_d0_keys(
    left_name: &str,
    left: &serde_json::Value,
    right_name: &str,
    right: &serde_json::Value,
) -> Result<BTreeSet<String>, String> {
    let scope = "fn_data";
    let left = left
        .as_object()
        .and_then(|root| root.get(scope))
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| format!("{left_name}: {scope} must be an object"))?;
    let right = right
        .as_object()
        .and_then(|root| root.get(scope))
        .and_then(serde_json::Value::as_object)
        .ok_or_else(|| format!("{right_name}: {scope} must be an object"))?;
    let mut keys = BTreeSet::new();
    for (owner, left_slots) in left {
        let left_slots = left_slots
            .as_object()
            .ok_or_else(|| format!("{left_name}: {scope}.{owner} must be an object"))?;
        let right_slots = right
            .get(owner)
            .and_then(serde_json::Value::as_object)
            .ok_or_else(|| format!("{right_name}: missing {scope}.{owner}"))?;
        for (slot, left_labels) in left_slots {
            let left_labels = left_labels
                .as_array()
                .ok_or_else(|| format!("{left_name}: {scope}.{owner}.{slot} must be an array"))?;
            let right_labels = right_slots
                .get(slot)
                .and_then(serde_json::Value::as_array)
                .ok_or_else(|| format!("{right_name}: missing {scope}.{owner}.{slot}"))?;
            if left_labels.len() != right_labels.len() {
                return Err(format!(
                    "{left_name}/{right_name}: depth mismatch at {scope}.{owner}.{slot}"
                ));
            }
            if left_labels.first().and_then(serde_json::Value::as_str) == Some("Mut")
                && right_labels.first().and_then(serde_json::Value::as_str) == Some("Ptr")
            {
                keys.insert(function_slot_key(owner, slot));
            }
        }
        if let Some(unexpected) = right_slots
            .keys()
            .find(|slot| !left_slots.contains_key(*slot))
        {
            return Err(format!(
                "{right_name}: unexpected {scope}.{owner}.{unexpected}"
            ));
        }
    }
    if let Some(unexpected) = right.keys().find(|owner| !left.contains_key(*owner)) {
        return Err(format!("{right_name}: unexpected {scope}.{unexpected}"));
    }
    Ok(keys)
}

#[derive(Clone, Copy)]
enum BoxFamily {
    Box,
    OptionBox,
}

#[derive(Clone, Copy)]
enum DeclarationFamily {
    RawMut,
    RawConst,
    Ref,
    MutRef,
    OptionRef,
    OptionMutRef,
}

struct RustInventoryVisitor<'aliases> {
    counts: RustCounts,
    declaration_aliases: &'aliases BTreeMap<String, DeclarationFamily>,
    current_function: Option<String>,
    module: &'aliases str,
}

impl<'aliases, 'ast> Visitor<'ast> for RustInventoryVisitor<'aliases> {
    fn visit_item(&mut self, item: &'ast Item) {
        let ItemKind::Fn(function) = &item.kind else {
            visit::walk_item(self, item);
            return;
        };
        let previous = self.current_function.replace(qualified_function(
            self.module,
            &function.ident.name.to_string(),
        ));
        self.count_function_signature(function);
        visit::walk_item(self, item);
        self.current_function = previous;
    }

    fn visit_assoc_item(&mut self, item: &'ast AssocItem, ctxt: AssocCtxt) {
        let AssocItemKind::Fn(function) = &item.kind else {
            visit::walk_assoc_item(self, item, ctxt);
            return;
        };
        if matches!(ctxt, AssocCtxt::Impl { .. }) {
            let previous = self.current_function.replace(qualified_function(
                self.module,
                &function.ident.name.to_string(),
            ));
            self.count_function_signature(function);
            visit::walk_assoc_item(self, item, ctxt);
            self.current_function = previous;
        } else {
            self.count_function_signature(function);
            visit::walk_assoc_item(self, item, ctxt);
        }
    }

    fn visit_local(&mut self, local: &'ast Local) {
        if let (Some(function), Some(slot)) = (&self.current_function, pat_ident(&local.pat)) {
            if local.ty.as_deref().and_then(box_family).is_some() {
                self.counts
                    .box_function_slot_keys
                    .insert(function_slot_key(function, &slot));
            }
            if local
                .ty
                .as_deref()
                .and_then(|ty| declaration_family(ty, self.declaration_aliases))
                .is_some_and(is_reference_family)
            {
                self.counts
                    .reference_function_slot_keys
                    .insert(function_slot_key(function, &slot));
            }
        }
        if let Some(ty) = local.ty.as_deref() {
            increment_type_position(
                box_family(ty),
                &mut self.counts.types.local_box,
                &mut self.counts.types.local_option_box,
            );
            increment_declaration_position(
                declaration_family(ty, self.declaration_aliases),
                DeclarationPosition::Local,
                &mut self.counts.declarations,
            );
        }
        if let Some(init) = local.kind.init() {
            self.counts.box_new_local_initializers += count_box_new_calls(init);
        }
        visit::walk_local(self, local);
    }

    fn visit_field_def(&mut self, field: &'ast FieldDef) {
        increment_type_position(
            box_family(&field.ty),
            &mut self.counts.types.field_box,
            &mut self.counts.types.field_option_box,
        );
        increment_declaration_position(
            declaration_family(&field.ty, self.declaration_aliases),
            DeclarationPosition::Field,
            &mut self.counts.declarations,
        );
        visit::walk_field_def(self, field);
    }

    fn visit_foreign_mod(&mut self, _foreign: &'ast rustc_ast::ast::ForeignMod) {}

    fn visit_expr(&mut self, expression: &'ast Expr) {
        if let ExprKind::Assign(_, right, _) = &expression.kind {
            self.counts.box_new_assignment_rhs += count_box_new_calls(right);
        }
        if let ExprKind::Call(callee, _) = &expression.kind {
            if let ExprKind::Path(_, path) = &callee.kind {
                let mut segments = path.segments.iter().rev();
                let Some(last) = segments.next() else {
                    visit::walk_expr(self, expression);
                    return;
                };
                let name = last.ident.name.as_str();
                if name == "malloc" {
                    self.counts.malloc_calls += 1;
                } else if name == "calloc" {
                    self.counts.calloc_calls += 1;
                } else if name == "realloc" {
                    self.counts.realloc_calls += 1;
                } else if name == "free" {
                    self.counts.free_calls += 1;
                } else if name == "drop" {
                    self.counts.drop_calls += 1;
                } else if is_box_associated_call(callee, "new") {
                    self.counts.box_new_calls += 1;
                } else if is_box_associated_call(callee, "from_raw") {
                    self.counts.box_from_raw_calls += 1
                } else if is_box_associated_call(callee, "into_raw") {
                    self.counts.box_into_raw_calls += 1
                }
            }
        }
        visit::walk_expr(self, expression);
    }
}

impl RustInventoryVisitor<'_> {
    fn count_function_signature(&mut self, function: &Fn) {
        for input in &function.sig.decl.inputs {
            // Method receivers are not inventory parameter slots, although rustc
            // represents them as typed inputs.
            if input.is_self() {
                continue;
            }
            if let (Some(function), Some(slot)) = (&self.current_function, pat_ident(&input.pat)) {
                if box_family(&input.ty).is_some() {
                    self.counts
                        .box_function_slot_keys
                        .insert(function_slot_key(function, &slot));
                }
                if declaration_family(&input.ty, self.declaration_aliases)
                    .is_some_and(is_reference_family)
                {
                    self.counts
                        .reference_function_slot_keys
                        .insert(function_slot_key(function, &slot));
                }
            }
            increment_type_position(
                box_family(&input.ty),
                &mut self.counts.types.param_box,
                &mut self.counts.types.param_option_box,
            );
            increment_declaration_position(
                declaration_family(&input.ty, self.declaration_aliases),
                DeclarationPosition::Param,
                &mut self.counts.declarations,
            );
        }
        if let FnRetTy::Ty(ty) = &function.sig.decl.output {
            increment_type_position(
                box_family(ty),
                &mut self.counts.types.return_box,
                &mut self.counts.types.return_option_box,
            );
            increment_declaration_position(
                declaration_family(ty, self.declaration_aliases),
                DeclarationPosition::Return,
                &mut self.counts.declarations,
            );
        }
    }
}

#[derive(Clone, Copy)]
enum DeclarationPosition {
    Local,
    Param,
    Return,
    Field,
}

fn increment_declaration_position(
    family: Option<DeclarationFamily>,
    position: DeclarationPosition,
    counts: &mut DeclarationPositionCounts,
) {
    let Some(family) = family else {
        return;
    };
    let counter = match (position, family) {
        (DeclarationPosition::Local, DeclarationFamily::RawMut) => &mut counts.local_raw_mut,
        (DeclarationPosition::Local, DeclarationFamily::RawConst) => &mut counts.local_raw_const,
        (DeclarationPosition::Local, DeclarationFamily::Ref) => &mut counts.local_ref,
        (DeclarationPosition::Local, DeclarationFamily::MutRef) => &mut counts.local_mut_ref,
        (DeclarationPosition::Local, DeclarationFamily::OptionRef) => &mut counts.local_option_ref,
        (DeclarationPosition::Local, DeclarationFamily::OptionMutRef) => {
            &mut counts.local_option_mut_ref
        }
        (DeclarationPosition::Param, DeclarationFamily::RawMut) => &mut counts.param_raw_mut,
        (DeclarationPosition::Param, DeclarationFamily::RawConst) => &mut counts.param_raw_const,
        (DeclarationPosition::Param, DeclarationFamily::Ref) => &mut counts.param_ref,
        (DeclarationPosition::Param, DeclarationFamily::MutRef) => &mut counts.param_mut_ref,
        (DeclarationPosition::Param, DeclarationFamily::OptionRef) => &mut counts.param_option_ref,
        (DeclarationPosition::Param, DeclarationFamily::OptionMutRef) => {
            &mut counts.param_option_mut_ref
        }
        (DeclarationPosition::Return, DeclarationFamily::RawMut) => &mut counts.return_raw_mut,
        (DeclarationPosition::Return, DeclarationFamily::RawConst) => &mut counts.return_raw_const,
        (DeclarationPosition::Return, DeclarationFamily::Ref) => &mut counts.return_ref,
        (DeclarationPosition::Return, DeclarationFamily::MutRef) => &mut counts.return_mut_ref,
        (DeclarationPosition::Return, DeclarationFamily::OptionRef) => {
            &mut counts.return_option_ref
        }
        (DeclarationPosition::Return, DeclarationFamily::OptionMutRef) => {
            &mut counts.return_option_mut_ref
        }
        (DeclarationPosition::Field, DeclarationFamily::RawMut) => &mut counts.field_raw_mut,
        (DeclarationPosition::Field, DeclarationFamily::RawConst) => &mut counts.field_raw_const,
        (DeclarationPosition::Field, DeclarationFamily::Ref) => &mut counts.field_ref,
        (DeclarationPosition::Field, DeclarationFamily::MutRef) => &mut counts.field_mut_ref,
        (DeclarationPosition::Field, DeclarationFamily::OptionRef) => &mut counts.field_option_ref,
        (DeclarationPosition::Field, DeclarationFamily::OptionMutRef) => {
            &mut counts.field_option_mut_ref
        }
    };
    *counter += 1;
}

fn increment_type_position(family: Option<BoxFamily>, plain: &mut u64, optional: &mut u64) {
    match family {
        Some(BoxFamily::Box) => *plain += 1,
        Some(BoxFamily::OptionBox) => *optional += 1,
        None => {}
    }
}

fn box_family(ty: &Ty) -> Option<BoxFamily> {
    let TyKind::Path(_, path) = &strip_type_wrappers(ty).kind else {
        return None;
    };
    let last = path.segments.last()?;
    if last.ident.name.as_str() == "Box" {
        return Some(BoxFamily::Box);
    }
    if last.ident.name.as_str() != "Option" {
        return None;
    }
    matches!(
        first_type_argument(last.args.as_deref()).and_then(box_family),
        Some(BoxFamily::Box)
    )
    .then_some(BoxFamily::OptionBox)
}

fn declaration_family(
    ty: &Ty,
    aliases: &BTreeMap<String, DeclarationFamily>,
) -> Option<DeclarationFamily> {
    match &strip_type_wrappers(ty).kind {
        TyKind::Ptr(pointer) => Some(if pointer.mutbl == Mutability::Mut {
            DeclarationFamily::RawMut
        } else {
            DeclarationFamily::RawConst
        }),
        TyKind::Ref(_, reference) => Some(if reference.mutbl == Mutability::Mut {
            DeclarationFamily::MutRef
        } else {
            DeclarationFamily::Ref
        }),
        TyKind::Path(_, path) => {
            let last = path.segments.last()?;
            let name = last.ident.name.to_string();
            if name != "Option" {
                return aliases.get(&name).copied();
            }
            match first_type_argument(last.args.as_deref())
                .and_then(|inner| declaration_family(inner, aliases))
            {
                Some(DeclarationFamily::Ref) => Some(DeclarationFamily::OptionRef),
                Some(DeclarationFamily::MutRef) => Some(DeclarationFamily::OptionMutRef),
                _ => None,
            }
        }
        _ => None,
    }
}

fn first_type_argument(arguments: Option<&GenericArgs>) -> Option<&Ty> {
    let GenericArgs::AngleBracketed(arguments) = arguments? else {
        return None;
    };
    arguments.args.iter().find_map(|argument| match argument {
        AngleBracketedArg::Arg(GenericArg::Type(ty)) => Some(ty.as_ref()),
        _ => None,
    })
}

fn is_reference_family(family: DeclarationFamily) -> bool {
    matches!(
        family,
        DeclarationFamily::Ref
            | DeclarationFamily::MutRef
            | DeclarationFamily::OptionRef
            | DeclarationFamily::OptionMutRef
    )
}

fn function_slot_key(function: &str, slot: &str) -> String {
    format!("{function}::{slot}")
}

fn qualified_function(module: &str, function: &str) -> String {
    if module.is_empty() {
        function.to_owned()
    } else {
        format!("{module}::{function}")
    }
}

fn collect_declaration_aliases(file: &Crate) -> BTreeMap<String, DeclarationFamily> {
    #[derive(Default)]
    struct AliasCollector {
        definitions: Vec<(String, Ty)>,
    }

    impl<'ast> Visitor<'ast> for AliasCollector {
        fn visit_item(&mut self, item: &'ast Item) {
            if let ItemKind::TyAlias(alias) = &item.kind {
                if let Some(ty) = &alias.ty {
                    self.definitions
                        .push((alias.ident.name.to_string(), ty.as_ref().clone()));
                }
            }
            visit::walk_item(self, item);
        }
    }

    let mut collector = AliasCollector::default();
    collector.visit_crate(file);
    let mut aliases = BTreeMap::new();
    loop {
        let before = aliases.len();
        for (name, ty) in &collector.definitions {
            if let Some(family) = declaration_family(ty, &aliases) {
                aliases.insert(name.clone(), family);
            }
        }
        if aliases.len() == before {
            return aliases;
        }
    }
}

fn strip_type_wrappers(mut ty: &Ty) -> &Ty {
    loop {
        ty = match &ty.kind {
            TyKind::Paren(inner) => inner,
            _ => return ty,
        };
    }
}

fn count_box_new_calls(expr: &Expr) -> u64 {
    #[derive(Default)]
    struct BoxNewVisitor {
        count: u64,
    }

    impl<'ast> Visitor<'ast> for BoxNewVisitor {
        fn visit_expr(&mut self, expression: &'ast Expr) {
            if let ExprKind::Call(callee, _) = &expression.kind {
                if is_box_associated_call(callee, "new") {
                    self.count += 1;
                }
            }
            visit::walk_expr(self, expression);
        }
    }

    let mut visitor = BoxNewVisitor::default();
    visitor.visit_expr(expr);
    visitor.count
}

#[derive(Default)]
struct BoxExpressionEnvironment {
    returning_functions: BTreeSet<String>,
    fields: BTreeSet<String>,
}

impl<'ast> Visitor<'ast> for BoxExpressionEnvironment {
    fn visit_item(&mut self, item: &'ast Item) {
        if let ItemKind::Fn(function) = &item.kind {
            if let FnRetTy::Ty(ty) = &function.sig.decl.output {
                if box_family(ty).is_some() {
                    self.returning_functions
                        .insert(function.ident.name.to_string());
                }
            }
        }
        visit::walk_item(self, item);
    }

    fn visit_field_def(&mut self, field: &'ast FieldDef) {
        if box_family(&field.ty).is_some() {
            if let Some(ident) = field.ident {
                self.fields.insert(ident.name.to_string());
            }
        }
        visit::walk_field_def(self, field);
    }
}

fn infer_box_local_slots(
    module: &str,
    file: &Crate,
    environment: &BoxExpressionEnvironment,
) -> BTreeSet<String> {
    struct FunctionCounter<'environment, 'module> {
        environment: &'environment BoxExpressionEnvironment,
        module: &'module str,
        slots: BTreeSet<String>,
    }

    impl<'environment, 'module, 'ast> Visitor<'ast> for FunctionCounter<'environment, 'module> {
        fn visit_item(&mut self, item: &'ast Item) {
            if let ItemKind::Fn(function) = &item.kind {
                self.slots.extend(infer_function_box_locals(
                    self.module,
                    function,
                    self.environment,
                ));
            } else {
                visit::walk_item(self, item);
            }
        }
    }

    let mut counter = FunctionCounter {
        environment,
        module,
        slots: BTreeSet::new(),
    };
    counter.visit_crate(file);
    counter.slots
}

fn infer_function_box_locals(
    module: &str,
    function: &Fn,
    environment: &BoxExpressionEnvironment,
) -> BTreeSet<String> {
    #[derive(Default)]
    struct FlowCollector {
        bindings: BTreeSet<String>,
        explicit_box_locals: BTreeSet<String>,
        flows: Vec<(String, Expr)>,
    }

    impl<'ast> Visitor<'ast> for FlowCollector {
        fn visit_local(&mut self, local: &'ast Local) {
            if let Some(name) = pat_ident(&local.pat) {
                self.bindings.insert(name.clone());
                if local.ty.as_deref().and_then(box_family).is_some() {
                    self.explicit_box_locals.insert(name.clone());
                }
                if let Some(init) = local.kind.init() {
                    self.flows.push((name, init.clone()));
                }
            }
            visit::walk_local(self, local);
        }

        fn visit_expr(&mut self, expression: &'ast Expr) {
            if let ExprKind::Assign(left, right, _) = &expression.kind {
                if let ExprKind::Path(_, path) = &left.kind {
                    if let Some(ident) = simple_path_ident(path) {
                        self.flows.push((ident, right.as_ref().clone()));
                    }
                }
            }
            visit::walk_expr(self, expression);
        }
    }

    let mut known = BTreeSet::new();
    for input in &function.sig.decl.inputs {
        if input.is_self() {
            continue;
        }
        if box_family(&input.ty).is_some() {
            if let Some(name) = pat_ident(&input.pat) {
                known.insert(name);
            }
        }
    }

    let mut collector = FlowCollector::default();
    let Some(body) = &function.body else {
        return BTreeSet::new();
    };
    collector.visit_block(body);
    known.extend(collector.explicit_box_locals.iter().cloned());
    loop {
        let before = known.len();
        for (target, expression) in &collector.flows {
            if expr_is_box(expression, &known, environment) {
                known.insert(target.clone());
            }
        }
        if known.len() == before {
            break;
        }
    }

    known
        .difference(&collector.explicit_box_locals)
        .filter(|name| collector.bindings.contains(*name))
        .map(|name| {
            function_slot_key(
                &qualified_function(module, &function.ident.name.to_string()),
                name,
            )
        })
        .collect()
}

fn expr_is_box(
    expression: &Expr,
    known: &BTreeSet<String>,
    environment: &BoxExpressionEnvironment,
) -> bool {
    let expression = expression.peel_parens();
    match &expression.kind {
        ExprKind::Path(_, path) => {
            simple_path_ident(path).is_some_and(|ident| known.contains(&ident))
        }
        ExprKind::Call(callee, arguments) => {
            if is_box_associated_call(callee, "new") {
                return true;
            }
            let ExprKind::Path(_, path) = &callee.kind else {
                return false;
            };
            let Some(last) = path.segments.last() else {
                return false;
            };
            if last.ident.name.as_str() == "Some" {
                return arguments
                    .first()
                    .is_some_and(|argument| expr_is_box(argument, known, environment));
            }
            environment
                .returning_functions
                .contains(&last.ident.name.to_string())
        }
        ExprKind::MethodCall(call) => {
            matches!(call.seg.ident.name.as_str(), "take" | "clone")
                && expr_is_box(&call.receiver, known, environment)
        }
        ExprKind::Field(_, name) => environment.fields.contains(&name.name.to_string()),
        ExprKind::Block(block, _) => block_tail_is_box(block, known, environment),
        ExprKind::If(_, then_branch, else_branch) => {
            block_tail_is_box(then_branch, known, environment)
                || else_branch
                    .as_deref()
                    .is_some_and(|expression| expr_is_box(expression, known, environment))
        }
        ExprKind::Match(_, arms, _) => arms.iter().any(|arm| {
            arm.body
                .as_deref()
                .is_some_and(|body| expr_is_box(body, known, environment))
        }),
        _ => false,
    }
}

fn block_tail_is_box(
    block: &rustc_ast::ast::Block,
    known: &BTreeSet<String>,
    environment: &BoxExpressionEnvironment,
) -> bool {
    block.stmts.last().is_some_and(|statement| {
        let StmtKind::Expr(expression) = &statement.kind else {
            return false;
        };
        expr_is_box(expression, known, environment)
    })
}

fn simple_path_ident(path: &rustc_ast::ast::Path) -> Option<String> {
    let [segment] = path.segments.as_slice() else {
        return None;
    };
    segment
        .args
        .is_none()
        .then(|| segment.ident.name.to_string())
}

fn pat_ident(pat: &Pat) -> Option<String> {
    match &pat.kind {
        PatKind::Ident(_, ident, _) => Some(ident.name.to_string()),
        PatKind::Paren(inner) => pat_ident(inner),
        _ => None,
    }
}

fn is_box_associated_call(callee: &Expr, method: &str) -> bool {
    let ExprKind::Path(_, path) = &callee.kind else {
        return false;
    };
    let mut segments = path.segments.iter().rev();
    let Some(last) = segments.next() else {
        return false;
    };
    last.ident.name.as_str() == method
        && segments
            .next()
            .is_some_and(|segment| segment.ident.name.as_str() == "Box")
}

fn parse_json_document(name: &str, source: &str) -> Result<serde_json::Value, String> {
    serde_json::from_str(source).map_err(|error| format!("{name}: {error}"))
}

fn count_qualifier_scope(
    document: &str,
    root: &serde_json::Value,
    scope: &str,
    expected_labels: &[&str],
    counts: &mut BTreeMap<String, u64>,
    by_depth: &mut Vec<BTreeMap<String, u64>>,
    max_depth: &mut usize,
) -> Result<(), String> {
    let root = root
        .as_object()
        .ok_or_else(|| format!("{document}: root must be an object"))?;
    let owners = root
        .get(scope)
        .ok_or_else(|| format!("{document}: missing {scope}"))?
        .as_object()
        .ok_or_else(|| format!("{document}: {scope} must be an object"))?;
    for (owner, slots) in owners {
        let slots = slots
            .as_object()
            .ok_or_else(|| format!("{document}: {scope}.{owner} must be an object"))?;
        for (slot, labels) in slots {
            let labels = labels
                .as_array()
                .ok_or_else(|| format!("{document}: {scope}.{owner}.{slot} must be an array"))?;
            *max_depth = (*max_depth).max(labels.len());
            if by_depth.len() < labels.len() {
                by_depth.resize_with(labels.len(), BTreeMap::new);
            }
            for (depth, label) in labels.iter().enumerate() {
                let label = label.as_str().ok_or_else(|| {
                    format!("{document}: {scope}.{owner}.{slot}[{depth}] must be a string")
                })?;
                if !expected_labels.contains(&label) {
                    return Err(format!(
                        "{document}: unexpected label {label} at {scope}.{owner}.{slot}[{depth}]"
                    ));
                }
                *counts.entry(label.to_owned()).or_default() += 1;
                *by_depth[depth].entry(label.to_owned()).or_default() += 1;
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reports_parse_errors_through_tool_owned_result() {
        let error: String = analyze_rust_source("fn broken(").unwrap_err();
        assert!(!error.is_empty());
    }

    #[test]
    fn reports_recovered_parse_errors_through_tool_owned_result() {
        let error: String = analyze_rust_source("fn f() { mut x = 1; }").unwrap_err();
        assert!(!error.is_empty());
    }

    #[test]
    fn reuses_existing_rustc_session_globals() {
        rustc_span::create_default_session_globals_then(|| {
            analyze_rust_source("fn f() {}").unwrap();
        });
    }

    #[test]
    fn parses_source_with_the_corpus_edition() {
        analyze_rust_source("fn f() { let gen = 1; let _ = gen; }").unwrap();
    }

    #[test]
    fn excludes_method_receivers_from_function_slot_counts() {
        let source = r#"
            struct Example;

            impl Example {
                fn take(&mut self, value: &u8) {
                    let _ = value;
                }
            }
        "#;

        let counts = analyze_rust_source(source).unwrap();
        assert_eq!(counts.declarations.param_mut_ref, 0);
        assert_eq!(counts.declarations.param_ref, 1);
        assert_eq!(
            counts.reference_function_slot_keys,
            BTreeSet::from(["take::value".to_owned()])
        );
    }

    #[test]
    fn counts_only_declared_box_family_positions_and_real_calls() {
        let source = r#"
            extern "C" {
                fn malloc(size: usize) -> *mut u8;
                fn free(ptr: *mut u8);
            }

            // Box::new(99); free(ptr);
            struct Example {
                plain: Box<u8>,
                optional: core::option::Option<std::boxed::Box<u16>>,
                nested_but_not_a_position: Vec<Box<u32>>,
            }

            fn convert(
                plain: std::boxed::Box<u8>,
                optional: Option<Box<u16>>,
                raw: *mut u8,
            ) -> Option<Box<u32>> {
                let local_plain: Box<u8> = Box::new(1);
                let local_optional: Option<Box<u8>> = Some(Box::new(2));
                let nested_local: Vec<Box<u8>> = Vec::new();
                malloc(1);
                calloc(1, 2);
                realloc(raw, 3);
                free(raw);
                drop(local_plain);
                let _ = (local_optional, nested_local);
                None
            }
        "#;

        let counts = analyze_rust_source(source).unwrap();
        assert_eq!(
            counts.types,
            TypePositionCounts {
                local_box: 1,
                local_option_box: 1,
                param_box: 1,
                param_option_box: 1,
                return_option_box: 1,
                field_box: 1,
                field_option_box: 1,
                ..TypePositionCounts::default()
            }
        );
        assert_eq!(counts.box_new_calls, 2);
        assert_eq!(counts.malloc_calls, 1);
        assert_eq!(counts.calloc_calls, 1);
        assert_eq!(counts.realloc_calls, 1);
        assert_eq!(counts.free_calls, 1);
        assert_eq!(counts.drop_calls, 1);
    }

    #[test]
    fn counts_declaration_families_and_box_expression_evidence() {
        let source = r#"
            struct Example<'a> {
                raw_mut: *mut u8,
                raw_const: *const u8,
                shared: &'a u8,
                mutable: &'a mut u8,
                optional_shared: Option<&'a u8>,
                optional_mutable: Option<&'a mut u8>,
                nested_raw_is_not_outer: Vec<*mut u8>,
                nested_ref_is_not_outer: Vec<&'a u8>,
            }

            type RawAlias = *mut u8;
            type RefAlias<'a> = Option<&'a mut u8>;

            fn make_box() -> Option<Box<u8>> {
                None
            }

            fn convert<'a>(
                raw: *mut u8,
                raw_alias: RawAlias,
                shared: &'a u8,
                optional_mutable: Option<&'a mut u8>,
                reference_alias: RefAlias<'a>,
            ) -> Option<&'a u8> {
                let local_raw: *const u8 = core::ptr::null();
                let local_ref: &u8 = shared;
                let mut inferred_initializer = Some(Box::new(1));
                let mut inferred_assignment = None;
                inferred_assignment = Some(Box::new(2));
                let moved = inferred_initializer.take();
                let from_call = make_box();
                let _nested: Vec<*mut u8> = Vec::new();
                let _ = (
                    raw,
                    raw_alias,
                    local_raw,
                    local_ref,
                    reference_alias,
                    inferred_initializer,
                    inferred_assignment,
                    moved,
                    from_call,
                );
                None
            }
        "#;

        let counts = analyze_rust_source(source).unwrap();
        assert_eq!(
            counts.declarations,
            DeclarationPositionCounts {
                local_raw_const: 1,
                local_ref: 1,
                param_raw_mut: 2,
                param_ref: 1,
                param_option_mut_ref: 2,
                return_option_ref: 1,
                field_raw_mut: 1,
                field_raw_const: 1,
                field_ref: 1,
                field_mut_ref: 1,
                field_option_ref: 1,
                field_option_mut_ref: 1,
                ..DeclarationPositionCounts::default()
            }
        );
        assert_eq!(counts.raw_pointer_type_positions(), 5);
        assert_eq!(counts.reference_family_type_positions(), 9);
        assert_eq!(counts.box_new_local_initializers, 1);
        assert_eq!(counts.box_new_assignment_rhs, 1);
        assert_eq!(counts.box_expression_evidence(), 2);
        assert_eq!(counts.inferred_box_local_slots, 4);
        assert_eq!(counts.box_function_slots(), 4);
        assert_eq!(
            counts.box_function_slot_keys,
            BTreeSet::from([
                "convert::from_call".to_owned(),
                "convert::inferred_assignment".to_owned(),
                "convert::inferred_initializer".to_owned(),
                "convert::moved".to_owned(),
            ])
        );
        assert_eq!(
            counts.reference_function_slot_keys,
            BTreeSet::from([
                "convert::local_ref".to_owned(),
                "convert::optional_mutable".to_owned(),
                "convert::reference_alias".to_owned(),
                "convert::shared".to_owned(),
            ])
        );

        let named = analyze_named_rust_sources(&[("src::sample", source)]).unwrap();
        assert!(named
            .box_function_slot_keys
            .contains("src::sample::convert::inferred_initializer"));
    }

    #[test]
    fn preserves_native_json_labels_and_pointer_depths() {
        let ownership = r#"{
            "fn_data": {"crate::f": {"x": ["Owning", "Unknown"], "y": ["Transient"]}},
            "struct_data": {"crate::S": {"field": ["Owning"]}}
        }"#;
        let statistics = r#"{
            "num_unsafe_ptrs": 3,
            "num_non_arr_unsafe_ptrs": 2,
            "num_mut_unsafe_ptrs": 1,
            "num_non_arr_mut_unsafe_ptrs": 1,
            "num_unsafe_usages": 4,
            "num_non_arr_unsafe_usages": 3,
            "num_mut_unsafe_usages": 2,
            "num_non_arr_mut_unsafe_usages": 1,
            "num_owning_ptrs_detected": 2
        }"#;
        let mutability = r#"{
            "fn_data": {"crate::f": {"x": ["Mut", "Imm"]}},
            "struct_data": {"crate::S": {"field": ["Mut"]}}
        }"#;
        let fatness = r#"{
            "fn_data": {"crate::f": {"x": ["Ptr", "Arr"]}},
            "struct_data": {"crate::S": {"field": ["Ptr"]}}
        }"#;

        let claims = analyze_json_claims(ownership, statistics, mutability, fatness).unwrap();
        assert_eq!(claims.ownership_fn["Owning"], 1);
        assert_eq!(claims.ownership_fn["Unknown"], 1);
        assert_eq!(claims.ownership_fn["Transient"], 1);
        assert_eq!(claims.ownership_struct["Owning"], 1);
        assert_eq!(claims.ownership_fn_by_depth[0]["Owning"], 1);
        assert_eq!(claims.ownership_fn_by_depth[0]["Transient"], 1);
        assert_eq!(claims.ownership_fn_by_depth[1]["Unknown"], 1);
        assert_eq!(claims.ownership_struct_by_depth[0]["Owning"], 1);
        assert_eq!(claims.mutability_fn["Mut"], 1);
        assert_eq!(claims.mutability_fn["Imm"], 1);
        assert_eq!(claims.mutability_fn_by_depth[0]["Mut"], 1);
        assert_eq!(claims.mutability_fn_by_depth[1]["Imm"], 1);
        assert_eq!(claims.fatness_fn["Ptr"], 1);
        assert_eq!(claims.fatness_fn["Arr"], 1);
        assert_eq!(claims.fatness_fn_by_depth[0]["Ptr"], 1);
        assert_eq!(claims.fatness_fn_by_depth[1]["Arr"], 1);
        assert_eq!(claims.statistics["num_owning_ptrs_detected"], 2);
        assert_eq!(claims.fn_d0_mut_ptr, 1);
        assert_eq!(
            claims.fn_d0_mut_ptr_keys,
            BTreeSet::from(["crate::f::x".to_owned()])
        );
        assert_eq!(claims.max_depth, 2);
    }

    #[test]
    fn rejects_structurally_invalid_analysis_json() {
        let missing_scope = r#"{"fn_data": {}}"#;
        let statistics = r#"{
            "num_unsafe_ptrs": 3,
            "num_non_arr_unsafe_ptrs": 2,
            "num_mut_unsafe_ptrs": 1,
            "num_non_arr_mut_unsafe_ptrs": 1,
            "num_unsafe_usages": 4,
            "num_non_arr_unsafe_usages": 3,
            "num_mut_unsafe_usages": 2,
            "num_non_arr_mut_unsafe_usages": 1,
            "num_owning_ptrs_detected": 1
        }"#;
        let valid_qualifier = r#"{"fn_data": {}, "struct_data": {}}"#;

        let error =
            analyze_json_claims(missing_scope, statistics, valid_qualifier, valid_qualifier)
                .unwrap_err();
        let error = error.to_string();
        assert!(error.contains("ownership.json"));
        assert!(error.contains("struct_data"));

        let missing_statistic = statistics.replace(
            r#""num_owning_ptrs_detected": 1"#,
            r#""unexpected_counter": 1"#,
        );
        let error = analyze_json_claims(
            valid_qualifier,
            &missing_statistic,
            valid_qualifier,
            valid_qualifier,
        )
        .unwrap_err();
        let error = error.to_string();
        assert!(error.contains("statistics.json"));
        assert!(error.contains("num_owning_ptrs_detected"));
    }

    #[test]
    fn parses_the_official_evaluation_contract_without_redefining_it() {
        let source = "\
Benchmark Name,#Unsafe Mutable Non-Array Pointers,,,#Unsafe Mutable Non-Array Usages,,
small,1000,500,50.0%,10,5,50.0%
large,1414,1211,14.4%,0,0,NaN%
";

        let rows = parse_official_evaluation(source).expect("official evaluation");
        assert_eq!(rows.len(), 2);
        assert_eq!(rows["small"].declaration_before, 1000);
        assert_eq!(rows["small"].declaration_after, 500);
        assert_eq!(rows["large"].declaration_before, 1414);
        assert_eq!(rows["large"].declaration_after, 1211);
        assert_eq!(rows["small"].usage_before, 10);
        assert_eq!(rows["small"].usage_after, 5);
    }
}
