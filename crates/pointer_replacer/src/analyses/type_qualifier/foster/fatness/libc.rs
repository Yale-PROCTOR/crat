use rustc_hash::FxHashMap;
use rustc_middle::mir::{HasLocalDecls, Local, Operand, Place};
use rustc_span::{Symbol, source_map::Spanned};
use utils::file::{fprintf, fscanf};

use super::{Fatness, place_vars};
use crate::analyses::type_qualifier::foster::{
    StructFields, Var,
    constraint_system::{BooleanSystem, ConstraintSystem},
};

#[allow(clippy::too_many_arguments)]
pub fn libc_call<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    callee: Symbol,
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    string_literals: &FxHashMap<Local, &[u8]>,
    database: &mut BooleanSystem<Fatness>,
) {
    match callee.as_str() {
        // dest is fat, all ptr args are fat
        "strstr" | "strtok" => {
            mark_dest_and_args_bottom(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                database,
            );
        }
        // dest is fat, first 2 ptr args are fat
        "memcpy" | "memmove" | "strcat" | "strncat" | "strcpy" | "strncpy" => {
            mark_dest_and_args_bottom(
                destination,
                &args[..2.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
        }
        // dest is fat, first ptr arg is fat
        "memset" | "realloc" | "strchr" | "strrchr" => {
            mark_dest_and_args_bottom(
                destination,
                &args[..1.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
        }
        // all ptr args are fat, no dest effect
        "strcmp" | "strcasecmp" | "strcspn" => {
            mark_args_bottom(args, local_decls, locals, struct_fields, database);
        }
        // first 2 ptr args are fat (third arg is size_t), no dest effect
        "strncmp" | "strncasecmp" | "memcmp" => {
            mark_args_bottom(
                &args[..2.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
        }
        // first ptr arg is fat, no dest effect
        "strlen" | "strdup" | "atoi" | "atof" | "fgets" | "fputs" | "puts" | "fread" | "fwrite"
        | "getenv" => {
            mark_args_bottom(
                &args[..1.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
        }
        // TODO generate constraints when the first argument is not 1
        "calloc" => {
            let dest_vars = place_vars(destination, local_decls, locals, struct_fields);
            assert!(!dest_vars.is_empty());
        }
        // first arg is a fat buffer, rest are printf-like
        "sprintf" => {
            mark_args_bottom(
                &args[..1.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
            call_printf(
                &args[1..],
                local_decls,
                locals,
                struct_fields,
                string_literals,
                database,
            );
        }
        // first arg is a fat buffer, second is size, rest are printf-like
        "snprintf" => {
            mark_args_bottom(
                &args[..1.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
            call_printf(
                &args[2..],
                local_decls,
                locals,
                struct_fields,
                string_literals,
                database,
            );
        }
        "printf" => call_printf(
            args,
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "fprintf" => call_printf(
            &args[1..],
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "scanf" => call_scanf(
            args,
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "fscanf" => call_scanf(
            &args[1..],
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "sscanf" => {
            mark_args_bottom(
                &args[..1.min(args.len())],
                local_decls,
                locals,
                struct_fields,
                database,
            );
            call_scanf(
                &args[1..],
                local_decls,
                locals,
                struct_fields,
                string_literals,
                database,
            );
        }
        _ => {}
    }
}

fn mark_dest_and_args_bottom<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let dest_vars = place_vars(destination, local_decls, locals, struct_fields);
    assert!(!dest_vars.is_empty());
    database.bottom(dest_vars.start);

    mark_args_bottom(args, local_decls, locals, struct_fields, database);
}

fn mark_args_bottom<'tcx>(
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    for ptr in args.iter().filter_map(|arg| arg.node.place()) {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_printf<'tcx>(
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    string_literals: &FxHashMap<Local, &[u8]>,
    database: &mut BooleanSystem<Fatness>,
) {
    let [fmt, args @ ..] = args else { panic!() };
    if let Some(lit) = string_literals.get(&fmt.node.place().unwrap().local) {
        let specs = fprintf::parse_specs(lit);
        for (arg, spec) in args.iter().zip(specs) {
            if spec.conversion != fprintf::Conversion::Str {
                continue;
            }
            let Some(ptr) = arg.node.place() else { continue };
            if !local_decls.local_decls()[ptr.local].ty.is_raw_ptr() {
                continue;
            }
            let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
            assert!(!ptr_vars.is_empty());
            database.bottom(ptr_vars.start);
        }
    }
}

fn call_scanf<'tcx>(
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    string_literals: &FxHashMap<Local, &[u8]>,
    database: &mut BooleanSystem<Fatness>,
) {
    let [fmt, args @ ..] = args else { panic!() };
    if let Some(lit) = string_literals.get(&fmt.node.place().unwrap().local) {
        let specs = fscanf::parse_specs(lit);
        for (arg, spec) in args.iter().zip(specs) {
            if !matches!(
                spec.conversion,
                fscanf::Conversion::Str | fscanf::Conversion::ScanSet(_)
            ) {
                continue;
            }
            let Some(ptr) = arg.node.place() else { continue };
            if !local_decls.local_decls()[ptr.local].ty.is_raw_ptr() {
                continue;
            }
            let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
            assert!(!ptr_vars.is_empty());
            database.bottom(ptr_vars.start);
        }
    }
}
