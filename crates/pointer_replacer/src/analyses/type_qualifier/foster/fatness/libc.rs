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
        // malloc is skipped
        // "malloc" => {},
        // free is skipped
        // "free" => {},
        "strlen" => call_strlen(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "strstr" => call_strstr(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "strcmp" => call_strcmp(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "strncat" => call_strncat(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "memcpy" => call_memcpy(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "memmove" => call_memmove(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "memset" => call_memset(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "calloc" => call_calloc(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "realloc" => call_realloc(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        "atoi" | "atof" | "fgets" | "fputs" | "puts" | "fread" | "fwrite" => {
            call_fn_with_array_arg(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                database,
                &[0],
            )
        }
        "printf" => call_printf(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "fprintf" => call_printf(
            destination,
            &args[1..],
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "scanf" => call_scanf(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        "fscanf" => call_scanf(
            destination,
            &args[1..],
            local_decls,
            locals,
            struct_fields,
            string_literals,
            database,
        ),
        fn_name if fn_name.starts_with("str") => call_str_general(
            destination,
            args,
            local_decls,
            locals,
            struct_fields,
            database,
        ),
        _ => {}
    }
}

fn call_str_general<'tcx>(
    _destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    for ptr in args.iter().filter_map(|arg| arg.node.place()) {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        if !ptr_vars.is_empty() {
            database.bottom(ptr_vars.start);
        }
    }
}

/// TODO generate constraints when the first argument is not 1
fn call_calloc<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let dest_vars = place_vars(destination, local_decls, locals, struct_fields);
    assert!(dest_vars.end > dest_vars.start);
    // database.bottom(dest_vars.start);
    let _ = dest_vars;
    let _ = database;
    let _ = args;
}

fn call_realloc<'tcx>(
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
    let ptr = &args[0];
    if let Some(ptr) = ptr.node.place() {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_strlen<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let _ = destination;
    let ptr = &args[0];
    if let Some(ptr) = ptr.node.place() {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_strstr<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let dest_vars = place_vars(destination, local_decls, locals, struct_fields);
    assert!(dest_vars.end > dest_vars.start);
    database.bottom(dest_vars.start);

    for ptr in args.iter().filter_map(|arg| arg.node.place()) {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_strcmp<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let _ = destination;

    for ptr in args.iter().filter_map(|arg| arg.node.place()) {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_strncat<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let dest_vars = place_vars(destination, local_decls, locals, struct_fields);
    assert!(dest_vars.end > dest_vars.start);
    database.bottom(dest_vars.start);

    for ptr in args.iter().take(2).filter_map(|arg| arg.node.place()) {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_memcpy<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    call_strncat(
        destination,
        args,
        local_decls,
        locals,
        struct_fields,
        database,
    )
}

fn call_memmove<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    call_memcpy(
        destination,
        args,
        local_decls,
        locals,
        struct_fields,
        database,
    )
}

fn call_memset<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
) {
    let dest_vars = place_vars(destination, local_decls, locals, struct_fields);
    assert!(dest_vars.end > dest_vars.start);
    database.bottom(dest_vars.start);

    let ptr = &args[0];
    if let Some(ptr) = ptr.node.place() {
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_fn_with_array_arg<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    database: &mut BooleanSystem<Fatness>,
    indices: &[usize],
) {
    let _ = destination;

    for i in indices {
        let arg = &args[*i];
        let Some(ptr) = arg.node.place() else { return };
        let ptr_vars = place_vars(&ptr, local_decls, locals, struct_fields);
        assert!(!ptr_vars.is_empty());
        database.bottom(ptr_vars.start);
    }
}

fn call_printf<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    string_literals: &FxHashMap<Local, &[u8]>,
    database: &mut BooleanSystem<Fatness>,
) {
    let _ = destination;

    let [fmt, args @ ..] = args else { panic!() };
    let lit = string_literals[&fmt.node.place().unwrap().local];
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

fn call_scanf<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    string_literals: &FxHashMap<Local, &[u8]>,
    database: &mut BooleanSystem<Fatness>,
) {
    let _ = destination;

    let [fmt, args @ ..] = args else { panic!() };
    let lit = string_literals[&fmt.node.place().unwrap().local];
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
