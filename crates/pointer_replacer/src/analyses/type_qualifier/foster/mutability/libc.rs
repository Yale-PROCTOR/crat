use rustc_middle::{
    mir::{HasLocalDecls, Operand, Place},
    ty::TyCtxt,
};
use rustc_span::{Symbol, source_map::Spanned};

use super::{EnsureNoDeref, MutCtxt, Mutability, conservative_call, place_vars};
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
    tcx: TyCtxt<'tcx>,
    database: &mut BooleanSystem<Mutability>,
) {
    match callee.as_str() {
        // _1 flows to _0
        "strchr" | "strrchr" | "strstr" => {
            call_strchr(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                tcx,
                database,
            );
        }
        // _1 is mutated
        "sprintf" | "snprintf" | "regcomp" => {
            call_sprintf(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                tcx,
                database,
            );
        }
        // _1 is mutated, _1 flows to _0
        "memcpy" | "memmove" | "memset" | "strcat" | "strncat" | "strcpy" | "strncpy"
        | "strtok" => {
            call_memcpy(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                tcx,
                database,
            );
        }
        // _1 and onwards are mutated
        "scanf" => {
            call_scanf::<1>(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                tcx,
                database,
            );
        }
        // _2 and onwards are mutated
        "fscanf" | "sscanf" => {
            call_scanf::<2>(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                tcx,
                database,
            );
        }
        "strlen" | "strdup" | "strcmp" | "strcasecmp" | "strncmp" | "strncasecmp" | "strcspn"
        | "atoi" | "atof" | "printf" | "fprintf" | "fdopen" | "fopen" | "regerror" | "regexec"
        | "regfree" | "getenv" | "realloc" | "free" | "memcmp" => {}
        _ => {
            conservative_call(
                destination,
                args,
                local_decls,
                locals,
                struct_fields,
                tcx,
                database,
            );
        }
    }
}

fn call_memcpy<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: TyCtxt<'tcx>,
    database: &mut BooleanSystem<Mutability>,
) {
    let dest_vars = place_vars::<MutCtxt>(
        destination,
        local_decls,
        locals,
        struct_fields,
        tcx,
        database,
    );
    if let Some(memcpy_dest) = args[0].node.place() {
        let memcpy_dest = place_vars::<EnsureNoDeref>(
            &memcpy_dest,
            local_decls,
            locals,
            struct_fields,
            tcx,
            &mut (),
        );

        assert!(memcpy_dest.end > memcpy_dest.start);
        database.bottom(memcpy_dest.start);

        let mut lhs_rhs = dest_vars.zip(memcpy_dest);
        if let Some((lhs, rhs)) = lhs_rhs.next() {
            database.guard(lhs, rhs);
        }
        for (lhs, rhs) in lhs_rhs {
            database.guard(lhs, rhs);
            database.guard(rhs, lhs)
        }
    }
}

fn call_strchr<'tcx>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: TyCtxt<'tcx>,
    database: &mut BooleanSystem<Mutability>,
) {
    let dest_vars = place_vars::<MutCtxt>(
        destination,
        local_decls,
        locals,
        struct_fields,
        tcx,
        database,
    );

    if let Some(arg) = args[0].node.place() {
        let arg_vars =
            place_vars::<EnsureNoDeref>(&arg, local_decls, locals, struct_fields, tcx, &mut ());
        let mut dest_arg = dest_vars.zip(arg_vars);

        if let Some((dest, arg)) = dest_arg.next() {
            database.guard(dest, arg)
        }
        for (dest, arg) in dest_arg {
            database.guard(arg, dest);
            database.guard(dest, arg);
        }
    }
}

fn call_sprintf<'tcx>(
    _destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: TyCtxt<'tcx>,
    database: &mut BooleanSystem<Mutability>,
) {
    if let Some(arg) = args[0].node.place() {
        let arg =
            place_vars::<EnsureNoDeref>(&arg, local_decls, locals, struct_fields, tcx, &mut ());

        assert!(arg.end > arg.start);
        database.bottom(arg.start);
    }
}

fn call_scanf<'tcx, const MUT_START: usize>(
    destination: &Place<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    local_decls: &impl HasLocalDecls<'tcx>,
    locals: &[Var],
    struct_fields: &StructFields,
    tcx: TyCtxt<'tcx>,
    database: &mut BooleanSystem<Mutability>,
) {
    let dest_vars = place_vars::<MutCtxt>(
        destination,
        local_decls,
        locals,
        struct_fields,
        tcx,
        database,
    );
    assert!(dest_vars.is_empty());
    for arg in &args[MUT_START..] {
        if let Some(arg) = arg.node.place() {
            let arg =
                place_vars::<EnsureNoDeref>(&arg, local_decls, locals, struct_fields, tcx, &mut ());

            assert!(arg.end > arg.start);
            database.bottom(arg.start);
        }
    }
}
