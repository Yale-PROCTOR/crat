use super::run_ownership_case_with_box_candidates;

const SOURCE: &str = r####"
#![warn(mutable_transmutes)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(c_variadic)]
#![feature(extern_types)]
#![feature(linkage)]
#![feature(rustc_private)]
#![feature(thread_local)]
#![feature(builtin_syntax)]
#![feature(core_intrinsics)]
#![feature(derive_clone_copy)]
#![feature(hint_must_use)]
#![feature(panic_internals)]
pub mod src {
    pub mod lib {
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
        }
        pub type size_t = usize;
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        #[repr(C)]
        pub struct _IO_FILE {
            pub _flags: core::ffi::c_int,
            pub _IO_read_ptr: *mut core::ffi::c_char,
            pub _IO_read_end: *mut core::ffi::c_char,
            pub _IO_read_base: *mut core::ffi::c_char,
            pub _IO_write_base: *mut core::ffi::c_char,
            pub _IO_write_ptr: *mut core::ffi::c_char,
            pub _IO_write_end: *mut core::ffi::c_char,
            pub _IO_buf_base: *mut core::ffi::c_char,
            pub _IO_buf_end: *mut core::ffi::c_char,
            pub _IO_save_base: *mut core::ffi::c_char,
            pub _IO_backup_base: *mut core::ffi::c_char,
            pub _IO_save_end: *mut core::ffi::c_char,
            pub _markers: *mut _IO_marker,
            pub _chain: *mut _IO_FILE,
            pub _fileno: core::ffi::c_int,
            pub _flags2: core::ffi::c_int,
            pub _old_offset: __off_t,
            pub _cur_column: core::ffi::c_ushort,
            pub _vtable_offset: core::ffi::c_schar,
            pub _shortbuf: [core::ffi::c_char; 1],
            pub _lock: *mut core::ffi::c_void,
            pub _offset: __off64_t,
            pub _codecvt: *mut _IO_codecvt,
            pub _wide_data: *mut _IO_wide_data,
            pub _freeres_list: *mut _IO_FILE,
            pub _freeres_buf: *mut core::ffi::c_void,
            pub __pad5: size_t,
            pub _mode: core::ffi::c_int,
            pub _unused2: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for _IO_FILE {}
        #[automatically_derived]
        impl ::core::clone::Clone for _IO_FILE {
            #[inline]
            fn clone(&self) -> _IO_FILE {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_marker>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_ushort>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_schar>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 1]>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<__off64_t>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_codecvt>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_wide_data>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        pub type _IO_lock_t = ();
        pub type FILE = _IO_FILE;
        #[repr(C)]
        pub struct node_t {
            pub city_name: [core::ffi::c_char; 64],
            pub ref_count: core::ffi::c_int,
            pub edges: [edge_t; 10],
            pub edge_count: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for node_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for node_t {
            #[inline]
            fn clone(&self) -> node_t {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 64]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[edge_t; 10]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct edge_t {
            pub destination: *mut node_t,
            pub distance: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for edge_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for edge_t {
            #[inline]
            fn clone(&self) -> edge_t {
                let _: ::core::clone::AssertParamIsClone<*mut node_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct graph_t {
            pub nodes: [*mut node_t; 100],
            pub node_count: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for graph_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for graph_t {
            #[inline]
            fn clone(&self) -> graph_t {
                let _: ::core::clone::AssertParamIsClone<[*mut node_t; 100]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct dijkstra_node_t {
            pub node: *mut node_t,
            pub distance: core::ffi::c_int,
            pub previous: *mut node_t,
            pub visited: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for dijkstra_node_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for dijkstra_node_t {
            #[inline]
            fn clone(&self) -> dijkstra_node_t {
                let _: ::core::clone::AssertParamIsClone<*mut node_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut node_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_CITY_NAME: core::ffi::c_int = 64 as core::ffi::c_int;
        pub const MAX_EDGES: core::ffi::c_int = 10 as core::ffi::c_int;
        pub const MAX_NODES: core::ffi::c_int = 100 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn create_graph() -> *mut graph_t {
            let graph: *mut graph_t =
                malloc(::core::mem::size_of::<graph_t>() as size_t) as *mut graph_t;
            if graph.is_null() {
                fprintf(
                    stderr,
                    b"Error: Failed to allocate graph\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<graph_t>();
            }
            (*graph).node_count = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < MAX_NODES {
                (*graph).nodes[i as usize] = std::ptr::null_mut::<node_t>();
                i += 1;
            }
            graph
        }
        #[no_mangle]
        pub unsafe extern "C" fn add_node(
            graph: *mut graph_t,
            city_name: *const core::ffi::c_char,
        ) -> *mut node_t {
            if graph.is_null() || city_name.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL parameter in add_node\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<node_t>();
            }
            if (*graph).node_count >= MAX_NODES {
                fprintf(
                    stderr,
                    b"Error: Graph is full (max %d nodes)\n\0" as *const u8
                        as *const core::ffi::c_char,
                    MAX_NODES,
                );
                return std::ptr::null_mut::<node_t>();
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*graph).node_count {
                if strcmp(
                    ((*(*graph).nodes[i as usize]).city_name).as_ptr(),
                    city_name,
                ) == 0 as core::ffi::c_int
                {
                    fprintf(
                        stderr,
                        b"Error: Node '%s' already exists\n\0" as *const u8
                            as *const core::ffi::c_char,
                        city_name,
                    );
                    return std::ptr::null_mut::<node_t>();
                }
                i += 1;
            }
            let node: *mut node_t =
                malloc(::core::mem::size_of::<node_t>() as size_t) as *mut node_t;
            if node.is_null() {
                fprintf(
                    stderr,
                    b"Error: Failed to allocate node\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<node_t>();
            }
            strncpy(
                ((*node).city_name).as_mut_ptr(),
                city_name,
                (MAX_CITY_NAME - 1 as core::ffi::c_int) as size_t,
            );
            (*node).city_name[(MAX_CITY_NAME - 1 as core::ffi::c_int) as usize] =
                '\0' as i32 as core::ffi::c_char;
            (*node).ref_count = 1 as core::ffi::c_int;
            (*node).edge_count = 0 as core::ffi::c_int;
            let fresh0 = (*graph).node_count;
            (*graph).node_count += 1;
            (*graph).nodes[fresh0 as usize] = node;
            node
        }
        #[no_mangle]
        pub unsafe extern "C" fn add_edge(
            from: *mut node_t,
            to: *mut node_t,
            distance: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if from.is_null() || to.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL node in add_edge\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            if (*from).edge_count >= MAX_EDGES {
                fprintf(
                    stderr,
                    b"Error: Node '%s' has maximum edges\n\0" as *const u8
                        as *const core::ffi::c_char,
                    ((*from).city_name).as_ptr(),
                );
                return -(1 as core::ffi::c_int);
            }
            if distance < 0 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error: Negative distance not allowed\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*from).edge_count {
                if (*from).edges[i as usize].destination == to {
                    fprintf(
                        stderr,
                        b"Error: Edge already exists\n\0" as *const u8 as *const core::ffi::c_char,
                    );
                    return -(1 as core::ffi::c_int);
                }
                i += 1;
            }
            (*from).edges[(*from).edge_count as usize].destination = to;
            (*from).edges[(*from).edge_count as usize].distance = distance;
            (*from).edge_count += 1;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn delete_node(node: *mut node_t) {
            if node.is_null() {
                return;
            }
            (*node).ref_count -= 1;
            if (*node).ref_count == 0 as core::ffi::c_int {
                free(node as *mut core::ffi::c_void);
            }
        }
        unsafe extern "C" fn increment_refs_recursive(
            node: *mut node_t,
            visited: *mut *mut node_t,
            visited_count: *mut core::ffi::c_int,
        ) {
            if node.is_null() {
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < *visited_count {
                if *visited.offset(i as isize) == node {
                    return;
                }
                i += 1;
            }
            if *visited_count < MAX_NODES {
                let fresh1 = *visited_count;
                *visited_count += 1;
                *visited.offset(fresh1 as isize) = node;
            }
            (*node).ref_count += 1;
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < (*node).edge_count {
                increment_refs_recursive(
                    (*node).edges[i_0 as usize].destination,
                    visited,
                    visited_count,
                );
                i_0 += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn shallow_copy(start: *mut node_t) -> *mut node_t {
            if start.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL node in shallow_copy\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<node_t>();
            }
            let mut visited: [*mut node_t; 100] = [std::ptr::null_mut::<node_t>(); 100];
            let mut visited_count: core::ffi::c_int = 0 as core::ffi::c_int;
            increment_refs_recursive(start, visited.as_mut_ptr(), &mut visited_count);
            start
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_shortest_path(
            start: *mut node_t,
            end: *mut node_t,
            path_length: *mut core::ffi::c_int,
        ) -> *mut *mut node_t {
            if start.is_null() || end.is_null() || path_length.is_null() {
                fprintf(
                    stderr,
                    b"Error: NULL parameter in find_shortest_path\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<*mut node_t>();
            }
            let mut state: [dijkstra_node_t; 100] = [dijkstra_node_t {
                node: std::ptr::null_mut::<node_t>(),
                distance: 0,
                previous: std::ptr::null_mut::<node_t>(),
                visited: 0,
            }; 100];
            let mut state_count: core::ffi::c_int = 0 as core::ffi::c_int;
            state[state_count as usize].node = start;
            state[state_count as usize].distance = 0 as core::ffi::c_int;
            state[state_count as usize].previous = std::ptr::null_mut::<node_t>();
            state[state_count as usize].visited = 0 as core::ffi::c_int;
            state_count += 1;
            let mut current: *mut node_t = start;
            while !current.is_null() {
                let mut current_idx: core::ffi::c_int = -(1 as core::ffi::c_int);
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < state_count {
                    if state[i as usize].node == current {
                        current_idx = i;
                        break;
                    } else {
                        i += 1;
                    }
                }
                if current_idx == -(1 as core::ffi::c_int) {
                    break;
                }
                state[current_idx as usize].visited = 1 as core::ffi::c_int;
                if current == end {
                    break;
                }
                let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
                while i_0 < (*current).edge_count {
                    let neighbor: *mut node_t = (*current).edges[i_0 as usize].destination;
                    let new_distance: core::ffi::c_int = state[current_idx as usize].distance
                        + (*current).edges[i_0 as usize].distance;
                    let mut neighbor_idx: core::ffi::c_int = -(1 as core::ffi::c_int);
                    let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                    while j < state_count {
                        if state[j as usize].node == neighbor {
                            neighbor_idx = j;
                            break;
                        } else {
                            j += 1;
                        }
                    }
                    if neighbor_idx == -(1 as core::ffi::c_int) && state_count < MAX_NODES {
                        neighbor_idx = state_count;
                        state[state_count as usize].node = neighbor;
                        state[state_count as usize].distance = INT_MAX;
                        state[state_count as usize].previous = std::ptr::null_mut::<node_t>();
                        state[state_count as usize].visited = 0 as core::ffi::c_int;
                        state_count += 1;
                    }
                    if neighbor_idx != -(1 as core::ffi::c_int)
                        && new_distance < state[neighbor_idx as usize].distance
                    {
                        state[neighbor_idx as usize].distance = new_distance;
                        state[neighbor_idx as usize].previous = current;
                    }
                    i_0 += 1;
                }
                let mut min_distance: core::ffi::c_int = INT_MAX;
                current = std::ptr::null_mut::<node_t>();
                let mut i_1: core::ffi::c_int = 0 as core::ffi::c_int;
                while i_1 < state_count {
                    if state[i_1 as usize].visited == 0
                        && state[i_1 as usize].distance < min_distance
                    {
                        min_distance = state[i_1 as usize].distance;
                        current = state[i_1 as usize].node;
                    }
                    i_1 += 1;
                }
            }
            let mut end_idx: core::ffi::c_int = -(1 as core::ffi::c_int);
            let mut i_2: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_2 < state_count {
                if state[i_2 as usize].node == end {
                    end_idx = i_2;
                    break;
                } else {
                    i_2 += 1;
                }
            }
            if end_idx == -(1 as core::ffi::c_int) || state[end_idx as usize].distance == INT_MAX {
                fprintf(
                    stderr,
                    b"No path found\n\0" as *const u8 as *const core::ffi::c_char,
                );
                *path_length = 0 as core::ffi::c_int;
                return std::ptr::null_mut::<*mut node_t>();
            }
            let mut path: [*mut node_t; 100] = [std::ptr::null_mut::<node_t>(); 100];
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut current_node: *mut node_t = end;
            while !current_node.is_null() {
                let fresh3 = count;
                count += 1;
                path[fresh3 as usize] = current_node;
                let mut current_state_idx: core::ffi::c_int = -(1 as core::ffi::c_int);
                let mut i_3: core::ffi::c_int = 0 as core::ffi::c_int;
                while i_3 < state_count {
                    if state[i_3 as usize].node == current_node {
                        current_state_idx = i_3;
                        break;
                    } else {
                        i_3 += 1;
                    }
                }
                if current_state_idx == -(1 as core::ffi::c_int) {
                    break;
                }
                current_node = state[current_state_idx as usize].previous;
            }
            let result: *mut *mut node_t = malloc(
                (::core::mem::size_of::<*mut node_t>() as size_t).wrapping_mul(count as size_t),
            ) as *mut *mut node_t;
            if result.is_null() {
                fprintf(
                    stderr,
                    b"Error: Failed to allocate path\n\0" as *const u8 as *const core::ffi::c_char,
                );
                *path_length = 0 as core::ffi::c_int;
                return std::ptr::null_mut::<*mut node_t>();
            }
            let mut i_4: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_4 < count {
                *result.offset(i_4 as isize) = path[(count - 1 as core::ffi::c_int - i_4) as usize];
                i_4 += 1;
            }
            *path_length = count;
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_node_by_name(
            graph: *mut graph_t,
            city_name: *const core::ffi::c_char,
        ) -> *mut node_t {
            if graph.is_null() || city_name.is_null() {
                return std::ptr::null_mut::<node_t>();
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*graph).node_count {
                if strcmp(
                    ((*(*graph).nodes[i as usize]).city_name).as_ptr(),
                    city_name,
                ) == 0 as core::ffi::c_int
                {
                    return (*graph).nodes[i as usize];
                }
                i += 1;
            }
            std::ptr::null_mut::<node_t>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_node(node: *mut node_t) {
            if node.is_null() {
                printf(b"NULL node\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"City: %s (ref_count: %d)\n\0" as *const u8 as *const core::ffi::c_char,
                ((*node).city_name).as_ptr(),
                (*node).ref_count,
            );
            printf(b"  Edges:\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*node).edge_count {
                printf(
                    b"    -> %s (distance: %d)\n\0" as *const u8 as *const core::ffi::c_char,
                    ((*(*node).edges[i as usize].destination).city_name).as_ptr(),
                    (*node).edges[i as usize].distance,
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_graph(graph: *mut graph_t) {
            if graph.is_null() {
                printf(b"NULL graph\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Graph with %d nodes:\n\0" as *const u8 as *const core::ffi::c_char,
                (*graph).node_count,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*graph).node_count {
                print_node((*graph).nodes[i as usize]);
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn free_graph(graph: *mut graph_t) {
            if graph.is_null() {
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*graph).node_count {
                delete_node((*graph).nodes[i as usize]);
                i += 1;
            }
            free(graph as *mut core::ffi::c_void);
        }
        pub const __INT_MAX__: core::ffi::c_int = 2147483647 as core::ffi::c_int;
        pub const INT_MAX: core::ffi::c_int = __INT_MAX__;
    }
    pub mod main {
        use crate::src::lib::add_edge;
        use crate::src::lib::add_node;
        use crate::src::lib::create_graph;
        use crate::src::lib::delete_node;
        use crate::src::lib::find_shortest_path;
        use crate::src::lib::free_graph;
        use crate::src::lib::get_node_by_name;
        use crate::src::lib::graph_t;
        use crate::src::lib::node_t;
        use crate::src::lib::print_graph;
        use crate::src::lib::print_node;
        use crate::src::lib::shallow_copy;
        use crate::src::lib::FILE;
        extern "C" {
            static mut stdin: *mut FILE;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn sscanf(
                __s: *const core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strcspn(
                __s: *const core::ffi::c_char,
                __reject: *const core::ffi::c_char,
            ) -> core::ffi::c_ulong;
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_INPUT: core::ffi::c_int = 256 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn print_menu() {
            printf(
                b"\n=== DAG City Route Manager ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(b"1. Add city (node)\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"2. Add route (edge)\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"3. Show all cities\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"4. Show city details\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"5. Find shortest path\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"6. Make shallow copy of subsection\n\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(b"7. Delete node\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"8. Exit\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"Choice: \0" as *const u8 as *const core::ffi::c_char);
        }
        unsafe fn main_0() -> core::ffi::c_int {
            let graph: *mut graph_t = create_graph();
            if graph.is_null() {
                fprintf(
                    stderr,
                    b"Failed to create graph\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return 1 as core::ffi::c_int;
            }
            let mut input: [core::ffi::c_char; 256] = [0; 256];
            let mut choice: core::ffi::c_int = 0;
            printf(b"City Route Management System\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"Commands are read from stdin\n\0" as *const u8 as *const core::ffi::c_char);
            loop {
                print_menu();
                if (fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                    break;
                }
                if sscanf(
                    input.as_ptr(),
                    b"%d\0" as *const u8 as *const core::ffi::c_char,
                    &mut choice as *mut core::ffi::c_int,
                ) != 1 as core::ffi::c_int
                {
                    printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                } else {
                    match choice {
                        1 => {
                            printf(b"Enter city name: \0" as *const u8 as *const core::ffi::c_char);
                            if !(fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                input[strcspn(
                                    input.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                let node: *mut node_t = add_node(graph, input.as_ptr());
                                if !node.is_null() {
                                    printf(
                                        b"Added city: %s\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                        input.as_ptr(),
                                    );
                                } else {
                                    printf(
                                        b"Failed to add city\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                    );
                                }
                            }
                        }
                        2 => {
                            let mut from_city: [core::ffi::c_char; 256] = [0; 256];
                            let mut to_city: [core::ffi::c_char; 256] = [0; 256];
                            let mut distance: core::ffi::c_int = 0;
                            printf(b"Enter from city: \0" as *const u8 as *const core::ffi::c_char);
                            if !(fgets(from_city.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                from_city[strcspn(
                                    from_city.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                printf(
                                    b"Enter to city: \0" as *const u8 as *const core::ffi::c_char,
                                );
                                if !(fgets(to_city.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                    to_city[strcspn(
                                        to_city.as_ptr(),
                                        b"\n\0" as *const u8 as *const core::ffi::c_char,
                                    ) as usize] = 0 as core::ffi::c_char;
                                    printf(
                                        b"Enter distance: \0" as *const u8
                                            as *const core::ffi::c_char,
                                    );
                                    if !(fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                        if sscanf(
                                            input.as_ptr(),
                                            b"%d\0" as *const u8 as *const core::ffi::c_char,
                                            &mut distance as *mut core::ffi::c_int,
                                        ) != 1 as core::ffi::c_int
                                        {
                                            printf(
                                                b"Invalid distance\n\0" as *const u8
                                                    as *const core::ffi::c_char,
                                            );
                                        } else {
                                            let from: *mut node_t =
                                                get_node_by_name(graph, from_city.as_ptr());
                                            let to: *mut node_t =
                                                get_node_by_name(graph, to_city.as_ptr());
                                            if from.is_null() {
                                                printf(
                                                    b"City '%s' not found\n\0" as *const u8
                                                        as *const core::ffi::c_char,
                                                    from_city.as_ptr(),
                                                );
                                            } else if to.is_null() {
                                                printf(
                                                    b"City '%s' not found\n\0" as *const u8
                                                        as *const core::ffi::c_char,
                                                    to_city.as_ptr(),
                                                );
                                            } else if add_edge(from, to, distance)
                                                == 0 as core::ffi::c_int
                                            {
                                                printf(
                                                    b"Added route: %s -> %s (distance: %d)\n\0"
                                                        as *const u8
                                                        as *const core::ffi::c_char,
                                                    from_city.as_ptr(),
                                                    to_city.as_ptr(),
                                                    distance,
                                                );
                                            } else {
                                                printf(
                                                    b"Failed to add route\n\0" as *const u8
                                                        as *const core::ffi::c_char,
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        3 => {
                            print_graph(graph);
                        }
                        4 => {
                            printf(b"Enter city name: \0" as *const u8 as *const core::ffi::c_char);
                            if !(fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                input[strcspn(
                                    input.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                let node_0: *mut node_t = get_node_by_name(graph, input.as_ptr());
                                if !node_0.is_null() {
                                    print_node(node_0);
                                } else {
                                    printf(
                                        b"City '%s' not found\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                        input.as_ptr(),
                                    );
                                }
                            }
                        }
                        5 => {
                            let mut start_city: [core::ffi::c_char; 256] = [0; 256];
                            let mut end_city: [core::ffi::c_char; 256] = [0; 256];
                            printf(
                                b"Enter start city: \0" as *const u8 as *const core::ffi::c_char,
                            );
                            if !(fgets(start_city.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                start_city[strcspn(
                                    start_city.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                printf(
                                    b"Enter end city: \0" as *const u8 as *const core::ffi::c_char,
                                );
                                if !(fgets(end_city.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                    end_city[strcspn(
                                        end_city.as_ptr(),
                                        b"\n\0" as *const u8 as *const core::ffi::c_char,
                                    ) as usize] = 0 as core::ffi::c_char;
                                    let start: *mut node_t =
                                        get_node_by_name(graph, start_city.as_ptr());
                                    let end: *mut node_t =
                                        get_node_by_name(graph, end_city.as_ptr());
                                    if start.is_null() {
                                        printf(
                                            b"City '%s' not found\n\0" as *const u8
                                                as *const core::ffi::c_char,
                                            start_city.as_ptr(),
                                        );
                                    } else if end.is_null() {
                                        printf(
                                            b"City '%s' not found\n\0" as *const u8
                                                as *const core::ffi::c_char,
                                            end_city.as_ptr(),
                                        );
                                    } else {
                                        let mut path_length: core::ffi::c_int = 0;
                                        let path: *mut *mut node_t =
                                            find_shortest_path(start, end, &mut path_length);
                                        if !path.is_null() {
                                            printf(
                                                b"Shortest path from %s to %s:\n\0" as *const u8
                                                    as *const core::ffi::c_char,
                                                start_city.as_ptr(),
                                                end_city.as_ptr(),
                                            );
                                            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                                            while i < path_length {
                                                printf(
                                                    b"  %d. %s\n\0" as *const u8
                                                        as *const core::ffi::c_char,
                                                    i + 1 as core::ffi::c_int,
                                                    ((**path.offset(i as isize)).city_name)
                                                        .as_ptr(),
                                                );
                                                i += 1;
                                            }
                                            free(path as *mut core::ffi::c_void);
                                        } else {
                                            printf(
                                                b"No path found\n\0" as *const u8
                                                    as *const core::ffi::c_char,
                                            );
                                        }
                                    }
                                }
                            }
                        }
                        6 => {
                            printf(
                                b"Enter start city for shallow copy: \0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            if !(fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                input[strcspn(
                                    input.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                let node_1: *mut node_t = get_node_by_name(graph, input.as_ptr());
                                if node_1.is_null() {
                                    printf(
                                        b"City '%s' not found\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                        input.as_ptr(),
                                    );
                                } else {
                                    let copy: *mut node_t = shallow_copy(node_1);
                                    if !copy.is_null() {
                                        printf(
                                            b"Created shallow copy starting from %s\n\0"
                                                as *const u8
                                                as *const core::ffi::c_char,
                                            input.as_ptr(),
                                        );
                                        printf(b"Reference counts incremented for all reachable nodes\n\0"
                                                    as *const u8 as *const core::ffi::c_char);
                                        print_node(copy);
                                    } else {
                                        printf(
                                            b"Failed to create shallow copy\n\0" as *const u8
                                                as *const core::ffi::c_char,
                                        );
                                    }
                                }
                            }
                        }
                        7 => {
                            printf(
                                b"Enter city name to delete: \0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            if !(fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                                input[strcspn(
                                    input.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                let node_2: *mut node_t = get_node_by_name(graph, input.as_ptr());
                                if node_2.is_null() {
                                    printf(
                                        b"City '%s' not found\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                        input.as_ptr(),
                                    );
                                } else {
                                    printf(
                                        b"Current ref count: %d\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                        (*node_2).ref_count,
                                    );
                                    delete_node(node_2);
                                    printf(
                                        b"Decremented reference count for %s\n\0" as *const u8
                                            as *const core::ffi::c_char,
                                        input.as_ptr(),
                                    );
                                    printf(
                                        b"Note: Node will be freed when ref count reaches 0\n\0"
                                            as *const u8
                                            as *const core::ffi::c_char,
                                    );
                                }
                            }
                        }
                        8 => {
                            printf(
                                b"Freeing graph and exiting...\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            free_graph(graph);
                            return 0 as core::ffi::c_int;
                        }
                        _ => {
                            printf(b"Invalid choice\n\0" as *const u8 as *const core::ffi::c_char);
                        }
                    }
                }
            }
            free_graph(graph);
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "mutable-duplication-dag",
        SOURCE,
        &["create_graph#graph", "add_node#node"],
        &[],
    );
}
