//! Tracing garbage collector
//!
//! Use malloc to allocate/free memory.
//! Keep track of all allocated objects.
//! Keep track of root nodes.
//!   Root nodes are: Global vars, all local vars in scope.
//!   Global vars:
//!     Add them from main permanently.
//!   Local vars:
//!     Add them to stack when bound, and insert a pop(n) in kvasir code at end of scope.
//!   Temporary vals(?):
//!     Like if you do
//!       let a = b + c
//!     where both b and c are expressions that result in heap allocated objects.
//!     Consider: First b is allocated, then c is allocated, then (b + c) is allocated and stored in a.
//!     If the GC decides it's time to clean when the allocation request for c is made, what happens to b then?
//!     Maybe we need a way to consider temporary values as root nodes, until a binding is made and they're referd to through there.

use libc;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Mutex;
use std::mem;
use std::iter;

lazy_static! {
    static ref GC: Mutex<Gc> = Mutex::new(Gc::new());
}

type ObjHandler = extern "C" fn(obj_ref: *const i8);

type ObjVisitor = extern "C" fn(obj: *const i8, obj_handler: ObjHandler);

#[no_mangle]
pub extern "C" fn gc_push_new_scope() {
    let mut gc = GC.lock().unwrap();
    gc.push_new_scope()
}

#[no_mangle]
pub extern "C" fn gc_alloc_temp(size: usize, obj_visitor: ObjVisitor) -> *mut i8 {
    let mut gc = GC.lock().unwrap();
    gc.alloc_temp(size, obj_visitor)
}

#[no_mangle]
pub extern "C" fn gc_mark_bound(obj: *const i8, obj_visitor: ObjVisitor) {
    let mut gc = GC.lock().unwrap();
    gc.mark_bound(obj, obj_visitor)
}

#[no_mangle]
pub extern "C" fn gc_mark_bound_and_clear_scope_temps(obj: *const i8, obj_visitor: ObjVisitor) {
    let mut gc = GC.lock().unwrap();
    gc.mark_bound(obj, obj_visitor);
    gc.clear_scope_temps()
}

#[no_mangle]
pub extern "C" fn gc_pop_scope() {
    let mut gc = GC.lock().unwrap();
    gc.pop_scope()
}

type UIntPtr = usize;

struct Scope {
    temps: BTreeSet<UIntPtr>,
    bounds: BTreeSet<UIntPtr>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            temps: BTreeSet::new(),
            bounds: BTreeSet::new(),
        }
    }
}

static mut GET_OBJ_REFS_REFS: Vec<UIntPtr> = Vec::new();

extern "C" fn push_obj_ref_to_static_vec(obj: *const i8) {
    unsafe { GET_OBJ_REFS_REFS.push(obj as UIntPtr) }
}

fn get_obj_refs(obj: *const i8, obj_visitor: ObjVisitor) -> &'static [UIntPtr] {
    unsafe {
        GET_OBJ_REFS_REFS.clear();
        obj_visitor(obj, push_obj_ref_to_static_vec);
        &GET_OBJ_REFS_REFS
    }
}

struct Gc {
    allocs: BTreeMap<UIntPtr, ObjVisitor>,
    scopes: Vec<Scope>,
    top_scope: Scope,
}

impl Gc {
    fn new() -> Self {
        Gc {
            allocs: BTreeMap::new(),
            scopes: Vec::with_capacity(8),
            top_scope: Scope::new(),
        }
    }

    fn push_new_scope(&mut self) {
        let new_top_scope = Scope::new();
        let prev_top_scope = mem::replace(&mut self.top_scope, new_top_scope);
        self.scopes.push(prev_top_scope);
    }

    fn alloc_temp(&mut self, size: usize, obj_visitor: ObjVisitor) -> *mut i8 {
        let ptr = unsafe { libc::malloc(size) };
        let ptr_u = ptr as UIntPtr;
        self.allocs.insert(ptr_u, obj_visitor);
        self.top_scope.temps.insert(ptr_u);
        self.clean();
        ptr as *mut i8
    }

    fn mark_bound(&mut self, obj: *const i8, obj_visitor: ObjVisitor) {
        let refs = get_obj_refs(obj, obj_visitor);
        for r in refs {
            if self.top_scope.temps.remove(r) {
                self.top_scope.bounds.insert(*r);
            }
        }
    }

    fn clear_scope_temps(&mut self) {
        self.top_scope.temps.clear()
    }

    fn pop_scope(&mut self) {
        let new_top_scope = self.scopes
            .pop()
            .expect("ICE: Popped GC scope when no scopes below");
        self.top_scope = new_top_scope;
    }

    fn gather_reachable_objects(&self) -> BTreeSet<UIntPtr> {
        let mut objs: VecDeque<UIntPtr> = self.scopes
            .iter()
            .chain(iter::once(&self.top_scope))
            .flat_map(|s| s.temps.iter().chain(&s.bounds).cloned())
            .collect();
        let mut reachables: BTreeSet<UIntPtr> = objs.iter().cloned().collect();
        while let Some(obj) = objs.pop_front() {
            if let Some(&obj_visitor) = self.allocs.get(&obj) {
                let refs = get_obj_refs(obj as *const i8, obj_visitor);
                for &r in refs {
                    if reachables.insert(r) {
                        objs.push_back(r)
                    }
                }
            } else {
                // Foreign pointer?
                // TODO: What is this case?
            }
        }
        reachables
    }

    fn free_unreachables(&mut self, reachables: BTreeSet<UIntPtr>) {
        let allocs = mem::replace(&mut self.allocs, BTreeMap::new());
        for (obj, obj_vis) in allocs {
            if reachables.contains(&obj) {
                self.allocs.insert(obj, obj_vis);
            } else {
                unsafe { libc::free(obj as *mut _) }
            }
        }
    }

    fn clean(&mut self) {
        let reachables = self.gather_reachable_objects();
        self.free_unreachables(reachables)
    }
}
