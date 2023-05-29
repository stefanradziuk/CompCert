open AST
open Floats
open Integers

type eventval =
| EVint of Int.int_compcert
| EVlong of Int64.int_compcert
| EVfloat of float
| EVsingle of float32
| EVptr_global of ident * Ptrofs.int_compcert

type event =
| Event_syscall of char list * eventval list * eventval
| Event_vload of memory_chunk * ident * Ptrofs.int_compcert * eventval
| Event_vstore of memory_chunk * ident * Ptrofs.int_compcert * eventval
| Event_annot of char list * eventval list

type trace = event list

(** val coq_E0 : trace **)

let coq_E0 =
  []
