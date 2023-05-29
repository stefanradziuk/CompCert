open AST
open Archi
open BinInt
open BinNums
open BoolEqual
open Coqlib
open Datatypes
open Floats
open Integers

type condition =
| Ccomp of comparison
| Ccompu of comparison
| Ccompimm of comparison * Int.int_compcert
| Ccompuimm of comparison * Int.int_compcert
| Ccompl of comparison
| Ccomplu of comparison
| Ccomplimm of comparison * Int64.int_compcert
| Ccompluimm of comparison * Int64.int_compcert
| Ccompf of comparison
| Cnotcompf of comparison
| Ccompfs of comparison
| Cnotcompfs of comparison
| Cmaskzero of Int.int_compcert
| Cmasknotzero of Int.int_compcert

type addressing =
| Aindexed of coq_Z
| Aindexed2 of coq_Z
| Ascaled of coq_Z * coq_Z
| Aindexed2scaled of coq_Z * coq_Z
| Aglobal of ident * Ptrofs.int_compcert
| Abased of ident * Ptrofs.int_compcert
| Abasedscaled of coq_Z * ident * Ptrofs.int_compcert
| Ainstack of Ptrofs.int_compcert

type operation =
| Omove
| Ointconst of Int.int_compcert
| Olongconst of Int64.int_compcert
| Ofloatconst of float
| Osingleconst of float32
| Oindirectsymbol of ident
| Ocast8signed
| Ocast8unsigned
| Ocast16signed
| Ocast16unsigned
| Oneg
| Osub
| Omul
| Omulimm of Int.int_compcert
| Omulhs
| Omulhu
| Odiv
| Odivu
| Omod
| Omodu
| Oand
| Oandimm of Int.int_compcert
| Oor
| Oorimm of Int.int_compcert
| Oxor
| Oxorimm of Int.int_compcert
| Onot
| Oshl
| Oshlimm of Int.int_compcert
| Oshr
| Oshrimm of Int.int_compcert
| Oshrximm of Int.int_compcert
| Oshru
| Oshruimm of Int.int_compcert
| Ororimm of Int.int_compcert
| Oshldimm of Int.int_compcert
| Olea of addressing
| Omakelong
| Olowlong
| Ohighlong
| Ocast32signed
| Ocast32unsigned
| Onegl
| Oaddlimm of Int64.int_compcert
| Osubl
| Omull
| Omullimm of Int64.int_compcert
| Omullhs
| Omullhu
| Odivl
| Odivlu
| Omodl
| Omodlu
| Oandl
| Oandlimm of Int64.int_compcert
| Oorl
| Oorlimm of Int64.int_compcert
| Oxorl
| Oxorlimm of Int64.int_compcert
| Onotl
| Oshll
| Oshllimm of Int.int_compcert
| Oshrl
| Oshrlimm of Int.int_compcert
| Oshrxlimm of Int.int_compcert
| Oshrlu
| Oshrluimm of Int.int_compcert
| Ororlimm of Int.int_compcert
| Oleal of addressing
| Onegf
| Oabsf
| Oaddf
| Osubf
| Omulf
| Odivf
| Omaxf
| Ominf
| Onegfs
| Oabsfs
| Oaddfs
| Osubfs
| Omulfs
| Odivfs
| Osingleoffloat
| Ofloatofsingle
| Ointoffloat
| Ofloatofint
| Ointofsingle
| Osingleofint
| Olongoffloat
| Ofloatoflong
| Olongofsingle
| Osingleoflong
| Ocmp of condition
| Osel of condition * typ

val eq_condition : condition -> condition -> bool

val eq_addressing : addressing -> addressing -> bool

val beq_operation : operation -> operation -> bool

val eq_operation : operation -> operation -> bool

val float_max : float -> float -> float

val float_min : float -> float -> float

val offset_in_range : coq_Z -> bool

val ptroffset_min : coq_Z

val ptroffset_max : coq_Z

val ptroffset_in_range : Ptrofs.int_compcert -> bool

val addressing_valid : addressing -> bool

val type_of_condition : condition -> typ list

val type_of_addressing_gen : typ -> addressing -> typ list

val type_of_addressing : addressing -> typ list

val type_of_addressing32 : addressing -> typ list

val type_of_addressing64 : addressing -> typ list

val type_of_operation : operation -> typ list * typ

val is_move_operation : operation -> 'a1 list -> 'a1 option

val negate_condition : condition -> condition

val shift_stack_addressing : coq_Z -> addressing -> addressing

val shift_stack_operation : coq_Z -> operation -> operation

val offset_addressing_total : addressing -> coq_Z -> addressing

val offset_addressing : addressing -> coq_Z -> addressing option

val is_trivial_op : operation -> bool

val condition_depends_on_memory : condition -> bool

val op_depends_on_memory : operation -> bool

val globals_addressing : addressing -> ident list

val globals_operation : operation -> ident list

val builtin_arg_ok_1 : 'a1 builtin_arg -> builtin_arg_constraint -> bool

val builtin_arg_ok : 'a1 builtin_arg -> builtin_arg_constraint -> bool
