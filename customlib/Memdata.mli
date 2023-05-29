open AST
open Archi
open BinInt
open BinNums
open Datatypes
open Floats
open Integers
open List0
open PeanoNat
open Values

val size_chunk : memory_chunk -> coq_Z

val size_chunk_nat : memory_chunk -> nat

val align_chunk : memory_chunk -> coq_Z

type quantity =
| Q32
| Q64

val quantity_eq : quantity -> quantity -> bool

val size_quantity_nat : quantity -> nat

type memval =
| Undef
| Byte of Byte.int_compcert
| Fragment of coq_val * quantity * nat

val bytes_of_int : nat -> coq_Z -> Byte.int_compcert list

val int_of_bytes : Byte.int_compcert list -> coq_Z

val rev_if_be : Byte.int_compcert list -> Byte.int_compcert list

val encode_int : nat -> coq_Z -> Byte.int_compcert list

val decode_int : Byte.int_compcert list -> coq_Z

val inj_bytes : Byte.int_compcert list -> memval list

val proj_bytes : memval list -> Byte.int_compcert list option

val inj_value_rec : nat -> coq_val -> quantity -> memval list

val inj_value : quantity -> coq_val -> memval list

val check_value : nat -> coq_val -> quantity -> memval list -> bool

val proj_value : quantity -> memval list -> coq_val

val encode_val : memory_chunk -> coq_val -> memval list

val decode_val : memory_chunk -> memval list -> coq_val
