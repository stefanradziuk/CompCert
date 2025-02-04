open Archi
open BinInt
open BinNums
open Coqlib
open Datatypes
open List0
open Zbits
open Zpower

type comparison =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

val negate_comparison : comparison -> comparison

val swap_comparison : comparison -> comparison

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : nat

  val zwordsize : coq_Z

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  val min_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : coq_Z -> int -> int

  val sign_ext : coq_Z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> coq_Z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> coq_Z -> int -> coq_Z -> bool

  val size : int -> coq_Z

  val unsigned_bitfield_extract : coq_Z -> coq_Z -> int -> int

  val signed_bitfield_extract : coq_Z -> coq_Z -> int -> int

  val bitfield_insert : coq_Z -> coq_Z -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : nat
 end

module Int :
 sig
  val wordsize : nat

  val zwordsize : coq_Z

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  val min_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : coq_Z -> int -> int

  val sign_ext : coq_Z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> coq_Z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> coq_Z -> int -> coq_Z -> bool

  val size : int -> coq_Z

  val unsigned_bitfield_extract : coq_Z -> coq_Z -> int -> int

  val signed_bitfield_extract : coq_Z -> coq_Z -> int -> int

  val bitfield_insert : coq_Z -> coq_Z -> int -> int -> int
 end

module Wordsize_8 :
 sig
  val wordsize : nat
 end

module Byte :
 sig
  val wordsize : nat

  val zwordsize : coq_Z

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  val min_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : coq_Z -> int -> int

  val sign_ext : coq_Z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> coq_Z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> coq_Z -> int -> coq_Z -> bool

  val size : int -> coq_Z

  val unsigned_bitfield_extract : coq_Z -> coq_Z -> int -> int

  val signed_bitfield_extract : coq_Z -> coq_Z -> int -> int

  val bitfield_insert : coq_Z -> coq_Z -> int -> int -> int
 end

module Wordsize_64 :
 sig
  val wordsize : nat
 end

module Int64 :
 sig
  val wordsize : nat

  val zwordsize : coq_Z

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  val min_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val ror : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val iwordsize' : Int.int_compcert

  val shl' : int -> Int.int_compcert -> int

  val shru' : int -> Int.int_compcert -> int

  val shr' : int -> Int.int_compcert -> int

  val shrx' : int -> Int.int_compcert -> int

  val one_bits' : int -> Int.int_compcert list

  val is_power2' : int -> Int.int_compcert option

  val loword : int -> Int.int_compcert

  val hiword : int -> Int.int_compcert

  val ofwords : Int.int_compcert -> Int.int_compcert -> int

  val mul' : Int.int_compcert -> Int.int_compcert -> int
 end

module Wordsize_Ptrofs :
 sig
  val wordsize : nat
 end

module Ptrofs :
 sig
  val wordsize : nat

  val modulus : coq_Z

  val half_modulus : coq_Z

  val max_unsigned : coq_Z

  val max_signed : coq_Z

  type int = coq_Z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> coq_Z

  val coq_Z_mod_modulus : coq_Z -> coq_Z

  val unsigned : int -> coq_Z

  val signed : int -> coq_Z

  val repr : coq_Z -> int

  val zero : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val ltu : int -> int -> bool

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val cmpu : comparison -> int -> int -> bool

  val to_int : int -> Int.int_compcert

  val to_int64 : int -> Int64.int_compcert

  val of_int : Int.int_compcert -> int

  val of_intu : Int.int_compcert -> int

  val of_ints : Int.int_compcert -> int

  val of_int64 : Int64.int_compcert -> int
 end
