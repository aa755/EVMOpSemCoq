(* Generated by Lem from set_helpers.lem. *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Program.Wf.

Require Import coqharness.

Open Scope nat_scope.
Open Scope string_scope.

(******************************************************************************)
(* Helper functions for sets                                                  *)
(******************************************************************************)

(* Usually there is a something.lem file containing the main definitions and a 
   something_extra.lem one containing functions that might cause problems for
   some backends or are just seldomly used.

   For sets the situation is different. folding is not well defined, since it
   is only sensibly defined for finite sets and the traversal 
   order is underspecified. *) 

(* ========================================================================== *)
(* Header                                                                     *)
(* ========================================================================== *)

Require Import lem_bool.
Require Export lem_bool.
Require Import lem_basic_classes.
Require Export lem_basic_classes.
Require Import lem_maybe.
Require Export lem_maybe.
Require Import lem_function.
Require Export lem_function.
Require Import lem_num.
Require Export lem_num.
 

Require Import Coq.Lists.List.
Require Export Coq.Lists.List.

(* [?]: removed value specification. *)



