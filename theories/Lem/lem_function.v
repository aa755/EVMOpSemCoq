(* Generated by Lem from function.lem. *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Program.Wf.

Require Import coqharness.

Open Scope nat_scope.
Open Scope string_scope.

(******************************************************************************)
(* A library for common operations on functions                               *)
(******************************************************************************)

Require Import lem_bool.
Require Export lem_bool.
Require Import lem_basic_classes.
Require Export lem_basic_classes.


Require Import Program.Basics.
Require Export Program.Basics.

(* [?]: removed value specification. *)

(* 
Definition id {a : Type}  (x : a)  : a:=  x. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* 
Definition comb {a b c : Type}  (f : b -> c) (g : a -> b)  : a -> c:=  (fun (x : a) => f (g x)). *)
(* [?]: removed value specification. *)

(* 
Definition apply {a b : Type}  (f : a -> b)  : a -> b:=  (fun (x : a) => f x). *)
(* [?]: removed value specification. *)

Definition rev_apply {a b : Type}  (x : a) (f : a -> b)  : b:=  f x.
(* [?]: removed value specification. *)

(* 
Definition flip {a b c : Type}  (f : a -> b -> c)  : b -> a -> c:=  (fun (x : b) (y : a) => f y x). *)
(* [?]: removed value specification. *)

Definition curry {a b c : Type}  (f : (a*b) % type -> c)  : a -> b -> c:=  (fun (a1 : a) (b1 : b) => f (a1, b1)).
(* [?]: removed value specification. *)

Definition uncurry {a b c : Type}  (f : a -> b -> c) (p : (a*b) % type)  : c:= 
  match ( (f,p)) with ( f,  (a1, b1)) => f a1 b1 end.
