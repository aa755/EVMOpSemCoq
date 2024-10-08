(* Generated by Lem from map.lem. *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Program.Wf.

Require Import coqharness.

Open Scope nat_scope.
Open Scope string_scope.



Require Import lem_bool.
Require Export lem_bool.
Require Import lem_basic_classes.
Require Export lem_basic_classes.
Require Import lem_function.
Require Export lem_function.
Require Import lem_maybe.
Require Export lem_maybe.
Require Import lem_list.
Require Export lem_list.
Require Import lem_tuple.
Require Export lem_tuple.
Require Import lem_set.
Require Export lem_set.
Require Import lem_num.
Require Export lem_num.


(* 

Inductive map (k : Type) (v : Type) : Type := .
Definition map_default {k: Type} {v: Type} : map k v := DAEMON. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed top-level value definition. *)

Instance x150_Eq{k v: Type} `{Eq k} `{Eq v}: Eq (fmap  k  v):= {
   isEqual  :=  (fmap_equal_by (fun x y => x = y) (fun x y => x = y));
   isInequal   m1  m2 :=  negb ((fmap_equal_by (fun x y => x = y) (fun x y => x = y) m1 m2))
}.



(* -------------------------------------------------------------------------- *)
(* Map type class                                                             *)
(* -------------------------------------------------------------------------- *)

Class  MapKeyType (a: Type): Type := { 
  mapKeyCompare: a ->a -> ordering
}.

(*  *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

Definition fromList {k v : Type} `{MapKeyType k}  (l : list ((k*v) % type))  : fmap k v:=  List.fold_left (
  fun (m : fmap k v) (p : (k*v) % type) =>
    match ( (m ,p) ) with ( m ,  (k1, v1)) => fmap_add k1 v1 m end) l fmap_empty.
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(*  

Definition all {k v : Type} `{MapKeyType k} `{Eq v}  (P : k -> v -> bool ) (m : fmap k v)  : bool :=  (forall k  v,( (P k v && (instance_Basic_classes_Eq_Maybe_maybe.= lookup k m Some v)) : Prop)). *)
(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed top-level value definition. *)
(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)

(* instance of SetType *)
Definition map_setElemCompare {a b c d e : Type} `{SetType a} `{SetType b} `{SetType c} `{SetType d} `{MapKeyType b} `{MapKeyType d}  (cmp : set ((d*c) % type) -> set ((b*a) % type) -> e) (x : fmap d c) (y : fmap b a)  : e:= 
  cmp (id x) (id y).

Instance x149_SetType{a b: Type} `{SetType a} `{SetType b} `{MapKeyType a}: SetType (fmap  a  b):= {
   setElemCompare   x  y :=  map_setElemCompare (set_compare_by (pairCompare setElemCompare setElemCompare)) x y
}.

