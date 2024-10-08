(* Generated by Lem from either.lem. *)

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
Require Import lem_list.
Require Export lem_list.
Require Import lem_tuple.
Require Export lem_tuple.



(* 

Inductive either (a : Type) (b : Type) : Type :=
   Left:   a -> either a b
  | Right:  b -> either a b.
Definition either_default {a: Type} {b: Type} : either a b := Left DAEMON. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)


Definition eitherEqualBy {a b : Type}  (eql : a -> a -> bool ) (eqr : b -> b -> bool )  (left: sum  a  b)  (right: sum  a  b)  : bool := 
  match ( (left, right)) with 
    | (inl l,  inl l') => eql l l'
    | (inr r,  inr r') => eqr r r'
    | _ => false
  end.
Definition eitherEqual {a b : Type} `{Eq a} `{Eq b}   : sum a b -> sum a b -> bool :=  eitherEqualBy (fun x y => x = y) (fun x y => x = y).

Instance x147_Eq{a b: Type} `{Eq a} `{Eq b}: Eq (sum  a  b):= {
   isEqual  :=  eitherEqual;
   isInequal   x  y :=  negb (eitherEqual x y)
}.
 

Definition either_setElemCompare {a b c d : Type}  (cmpa : d -> b -> ordering ) (cmpb : c -> a -> ordering ) (x : sum d c) (y : sum b a)  : ordering := 
  match ( (x, y)) with 
    | (inl x',  inl y') => cmpa x' y'
    | (inr x',  inr y') => cmpb x' y'
    | (inl _,  inr _) => LT
    | (inr _,  inl _) => GT
  end.

Instance x146_SetType{a b: Type} `{SetType a} `{SetType b}: SetType (sum  a  b):= {
   setElemCompare   x  y :=  either_setElemCompare setElemCompare setElemCompare x y
}.

(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

Definition either {a b c : Type}  (fa : a -> c) (fb : b -> c) (x : sum a b)  : c:=  match ( x) with 
  | inl a1 => fa a1
  | inr b1 => fb b1
end.
(* [?]: removed value specification. *)

Program Fixpoint partitionEither {a b : Type}  (l : list (sum a b))  : (list a*list b) % type:=  match ( l) with 
  | [] => ([], [])
  | x :: xs => (* begin block *) 
  match ( partitionEither xs) with (ll,  rl) =>
    match ( x) with | inl l => ((l :: ll), rl) | inr r => (ll, (r :: rl)) end
  end
    (* end block *)
end.
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)


