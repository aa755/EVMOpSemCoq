Require Import Bvector.
Require Export Bvector.

Require Import Evm.Zdigits.
Require Export Evm.Zdigits.

(*
Module ListNotations.
Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..) (compat "8.4") : list_scope.
End ListNotations.

Import ListNotations.
 *)
Require Import Coq.Lists.List.
Export ListNotations.

Open Scope list_scope.

Require Import ZArith.
Definition word256_default := Z_to_binary 256 0%Z.
