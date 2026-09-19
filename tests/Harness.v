From Stdlib Require Import List Arith.
From EVMOpSem Require Import Lem.coqharness block.
Import ListNotations.
Local Open Scope nat_scope.
Set Default Goal Selector "!".

(* These exercise both repaired well-founded recursions. *)
Example power_accumulator : @eq nat (gen_pow_aux Nat.mul 1 3 5) 243.
Proof. vm_compute. reflexivity. Qed.

Example binary_thirteen :
  @eq (list bool) (boolListFromNatural [] 13) [true; false; true; true].
Proof. vm_compute. reflexivity. Qed.

Example binary_zero : @eq (list bool) (boolListFromNatural [] 0) [].
Proof. reflexivity. Qed.

Print Assumptions gen_pow_aux.
Print Assumptions boolListFromNatural.
Print Assumptions word256Add.
Print Assumptions word256FromInteger.
Print Assumptions instruction_sem.
Print Assumptions step.
Print Assumptions start_transaction.
Print Assumptions end_transaction.
