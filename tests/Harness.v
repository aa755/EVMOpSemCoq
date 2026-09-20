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

(* Exercise conversion at transaction-sized values without normalizing a
   well-founded termination certificate at every recursive step. *)
Example gas_price_product :
  @eq _ (word256Mult (Z_to_binary 256 1) (Z_to_binary 256 30000))
    (Z_to_binary 256 30000).
Proof. vm_compute. reflexivity. Qed.
Print Assumptions boolListFromNatural_equation.

(* List slicing is on the bytecode and calldata execution paths. *)
Theorem natural_le_spec m n : @eq _ (nat_lteb m n) true <-> (m <= n)%nat.
Proof. apply Nat.leb_le. Qed.

Example slice_stops_at_bound :
  @eq _ (take 2 [10; 20; 30], drop 2 [10; 20; 30]) ([10; 20], [30]).
Proof. vm_compute. reflexivity. Qed.

Example push2_decodes_two_bytes :
  @eq _ (program_content (make_program (map word8FromNumeral [97; 1; 0; 0])) 0%Z)
    (Some (Stack (PUSH_N (map word8FromNumeral [1; 0])))).
Proof. vm_compute. reflexivity. Qed.

(* Settlement's gas refund is bounded by half the gas consumed. *)
Theorem natural_min_correct m n : @eq _ (nat_min m n) (Nat.min m n).
Proof. revert n. induction m; destruct n; cbn; auto. Qed.

Example zero_refund_cap : @eq _ (nat_min 24000 0) 0.
Proof. reflexivity. Qed.

Example refund_limited_by_consumed_gas : @eq _ (nat_min 24000 (30000 / 2)) 15000.
Proof. rewrite natural_min_correct. vm_compute. reflexivity. Qed.
