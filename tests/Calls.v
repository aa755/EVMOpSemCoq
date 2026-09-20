(* All low addresses use ordinary account dispatch; native precompiles are absent. *)
From Stdlib Require Import List ZArith.
From EVMOpSem Require Import Lem.coqharness block.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Goal Selector "!".

Definition low_call : call_arguments :=
  {| callarg_gas := word256FromNumeral 0; callarg_code := word160FromNumeral 1;
     callarg_recipient := word160FromNumeral 1; callarg_value := word256FromNumeral 0;
     callarg_data := []; callarg_output_begin := word256FromNumeral 0;
     callarg_output_size := word256FromNumeral 0 |}.

Theorem low_call_dispatches g v area :
  @eq _ (g_vmstate g) (InstructionToEnvironment (ContractCall low_call) v area) ->
  exists h, @eq _ (step Homestead (Continue g)) (Continue h).
Proof.
  intro Hr. unfold step. rewrite Hr.
  destruct (word256ULT _ _ || nat_gtb _ _); eexists; reflexivity.
Qed.

Theorem low_call_enters_ordinary_code g v area :
  @eq _ (g_vmstate g) (InstructionToEnvironment (ContractCall low_call) v area) ->
  @eq _ (word256ULT
    (block_account_balance (update_return (g_current g) (cctx_this (g_cctx g)) v
      (cctx_this (g_cctx g)))) (callarg_value low_call) ||
      nat_gtb (List.length (g_stack g)) 1023) false ->
  exists h, @eq _ (step Homestead (Continue g)) (Continue h) /\
    @eq _ (cctx_this (g_cctx h)) (word160FromNumeral 1) /\
    @eq _ (cctx_program (g_cctx h))
      (block_account_code (update_call
        (update_return (g_current g) (cctx_this (g_cctx g)) v)
        (cctx_this (g_cctx g)) low_call (word160FromNumeral 1))).
Proof.
  intros Hr Hallowed. unfold step. rewrite Hr, Hallowed.
  eexists. repeat split; reflexivity.
Qed.


Print Assumptions low_call_enters_ordinary_code.
