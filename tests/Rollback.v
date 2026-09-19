From Stdlib Require Import List ZArith.
From EVMOpSem Require Import block.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Goal Selector "!".

Fixpoint steps (fuel : nat) (s : global_state) : global_state :=
  match fuel with
  | O => s
  | S n => steps n (step Homestead s)
  end.

Definition test_v : variable_ctx :=
  {[ variable_ctx_default with vctx_gas := 100 ]}.
Definition stop_c : constant_ctx :=
  {| cctx_this := address_default; cctx_program := empty_program;
     cctx_hash_filter := fun _ => true |}.
Definition fail_c : constant_ctx :=
  {| cctx_this := address_default;
     cctx_program := {| program_content := fun _ => Some (Unknown byte_default);
                        program_length := 1 |};
     cctx_hash_filter := fun _ => true |}.

(* C is about to SELFDESTRUCT, B resumes at an invalid instruction,
   and A resumes at STOP. All transitions below use the real [step]. *)
Definition nested_suicide (c : address) (kept : list address)
    (resume_b : constant_ctx) : global_state :=
  Continue
    {| g_orig := world_state_default;
       g_current := world_state_default;
       g_stack := [(Build_call_frame world_state_default test_v resume_b (ReturnTo 0 0) kept);
                   (Build_call_frame world_state_default test_v stop_c (ReturnTo 0 0) kept)];
       g_cctx := {| cctx_this := c; cctx_program := empty_program;
                    cctx_hash_filter := fun _ => true |};
       g_killed := kept;
       g_vmstate := InstructionToEnvironment (ContractSuicide address_default) test_v None;
       g_create := false |}.

Example failed_ancestor_rolls_back_destruction (c : address) (kept : list address) :
  match steps 5 (nested_suicide c kept fail_c) with
  | Finished f => @eq _ (f_killed f) kept
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Example failure_restores_all_substate
    (net : network) (orig current saved : world_state)
    (caller child : variable_ctx) (c : constant_ctx) (hint : stack_hint)
    (kept discarded : list address) (rest : list call_frame) :
  let g := {| g_orig := orig; g_current := current;
              g_stack := Build_call_frame saved caller c hint kept :: rest;
              g_cctx := c; g_killed := discarded; g_create := false;
              g_vmstate := InstructionToEnvironment
                (ContractFail [OutOfGas]) child None |} in
  match step net (Continue g) with
  | Continue after =>
      @eq _ (g_current after) saved /\ @eq _ (g_killed after) kept /\
      match g_vmstate after with
      | InstructionContinue v =>
          @eq _ (vctx_logs v) (vctx_logs caller) /\
          @eq _ (vctx_refund v) (vctx_refund caller) /\
          @eq _ (vctx_storage v) (vctx_storage caller) /\
          @eq _ (vctx_gas v) (vctx_gas caller)
      | _ => False
      end
  | _ => False
  end.
Proof. cbn. repeat split; reflexivity. Qed.

Definition deposit_v : variable_ctx :=
  {[ {[ {[ test_v with vctx_gas := 0 ]}
       with vctx_refund := 99 ]}
       with vctx_block := {[ block_info_default
         with block_number := Z_to_binary 256 1150000 ]} ]}.

Example failed_code_deposit_restores_substate
    (caller : variable_ctx) (saved : world_state) (kept discarded : list address) :
  let g := {| g_orig := world_state_default; g_current := world_state_default;
              g_stack := [Build_call_frame saved caller stop_c
                            (CreateAddress address_default) kept];
              g_cctx := stop_c; g_killed := discarded; g_create := false;
              g_vmstate := InstructionToEnvironment
                (ContractReturn [byte_default]) deposit_v None |} in
  match step Homestead (Continue g) with
  | Continue after =>
      @eq _ (g_current after) saved /\ @eq _ (g_killed after) kept /\
      match g_vmstate after with
      | InstructionContinue v =>
          @eq _ (vctx_logs v) (vctx_logs caller) /\
          @eq _ (vctx_refund v) (vctx_refund caller) /\
          @eq _ (vctx_storage v) (vctx_storage caller) /\
          @eq _ (vctx_gas v) (vctx_gas caller)
      | _ => False
      end
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example successful_ancestor_keeps_destruction (c : address) (kept : list address) :
  match steps 5 (nested_suicide c kept stop_c) with
  | Finished f => @eq _ (f_killed f) (c :: kept)
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.
