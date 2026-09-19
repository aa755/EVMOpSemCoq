From Stdlib Require Import List ZArith ClassicalDescription.
From EVMOpSem Require Import Lem.coqharness Lem.lem_basic_classes block.
From EVMOpSemTests Require Import Rollback.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Goal Selector "!".

Lemma classical_eq_refl {A : Type} (x : A) :
  @eq bool (classical_boolean_equivalence x x) true.
Proof.
  unfold classical_boolean_equivalence, bool_of_Prop.
  destruct (excluded_middle_informative (@eq A x x)) as [same | different].
  { reflexivity. }
  { exfalso. apply different. reflexivity. }
Qed.

Example nonce_rejection_preserves_state tr state block :
  @eq bool (unsafe_structural_inequality (tr_nonce tr)
              (block_account_nonce (state (tr_from tr)))) true ->
  @eq _ (settle_transaction tr block (steps 7 (start_transaction tr state block)))
    (Some (TransactionRejected NonceMismatch state)).
Proof. intros H. unfold start_transaction. rewrite H. reflexivity. Qed.

(* No settlement or execution can change a rejected transaction's state. *)
Theorem rejection_is_terminal net reason state :
  @eq _ (step net (Rejected reason state)) (Rejected reason state).
Proof. reflexivity. Qed.

Theorem rejection_never_pays_fees tr block reason state :
  @eq _ (settle_transaction tr block (Rejected reason state))
    (Some (TransactionRejected reason state)).
Proof. reflexivity. Qed.

Example intrinsic_gas_rejected :
  @eq _ (start_transaction transaction_default world_state_default block_info_default)
    (Rejected IntrinsicGasTooLow world_state_default).
Proof.
  unfold start_transaction, unsafe_structural_inequality.
  cbn [transaction_default world_state_default block_account_default].
  rewrite classical_eq_refl. vm_compute. reflexivity.
Qed.

Definition exit_state (root_create : bool) (frames : list call_frame)
    (checkpoint current : world_state) (v : variable_ctx)
    (action : contract_action) : global_state :=
  Continue {| g_orig := checkpoint; g_current := current;
              g_stack := frames; g_cctx := stop_c; g_killed := [address_default];
              g_create := root_create;
              g_vmstate := InstructionToEnvironment action v None |}.

Example return_exposes_output bytes state v :
  match step Homestead (exit_state false [] state state v (ContractReturn bytes)) with
  | Finished f => @eq _ (f_outcome f) (ExecutionSuccess bytes)
  | _ => False
  end.
Proof. reflexivity. Qed.

Example root_failure_exposes_reason checkpoint current v reasons :
  match step Homestead (exit_state false [] checkpoint current v (ContractFail reasons)) with
  | Finished f =>
      @eq _ (f_outcome f) (ExecutionFailure reasons) /\
      @eq _ (f_state f) checkpoint /\ @eq _ (f_gas f) 0 /\
      @eq _ (f_refund f) 0 /\ @eq _ (f_logs f) [] /\ @eq _ (f_killed f) []
  | _ => False
  end.
Proof. repeat split; reflexivity. Qed.

Definition creation_frame (saved : world_state) : call_frame :=
  Build_call_frame saved test_v stop_c (CreateAddress address_default) [].

Example initcode_failure_is_transaction_failure checkpoint current v :
  match step Homestead
    (exit_state true [creation_frame current] checkpoint current v (ContractFail [OutOfGas])) with
  | Finished f => @eq _ (f_outcome f) (ExecutionFailure [OutOfGas]) /\
                  @eq _ (f_state f) checkpoint
  | _ => False
  end.
Proof. split; reflexivity. Qed.

Example root_deposit_failure_is_transaction_failure checkpoint current :
  match step Homestead
    (exit_state true [creation_frame current] checkpoint current deposit_v
      (ContractReturn [byte_default])) with
  | Finished f => @eq _ (f_outcome f) (ExecutionFailure [OutOfGas]) /\
                  @eq _ (f_state f) checkpoint /\ @eq _ (f_gas f) 0
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition funded_deposit : variable_ctx := {[ test_v with vctx_gas := 250 ]}.

Example root_deposit_success_finishes checkpoint current :
  match step Homestead
    (exit_state true [creation_frame current] checkpoint current funded_deposit
      (ContractReturn [byte_default])) with
  | Finished f => @eq _ (f_outcome f) (ExecutionSuccess [byte_default]) /\
                  @eq _ (f_gas f) 50
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example root_empty_code_success_finishes checkpoint current :
  match step Homestead
    (exit_state true [creation_frame current] checkpoint current test_v (ContractReturn [])) with
  | Finished f => @eq _ (f_outcome f) (ExecutionSuccess []) /\ @eq _ (f_gas f) 100
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Example frontier_deposit_failure_is_success checkpoint current :
  match step Frontier
    (exit_state true [creation_frame current] checkpoint current deposit_v
      (ContractReturn [byte_default])) with
  | Finished f => @eq _ (f_outcome f) (ExecutionSuccess [byte_default])
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

Theorem settlement_preserves_execution_outcome tr block f :
  match settle_transaction tr block (Finished f) with
  | Some (TransactionExecuted outcome _) => @eq _ outcome (f_outcome f)
  | _ => False
  end.
Proof. reflexivity. Qed.

Example incomplete_run_has_no_outcome tr block g :
  @eq _ (settle_transaction tr block (Continue g)) None.
Proof. reflexivity. Qed.

Definition address_eq_dec (x y : address) :
  { @eq address x y } + { ~ @eq address x y }.
Proof. repeat decide equality. Defined.

Lemma classical_address_eq x y :
  @eq bool (classical_boolean_equivalence x y)
    (if address_eq_dec x y then true else false).
Proof.
  unfold classical_boolean_equivalence, bool_of_Prop.
  destruct (excluded_middle_informative (@eq address x y)) as [same | different];
    destruct (address_eq_dec x y) as [same' | different']; try reflexivity; contradiction.
Qed.

Definition sender_address := word160FromNumeral 256%nat.
Definition miner_address := word160FromNumeral 257%nat.
Definition tx_block : block_info :=
  {[ {[ {[ block_info_default with block_coinbase := miner_address ]}
        with block_gaslimit := Z_to_binary 256 100000 ]}
        with block_number := Z_to_binary 256 1150000 ]}.
Definition funded_world (code : program) (a : address) : block_account :=
  {| block_account_address := a; block_account_storage := empty_storage;
     block_account_code := code; block_account_balance := Z_to_binary 256 100000;
     block_account_nonce := w256_default; block_account_exists := true;
     block_account_hascode := true |}.
Definition paid_tx : transaction :=
  {| tr_from := sender_address; tr_to := Some sender_address;
     tr_gas_limit := Z_to_binary 256 30000; tr_gas_price := Z_to_binary 256 1;
     tr_value := w256_default; tr_nonce := w256_default; tr_data := [] |}.

Example insufficient_funds_rejected :
  @eq _ (start_transaction paid_tx world_state_default tx_block)
    (Rejected InsufficientFunds world_state_default).
Proof.
  unfold start_transaction, unsafe_structural_inequality.
  cbv beta iota zeta delta [paid_tx funded_world world_state_default
    block_account_default tr_from tr_nonce block_account_nonce].
  rewrite (classical_eq_refl w256_default). vm_compute. reflexivity.
Qed.

Example block_gas_limit_rejected :
  @eq _ (start_transaction paid_tx (funded_world empty_program) block_info_default)
    (Rejected BlockGasLimitExceeded (funded_world empty_program)).
Proof.
  unfold start_transaction, unsafe_structural_inequality.
  cbv beta iota zeta delta [paid_tx funded_world world_state_default
    block_account_default tr_from tr_nonce block_account_nonce].
  rewrite (classical_eq_refl w256_default). vm_compute. reflexivity.
Qed.


Definition paid_checkpoint (code : program) : world_state :=
  update_nonce (sub_balance (funded_world code) sender_address
                  (Z_to_binary 256 30000)) sender_address.

Example accepted_transaction_records_checkpoint code :
  match start_transaction paid_tx (funded_world code) tx_block with
  | Continue g => @eq _ (g_orig g) (paid_checkpoint code)
  | _ => False
  end.
Proof.
  unfold start_transaction, unsafe_structural_inequality.
  cbv beta iota zeta delta [paid_tx funded_world tr_from tr_nonce block_account_nonce].
  rewrite (classical_eq_refl w256_default).
  cbv beta iota zeta delta [paid_checkpoint update_nonce sub_balance update_world].
  repeat rewrite classical_address_eq.
  vm_compute. reflexivity.
Qed.

(* The checkpoint above is restored by [root_failure_exposes_reason].
   Settlement then burns the allowance, preserves the nonce, and pays the miner. *)
Example failed_transaction_settles_fees_and_nonce :
  match settle_transaction paid_tx tx_block
    (fail_transaction (paid_checkpoint empty_program) [OutOfGas]) with
  | Some (TransactionExecuted (ExecutionFailure _) state) =>
      @eq _ (block_account_balance (state sender_address)) (Z_to_binary 256 70000) /\
      @eq _ (block_account_nonce (state sender_address)) (Z_to_binary 256 1) /\
      @eq _ (block_account_balance (state miner_address)) (Z_to_binary 256 130000)
  | _ => False
  end.
Proof.
  cbv beta iota zeta delta [settle_transaction fail_transaction paid_checkpoint
    sub_balance add_balance update_nonce update_world end_transaction kill_accounts
    f_state f_killed f_gas f_refund f_logs f_outcome tr_from tr_gas_price
    tr_gas_limit block_coinbase paid_tx tx_block block_account_balance
    block_account_nonce funded_world].
  repeat rewrite classical_address_eq.
  vm_compute. repeat split; reflexivity.
Qed.

Definition empty_creation_tx : transaction :=
  {[ {[ {[ paid_tx with tr_to := None ]}
        with tr_gas_limit := Z_to_binary 256 60000 ]}
        with tr_value := Z_to_binary 256 100 ]}.

Example empty_initcode_schedules_creation_with_value :
  match start_transaction empty_creation_tx (funded_world empty_program) tx_block with
  | Continue g =>
      @eq _ (g_create g) true /\
      match g_vmstate g with
      | InstructionToEnvironment (ContractCreate args) _ _ =>
          @eq _ (createarg_code args) [] /\
          @eq _ (createarg_value args) (Z_to_binary 256 100)
      | _ => False
      end
  | _ => False
  end.
Proof.
  unfold start_transaction, unsafe_structural_inequality.
  cbv beta iota zeta delta [empty_creation_tx paid_tx funded_world
    tr_from tr_nonce block_account_nonce].
  rewrite (classical_eq_refl w256_default).
  vm_compute. repeat split; reflexivity.
Qed.
