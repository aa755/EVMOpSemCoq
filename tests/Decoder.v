From Stdlib Require Import List ZArith Lia ClassicalDescription.
From EVMOpSem Require Import Lem.coqharness block.
Import ListNotations.
Set Default Goal Selector "!".

Lemma push_immediate_length width bytes :
  @eq _ (List.length (push_immediate width bytes)) width.
Proof.
  unfold push_immediate. rewrite length_firstn, length_app, repeat_length.
  apply Nat.min_l. lia.
Qed.

Lemma decode_bytes_length bytes : forall pending,
  @eq _ (List.length (decode_bytes pending bytes)) (List.length bytes).
Proof.
  induction bytes as [|b rest IH]; intro pending; [reflexivity |].
  destruct pending; cbn [decode_bytes].
  { destruct (byte_to_inst b); try (cbn; rewrite IH; reflexivity).
    destruct s; cbn; rewrite IH; reflexivity. }
  { cbn. rewrite IH. reflexivity. }
Qed.

(* All PUSH operand positions remain raw bytes, never executable JUMPDESTs. *)
Lemma decode_payload bytes : forall pending idx,
  (idx < pending)%nat ->
  @eq _ (nth_error (decode_bytes pending bytes) idx)
    (option_map Unknown (nth_error bytes idx)).
Proof.
  induction bytes as [|b rest IH]; intros pending idx H.
  { destruct idx; reflexivity. }
  { destruct pending as [|pending]; [lia |].
    destruct idx as [|idx]; [reflexivity |].
    cbn [decode_bytes nth_error]. apply IH. lia. }
Qed.

Lemma decode_push b rest zeros :
  @eq _ (byte_to_inst b) (Stack (PUSH_N zeros)) ->
  @eq _ (hd_error (decode_bytes O (b :: rest)))
    (Some (Stack (PUSH_N (push_immediate (List.length zeros) rest)))).
Proof. intro H. cbn [decode_bytes]. rewrite H. reflexivity. Qed.

(* These finite checks cover all PUSH widths, including an empty immediate,
   a short immediate, payload bytes resembling PUSH opcodes, and 0x5b data. *)
Example all_push_widths :
  @eq bool (forallb (fun width =>
    match bytelist_to_instlist [word8FromNumeral (95 + width); word8FromNumeral 91] with
    | Stack (PUSH_N data) :: Unknown b :: [] =>
      Nat.eqb (List.length data) width &&
      Nat.eqb (word8ToNatural b) 91 &&
      Nat.eqb (List.length (inst_code (Stack (PUSH_N data)))) (S width)
    | _ => false
    end) (seq 1 32)) true.
Proof. vm_compute. reflexivity. Qed.

Example empty_push_immediates :
  @eq bool (forallb (fun width =>
    match bytelist_to_instlist [word8FromNumeral (95 + width)] with
    | [Stack (PUSH_N data)] =>
      Nat.eqb (List.length data) width &&
      forallb (fun b => Nat.eqb (word8ToNatural b) 0) data
    | _ => false
    end) (seq 1 32)) true.
Proof. vm_compute. reflexivity. Qed.

Example opcode_byte_roundtrip :
  @eq _ (map (fun n => inst_to_byte (byte_to_inst (word8FromNumeral n))) (seq 0 256))
    (map word8FromNumeral (seq 0 256)).
Proof. vm_compute. reflexivity. Qed.

Local Open Scope Z_scope.
Definition audit_entry := {[ variable_ctx_default with vctx_gas := 100 ]}.
Definition audit_context bytes :=
  {| cctx_this := address_default; cctx_program := make_program bytes;
     cctx_hash_filter := fun _ => true |}.

(* 0: PUSH1 4; 2: JUMP; 3: PUSH1 0x5b; 5: STOP.
   Byte 4 belongs to PUSH1's immediate; it is not a valid JUMPDEST. *)
Definition jump_into_push_data := map word8FromNumeral [96;4;86;96;91;0]%nat.

Theorem payload_is_not_executable_jumpdest :
  @eq _ (program_content (make_program jump_into_push_data) 4) (Some (Unknown (word8FromNumeral 91))).
Proof. vm_compute. reflexivity. Qed.

Theorem model_rejects_jump_into_push_data :
  match program_sem (fun _ => tt) (audit_context jump_into_push_data) 4 Homestead
     (InstructionContinue audit_entry) with
  | InstructionToEnvironment (ContractFail [InvalidJumpDestination]) _ None => True
  | _ => False
  end.
Proof. vm_compute. exact I. Qed.

(* PUSH2 0x01 at end of code must push 0x0100 and advance by 3 bytes.
   Missing bytes are padded, and the declared instruction width is preserved. *)
Theorem model_pads_truncated_push :
  match next_state (fun _ => tt) (audit_context (map word8FromNumeral [97;1]%nat))
      Homestead (InstructionContinue audit_entry) with
  | InstructionContinue v =>
      @eq _ (vctx_stack v) [word256FromNumeral 256] /\ @eq _ (vctx_pc v) 3
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions model_rejects_jump_into_push_data.
Print Assumptions model_pads_truncated_push.

(* A real destination AFTER an immediate remains executable. *)
Example jump_to_instruction_boundary :
  match program_sem (fun _ => tt)
    (audit_context (map word8FromNumeral [96;5;86;96;91;91;0]%nat)) 4 Homestead
    (InstructionContinue audit_entry) with
  | InstructionToEnvironment (ContractReturn []) _ None => True
  | _ => False
  end.
Proof. vm_compute. exact I. Qed.

(* JUMPI must reject data targets too when its condition is true. *)
Example conditional_jump_into_push_data :
  match jumpi
    {[ audit_entry with vctx_stack := [word256FromNumeral 4; word256FromNumeral 1] ]}
    (audit_context jump_into_push_data) with
  | InstructionToEnvironment (ContractFail [InvalidJumpDestination]) _ None => True
  | _ => False
  end.
Proof.
  unfold jumpi. cbv beta iota zeta delta [vctx_stack].
  unfold classical_boolean_equivalence, bool_of_Prop.
  match goal with
  | |- context [excluded_middle_informative ?P] =>
      destruct (excluded_middle_informative P); [discriminate |]
  end.
  vm_compute. exact I.
Qed.

(* Byte access used by CODECOPY/EXTCODECOPY preserves all original byte values,
   including bytes inside PUSH operands; virtual padding does not extend code. *)
Example raw_byte_access :
  let bytes := map word8FromNumeral (seq 0 256) in
  @eq _ (map (program_as_natural_map (make_program bytes)) (seq 0 256)) bytes.
Proof. vm_compute. reflexivity. Qed.

Example padded_immediate_does_not_extend_code :
  let p := make_program (map word8FromNumeral [97;1]%nat) in
  @eq _ (program_length p) 2 /\
  @eq _ (map (program_as_natural_map p) [0;1;2]%nat)
    (map word8FromNumeral [97;1;0]%nat) /\
  @eq _ (program_content p 2) None.
Proof. vm_compute. repeat split; reflexivity. Qed.
