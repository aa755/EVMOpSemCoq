(**
This file is deprecated. do not use. use block.v instead

Require Import elpi.apps.derive.derive.
Require Import elpi.elpi.
Require Import elpi.apps.derive.derive.lens.
Require Import elpi.apps.derive.derive.lens_laws.

Require Import EVMOpSem.evm.

Module account.
  Record state : Type := {
  storage : storage ;
  code : option program ;
  balance : w256 ;
  nonce: N
    }.

Definition newAcWitBal : account.state:=
  {|
    storage := fun _ => w256_default (* 0 *);
    code := None;
    balance := w256_default (* 0 *);
    nonce := 0%N
  |}.
  
End account.


Definition lens_compose {a b c d e f : Type}
           (l1 : Lens a b c d) (l2 : Lens c d e f)
: Lens a b e f :=
{| view := fun x : a => view l2 (view l1 x)
; over := fun f0 : e -> f => over l1 (over l2 f0) |}.

Definition set {a b c d : Type} (l : Lens a b c d) (new : d) : a -> b :=
  l.(over) (fun _ => new).

(* level numbers copied from https://github.com/bedrocksystems/coq-lens/blob/47652c1446955964ed58cd7bd33abd239135f586/theories/Lens.v *)
Notation "a & b" := (b a) (at level 50, only parsing, left associativity) : lens_scope.
Notation "a %= f" := (over a f) (at level 49, left associativity) : lens_scope.
Notation "a .= b" := (set a b) (at level 49, left associativity) : lens_scope.
Notation "a .^ f" := (view f a) (at level 45, left associativity) : lens_scope.
Notation "a .@ b" := (lens_compose a b) (at level 19, left associativity) : lens_scope.

Require Import stdpp.gmap.
(*Definition w160:=N.  sigma(set) type can be used but that can slow down computation in coq Definition address := N.

Global Instance : forall {n}, Countable (Bvector n).
Proof using. Admitted.
 *)

Global Instance: EqDecision word160.
Proof using. Admitted.

Global Instance : Countable word160.
Proof using. Admitted.

Definition GlobalState := gmap address account.state.
Module Message.

  (** the message that triggered execution of this EVM instance. Calls to other contracts start execution of a new instance. This roughly corresponds to `class Message` in __init.py__ of the python instance. *)
  #[only(lens_laws)] derive
  Record t :=
    {
      caller:address;
      gas: N;
      data_sent: list byte;
      value_sent: w256;
      callee: address;
    }.
  Definition asMsg (ca: call_arguments) : t. Proof. Admitted.

End Message.

(*
Module Transaction.
 (** Details of the transaction that started the execution which may contain a chain of contract calls.
In addition, it also includes the blockhashes (to support the BLOCKHASH) instruction. This roughly correponds to
`class Environment` in the official ethereum-specs. We remove the `state` field because it is not really external and is modified by EVM.  *)
  Record t :=
    {
      caller: address;
      block_hashes: list N;
      
    }.
*)      

  Open Scope lens_scope.

Module EvmCall.
  #[only(lens_laws)] derive
  Record t :=
    {
      pc: N;
      stack: list w256;
      remainingGas: N; (* a callee does not inherit all the gas, so this is a per-call property, unlike gas refund which can be accounted for the whole chain *)
      memory: memory; (* use gmap? *)
      memUsage: N;
      initState: GlobalState;
      msg: Message.t;
      updatedState: GlobalState (* updated storage of this account *)
      (* without the call opcode, is it possible to update the balance of any other address ?*)
    }.

  Definition code (s:t) : program :=
    match option_bind _ _ account.code ((updatedState s) !! (Message.callee (msg s))) with
    | Some ac => ac
    | None => empty_program
    end.

  Definition thisAccount s :=  (Message.callee (msg s)).

  (*
  Definition transferBalance (src dst: address) (e:t): t :=
    e & t__memUsage .= 0%N.
  
    over (t__memUsage) (fun _ => 0%N) e.
*)
End EvmCall.

Module EvmCallChain.

  #[only(lens_laws)] derive
  Record t:=
    {
      callchain: list EvmCall.t;
      gas_refund: N;
    }.

End EvmCallChain.

Module Result.
Inductive t  : Type := 
| Failure:  list  failure_reason  -> t  (* failing back to the caller *)
| Suicide: t  (* destroying itself and returning back to the caller *)
| Return:  list  byte  -> t.
End Result.

Definition const_ctx_of (ec: EvmCall.t) : constant_ctx  :=
  {|
    cctx_program := EvmCall.code ec;
    cctx_this := Message.callee (EvmCall.msg ec);
    cctx_hash_filter := fun _ => true (* FIXME: no idea what is is *)
  |}.                 

Definition variable_ctx_of (gas_refund: N) (ec: EvmCall.t) : variable_ctx.
  refine
  {|
    vctx_stack := EvmCall.stack ec;
    vctx_gas := NtoZ (EvmCall.remainingGas ec);
    vctx_refund := NtoZ gas_refund;
    vctx_pc:= NtoZ (EvmCall.pc ec);
  |}.
  all: apply coqharness.DAEMON.
Defined.           
  
Open Scope stdpp.
Definition transferValue (src dst: address)  (value: w256) (g: GlobalState): GlobalState := g. (* FIX*)

Import EvmCall.
Import EvmCallChain.
Import Result.
(*
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre. *)
(* From iris.program_logic Require Import ectx_lifting. *)

#[only(lens_laws), module] derive
Record expr := {
    pc: N;
    code: list inst
  }.

(* a call returns a 0/1 status on stack and optionally data
to return data, the callee can use RETURN and REVERT
to return successfully without data, one can use STOP, SELFDESTRUCT
 *)
#[only(lens_laws), module] derive
Record val := {
    status:bool;
    retdata: list byte
  }.

    
(*    
Definition evmlang: language.
  refine
    {|
      
      language.expr := list expr; (* call chain. there is a choice about what to put in state vs expr. for compositional reasoning, we want RETURN to evaluate to a value regardless of state thus the continuation must be in the expression type, not state *)
      language.val := val;
      language.state:= unit (* the rest of [EvmCallChain] *)
        (* REVERT is problematic for separation logic reasoning *)
    |}.
  
  
*)
Definition bvToZ {n} (v: Bvector n) : Z := binary_value _ v.
Definition bvToN {n} (v: Bvector n) : N := Z.to_N (binary_value _ v).
(*
Definition next_step_full  *)

Definition removeKey `{Countable A} B (g: gmap A B) (a:A) : gmap A B :=
  delete a g.
(** this can be defined using Prgram Fixpoint with remaining gas as the decreasing measure. just need to be careful with JUMPDEST. if the pc points to JUMPDEST, we need to execute the next non-JUMPDEST instruction before recursing. then we can get rid of the fuel business *)
Fixpoint completeEval (fuel: nat) (net : network ) (ec :EvmCallChain.t) : option Result.t :=
  match fuel, EvmCallChain.callchain ec with
  | 0, _ => None
  | _, [] => None (* out of Coq fuel *)
  | S fuel', evh::evtl =>
      match program_sem (fun _=> tt) (const_ctx_of evh) fuel net (InstructionContinue (variable_ctx_of (EvmCallChain.gas_refund ec) evh)) with
      | InstructionContinue _ => None (* out of Coq fuel *)
      | InstructionToEnvironment caction vctx _ =>
          match caction with
          | ContractReturn ret => Some (Result.Return ret)
          | ContractCall callargs =>
              let callee := (callarg_recipient callargs) in
              let tfVal :=transferValue (thisAccount evh) callee (callarg_value callargs) in
              match (EvmCall.updatedState evh) !! callee with
              | None =>
                let newSt :GlobalState := 
                  tfVal (<[callee := account.newAcWitBal]>(EvmCall.updatedState evh)) in
                completeEval fuel' net (ec & t__callchain .= ((evh & t__updatedState .= newSt)::evtl))
              | Some {| account.code := opg |} =>
                  match opg with
                  | None =>
                      let newSt :GlobalState := tfVal (EvmCall.updatedState evh) in
                      completeEval fuel' net (ec & t__callchain .= ((evh & t__updatedState .= newSt)::evtl))
                  | Some _ =>
                      let newSt :GlobalState := tfVal (EvmCall.updatedState evh) in
                      let calleeGas := bvToN (callarg_gas callargs) in
                      let newCall : EvmCall.t :=
                        {|
                          pc:=0%N;
                          stack := []%N;
                          memUsage := 0%N;
                          memory:= memory_default;
                          initState := newSt;
                          updatedState := newSt;
                          msg := Message.asMsg callargs;
                          remainingGas := calleeGas;
                         |} in              
                          
                      let newCallChain:= (ec & t__callchain .= (newCall::((evh & t__updatedState .= newSt & t__remainingGas %= (N.sub calleeGas))::evtl))) in
                      match completeEval fuel' net newCallChain with
                      | None => None (* fot of Coq fuel *)
                      | Some (Failure _) =>
                          completeEval fuel' net (ec & t__callchain .= ((evh & t__stack %= (cons (Z_to_binary _ 0)))::evtl))
                      | Some Suicide =>
                          completeEval fuel' net (ec & t__callchain .= ((evh & t__updatedState %= (delete callee) & t__stack %= (cons (Z_to_binary _ 0)))::evtl))                          
                      | Some (Return bytes) => None
                      end
                  end
              end
          | _  => None
          end
      end
  end.
    
 *)
