(* Generated by Lem from lem/word4.lem. *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Program.Wf.

Require Import Lem.coqharness.

Open Scope nat_scope.
Open Scope string_scope.

(*
  Copyright 2016 Sami MÃ¤kelÃ¤

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
Require Import Lem.lem_pervasives.
Require Export Lem.lem_pervasives.

Require Import Lem.lem_word.
Require Export Lem.lem_word.


Inductive word4 : Type :=  W4:  bool  ->  list  bool  -> word4 .
Definition word4_default: word4  := W4 bool_default DAEMON.
(* [?]: removed value specification. *)

Definition bs_to_w4  (seq : bitSequence )  : word4 :=  match ( resizeBitSeq (Some( 4%nat)) seq) with 
 | BitSeq _ s b => W4 s b
end.
(* [?]: removed value specification. *)

Definition w4_to_bs  (w : word4 )  : bitSequence := 
  match ( (w)) with (( W4 s b)) => BitSeq (Some ( 4%nat)) s b end.
(* [?]: removed value specification. *)

Definition word4BinTest {a : Type}  (binop : bitSequence  -> bitSequence  -> a) (w1 : word4 ) (w2 : word4 )  : a:=  binop (w4_to_bs w1) (w4_to_bs w2).
(* [?]: removed value specification. *)

Definition word4BinOp  (binop : bitSequence  -> bitSequence  -> bitSequence ) (w1 : word4 ) (w2 : word4 )  : word4 :=  bs_to_w4 (binop (w4_to_bs w1) (w4_to_bs w2)).
(* [?]: removed value specification. *)

Definition word4NatOp  (binop : bitSequence  -> nat  -> bitSequence ) (w1 : word4 ) (n : nat )  : word4 :=  bs_to_w4 (binop (w4_to_bs w1) n).
(* [?]: removed value specification. *)

Definition word4UnaryOp  (op : bitSequence  -> bitSequence ) (w : word4 )  : word4 :=  bs_to_w4 (op (w4_to_bs w)).
(* [?]: removed value specification. *)

Definition word4ToNat  (w : word4 )  : nat :=  Z.abs_nat ( Coq.ZArith.Zdiv.Zmod( (integerFromBitSeq (w4_to_bs w)))((Z.pred (Z.pos (P_of_succ_nat 16%nat))))).
(* [?]: removed value specification. *)

Definition word4ToInt  (w : word4 )  : Z :=   (integerFromBitSeq (w4_to_bs w)).
(* [?]: removed value specification. *)

Definition word4ToUInt  (w : word4 )  : Z :=  Coq.ZArith.Zdiv.Zmod (word4ToInt w)((Z.pred (Z.pos (P_of_succ_nat 16%nat)))).
(* [?]: removed value specification. *)

Definition word4FromInteger  (i : Z )  : word4 :=  bs_to_w4 (bitSeqFromInteger (Some( 4%nat)) i).
(* [?]: removed value specification. *)

Definition word4FromInt  (i : Z )  : word4 :=  bs_to_w4 (bitSeqFromInteger (Some( 4%nat)) ( i)).
(* [?]: removed value specification. *)

Definition word4FromNat  (i : nat )  : word4 :=  word4FromInteger ((Z.pred (Z.pos (P_of_succ_nat i)))).
(* [?]: removed value specification. *)

Definition word4FromNatural  (i : nat )  : word4 :=  word4FromInteger ((Z.pred (Z.pos (P_of_succ_nat i)))).
(* [?]: removed value specification. *)

Definition word4FromBoollist  (lst : list (bool ))  : word4 :=  match ( bitSeqFromBoolList (List.rev lst)) with 
 | None => bs_to_w4(bitSeqFromInteger None ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))))
 | Some a => bs_to_w4 a
end.
(* [?]: removed value specification. *)

Definition boolListFromWord4  (w : word4 )  : list (bool ):=  List.rev (boolListFrombitSeq( 4%nat) (w4_to_bs w)).
(* [?]: removed value specification. *)

Definition word4FromNumeral  (w : nat )  : word4 :=  bs_to_w4 (bitSeqFromInteger None ((Z.pred (Z.pos (P_of_succ_nat w))))).
(* 

Instance x104_Numeral : Numeral word4 := {
   fromNumeral  :=  word4FromNumeral
}.
 *)
(* [?]: removed value specification. *)

Definition w4Eq   : word4  -> word4  -> bool :=  classical_boolean_equivalence.
(* [?]: removed value specification. *)

Definition w4Less  (bs1 : word4 ) (bs2 : word4 )  : bool :=  word4BinTest bitSeqLess bs1 bs2.
(* [?]: removed value specification. *)

Definition w4LessEqual  (bs1 : word4 ) (bs2 : word4 )  : bool :=  word4BinTest bitSeqLessEqual bs1 bs2.
(* [?]: removed value specification. *)

Definition w4Greater  (bs1 : word4 ) (bs2 : word4 )  : bool :=  word4BinTest bitSeqGreater bs1 bs2.
(* [?]: removed value specification. *)

Definition w4GreaterEqual  (bs1 : word4 ) (bs2 : word4 )  : bool :=  word4BinTest bitSeqGreaterEqual bs1 bs2.
(* [?]: removed value specification. *)

Definition w4Compare  (bs1 : word4 ) (bs2 : word4 )  : ordering :=  word4BinTest bitSeqCompare bs1 bs2.

Instance x103_Ord : Ord word4 := {
   compare  :=  w4Compare;
   isLess  :=  w4Less;
   isLessEqual  :=  w4LessEqual;
   isGreater  :=  w4Greater;
   isGreaterEqual  :=  w4GreaterEqual
}.


Instance x102_SetType : SetType word4 := {
   setElemCompare  :=  w4Compare
}.

(* [?]: removed value specification. *)

Definition word4Negate   : word4  -> word4 :=  word4UnaryOp bitSeqNegate.
(* [?]: removed value specification. *)

Definition word4Succ   : word4  -> word4 :=  word4UnaryOp bitSeqSucc.
(* [?]: removed value specification. *)

Definition word4Pred   : word4  -> word4 :=  word4UnaryOp bitSeqPred.
(* [?]: removed value specification. *)

Definition word4Lnot   : word4  -> word4 :=  word4UnaryOp bitSeqNot.
(* [?]: removed value specification. *)

Definition word4Add   : word4  -> word4  -> word4 :=  word4BinOp bitSeqAdd.
(* [?]: removed value specification. *)

Definition word4Minus   : word4  -> word4  -> word4 :=  word4BinOp bitSeqMinus.
(* [?]: removed value specification. *)

Definition word4Mult   : word4  -> word4  -> word4 :=  word4BinOp bitSeqMult.
(* [?]: removed value specification. *)

Definition word4IntegerDivision   : word4  -> word4  -> word4 :=  word4BinOp bitSeqDiv.
(* [?]: removed value specification. *)

Definition word4Division   : word4  -> word4  -> word4 :=  word4BinOp bitSeqDiv.
(* [?]: removed value specification. *)

Definition word4Remainder   : word4  -> word4  -> word4 :=  word4BinOp bitSeqMod.
(* [?]: removed value specification. *)

Definition word4Land   : word4  -> word4  -> word4 :=  word4BinOp bitSeqAnd.
(* [?]: removed value specification. *)

Definition word4Lor   : word4  -> word4  -> word4 :=  word4BinOp bitSeqOr.
(* [?]: removed value specification. *)

Definition word4Lxor   : word4  -> word4  -> word4 :=  word4BinOp bitSeqXor.
(* [?]: removed value specification. *)

Definition word4Min   : word4  -> word4  -> word4 :=  word4BinOp (bitSeqMin).
(* [?]: removed value specification. *)

Definition word4Max   : word4  -> word4  -> word4 :=  word4BinOp (bitSeqMax).
(* [?]: removed value specification. *)

Definition word4Power   : word4  -> nat  -> word4 :=  word4NatOp bitSeqPow.
(* [?]: removed value specification. *)

Definition word4Asr   : word4  -> nat  -> word4 :=  word4NatOp bitSeqArithmeticShiftRight.
(* [?]: removed value specification. *)

Definition word4Lsr   : word4  -> nat  -> word4 :=  word4NatOp bitSeqLogicalShiftRight.
(* [?]: removed value specification. *)

Definition word4Lsl   : word4  -> nat  -> word4 :=  word4NatOp bitSeqShiftLeft.


Instance x101_NumNegate : NumNegate word4 := {
   numNegate  :=  word4Negate
}.


Instance x100_NumAdd : NumAdd word4 := {
   numAdd  :=  word4Add
}.


Instance x99_NumMinus : NumMinus word4 := {
   numMinus  :=  word4Minus
}.


Instance x98_NumSucc : NumSucc word4 := {
   succ  :=  word4Succ
}.


Instance x97_NumPred : NumPred word4 := {
   pred  :=  word4Pred
}.


Instance x96_NumMult : NumMult word4 := {
   numMult  :=  word4Mult
}.


Instance x95_NumPow : NumPow word4 := {
   numPow  :=  word4Power
}.


Instance x94_NumIntegerDivision : NumIntegerDivision word4 := { 
   numIntegerDivision  :=  word4IntegerDivision
}.


Instance x93_NumDivision : NumDivision word4 := { 
   numDivision  :=  word4Division
}.


Instance x92_NumRemainder : NumRemainder word4 := { 
   numRemainder  :=  word4Remainder
}.


Instance x91_OrdMaxMin : OrdMaxMin word4 := { 
   max  :=  word4Max;
   min  :=  word4Min
}.


Instance x90_WordNot : WordNot word4 := { 
   lnot  :=  word4Lnot
}.


Instance x89_WordAnd : WordAnd word4 := { 
   conjunction  :=  word4Land
}.


Instance x88_WordOr : WordOr word4 := { 
   inclusive_or  :=  word4Lor
}.


Instance x87_WordXor : WordXor word4 := { 
   exclusive_or  :=  word4Lxor
}.


Instance x86_WordLsl : WordLsl word4 := { 
   left_shift  :=  word4Lsl
}.


Instance x85_WordLsr : WordLsr word4 := {
   logicial_right_shift  :=  word4Lsr
}.


Instance x84_WordAsr : WordAsr word4 := {
   arithmetic_right_shift  :=  word4Asr
}.

(* [?]: removed value specification. *)

Definition word4UGT  (a : word4 ) (b : word4 )  : bool :=  nat_gtb (word4ToNat a) (word4ToNat b).
