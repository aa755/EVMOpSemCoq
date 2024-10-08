(* Generated by Lem from lem/word256.lem. *)

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

Require Import helper.
Require Export helper.

Require Import Lem.lem_pervasives.
Require Export Lem.lem_pervasives.

Require Import Lem.lem_word.
Require Export Lem.lem_word.

(* 

Inductive word256 : Type :=  W256:  bool  ->  list  bool  -> word256 .
Definition word256_default: word256  := W256 bool_default DAEMON. *)
(* [?]: removed value specification. *)

(* 
Definition bs_to_w256  (seq : bitSequence )  : (Bvector  256) :=  match ( resizeBitSeq (Some 256%nat) seq) with 
 | BitSeq _ s b => W256 s b
end. *)
(* [?]: removed value specification. *)

(* 
Definition w256_to_bs   (W256(s : bool )(b : list (bool )))  : bitSequence :=  BitSeq (Some 256%nat) s b. *)
(* [?]: removed value specification. *)

Definition word256BinTest {a : Type}  (binop : bitSequence  -> bitSequence  -> a) (w1 : (Bvector  256) ) (w2 : (Bvector  256) )  : a:=  binop ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w1) ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w2).
(* [?]: removed value specification. *)

Definition word256BinOp  (binop : bitSequence  -> bitSequence  -> bitSequence ) (w1 : (Bvector  256) ) (w2 : (Bvector  256) )  : (Bvector  256) :=  (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) (binop ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w1) ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w2)).
(* [?]: removed value specification. *)

Definition word256NatOp  (binop : bitSequence  -> nat  -> bitSequence ) (w1 : (Bvector  256) ) (n : nat )  : (Bvector  256) :=  (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) (binop ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w1) n).
(* [?]: removed value specification. *)

Definition word256UnaryOp  (op : bitSequence  -> bitSequence ) (w : (Bvector  256) )  : (Bvector  256) :=  (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) (op ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w)).
(* [?]: removed value specification. *)

Definition size256   : Z :=  Coq.ZArith.Zpower.Zpower_nat((Z.pred (Z.pos (P_of_succ_nat 2%nat))))( 256%nat).
(* [?]: removed value specification. *)

(* 
Definition word256ToInteger  (w : (Bvector  256) )  : Z :=  integerFromBitSeq ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w). *)
(* [?]: removed value specification. *)

Definition word256ToNatural  (w : (Bvector  256) )  : nat :=  Z.abs_nat ( Coq.ZArith.Zdiv.Zmod((two_compl_value 255 w)) size256).
(* [?]: removed value specification. *)

Definition word256FromInteger  (i : Z )  : (Bvector  256) :=  (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) (bitSeqFromInteger (Some( 256%nat)) i).
(* [?]: removed value specification. *)

Definition word256FromInt  (i : Z )  : (Bvector  256) :=  (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) (bitSeqFromInteger (Some( 256%nat)) ( i)).
(* [?]: removed value specification. *)

Definition word256FromNatural  (i : nat )  : (Bvector  256) :=  word256FromInteger ((Z.pred (Z.pos (P_of_succ_nat i)))).
(* [?]: removed value specification. *)

Definition word256FromNat  (i : nat )  : (Bvector  256) :=  word256FromInteger ((Z.pred (Z.pos (P_of_succ_nat i)))).
(* [?]: removed value specification. *)

Definition word256FromBoollist  (lst : list (bool ))  : (Bvector  256) :=  match ( bitSeqFromBoolList (List.rev lst)) with 
 | None => (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w))(bitSeqFromInteger None ((Z.pred (Z.pos (P_of_succ_nat 0%nat)))))
 | Some a => (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) a
end.
(* [?]: removed value specification. *)

Definition boolListFromWord256  (w : (Bvector  256) )  : list (bool ):=  List.rev (boolListFrombitSeq( 256%nat) ((fun (w : (Bvector  256) ) => bitSeqFromInteger (Some 256%nat) ((two_compl_value 255 w))) w)).
(* [?]: removed value specification. *)

Definition word256FromNumeral  (w : nat )  : (Bvector  256) :=  (fun (w : bitSequence ) => Z_to_two_compl 255 (integerFromBitSeq w)) (bitSeqFromInteger None ((Z.pred (Z.pos (P_of_succ_nat w))))).
(* 

Instance x20_Numeral : Numeral (Bvector  256) := {
   fromNumeral   x :=  (word256FromNumeral x)
}.
 *)
(* [?]: removed value specification. *)

Definition w256Eq   : (Bvector  256)  -> (Bvector  256)  -> bool :=  classical_boolean_equivalence.
(* [?]: removed value specification. *)

Definition w256Less  (bs1 : (Bvector  256) ) (bs2 : (Bvector  256) )  : bool :=  word256BinTest bitSeqLess bs1 bs2.
(* [?]: removed value specification. *)

Definition w256LessEqual  (bs1 : (Bvector  256) ) (bs2 : (Bvector  256) )  : bool :=  word256BinTest bitSeqLessEqual bs1 bs2.
(* [?]: removed value specification. *)

Definition w256Greater  (bs1 : (Bvector  256) ) (bs2 : (Bvector  256) )  : bool :=  word256BinTest bitSeqGreater bs1 bs2.
(* [?]: removed value specification. *)

Definition w256GreaterEqual  (bs1 : (Bvector  256) ) (bs2 : (Bvector  256) )  : bool :=  word256BinTest bitSeqGreaterEqual bs1 bs2.
(* [?]: removed value specification. *)

Definition w256Compare  (bs1 : (Bvector  256) ) (bs2 : (Bvector  256) )  : ordering :=  word256BinTest bitSeqCompare bs1 bs2.

Instance x19_Ord : Ord (Bvector  256) := {
   compare  :=  w256Compare;
   isLess  :=  w256Less;
   isLessEqual  :=  w256LessEqual;
   isGreater  :=  w256Greater;
   isGreaterEqual  :=  w256GreaterEqual
}.


Instance x18_SetType : SetType (Bvector  256) := {
   setElemCompare  :=  w256Compare
}.

(* [?]: removed value specification. *)

Definition word256Negate   : (Bvector  256)  -> (Bvector  256) :=  word256UnaryOp bitSeqNegate.
(* [?]: removed value specification. *)

Definition word256Succ   : (Bvector  256)  -> (Bvector  256) :=  word256UnaryOp bitSeqSucc.
(* [?]: removed value specification. *)

Definition word256Pred   : (Bvector  256)  -> (Bvector  256) :=  word256UnaryOp bitSeqPred.
(* [?]: removed value specification. *)

Definition word256Lnot   : (Bvector  256)  -> (Bvector  256) :=  word256UnaryOp bitSeqNot.
(* [?]: removed value specification. *)

Definition word256Add   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqAdd.
(* [?]: removed value specification. *)

Definition word256Minus   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqMinus.
(* [?]: removed value specification. *)

Definition word256Mult   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqMult.
(* [?]: removed value specification. *)

Definition word256IntegerDivision   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqDiv.
(* [?]: removed value specification. *)

Definition word256Division   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqDiv.
(* [?]: removed value specification. *)

Definition word256Remainder   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqMod.
(* [?]: removed value specification. *)

Definition word256Land   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqAnd.
(* [?]: removed value specification. *)

Definition word256Lor   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqOr.
(* [?]: removed value specification. *)

Definition word256Lxor   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp bitSeqXor.
(* [?]: removed value specification. *)

Definition word256Min   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp (bitSeqMin).
(* [?]: removed value specification. *)

Definition word256Max   : (Bvector  256)  -> (Bvector  256)  -> (Bvector  256) :=  word256BinOp (bitSeqMax).
(* [?]: removed value specification. *)

Definition word256Power   : (Bvector  256)  -> nat  -> (Bvector  256) :=  word256NatOp bitSeqPow.
(* [?]: removed value specification. *)

Definition word256Asr   : (Bvector  256)  -> nat  -> (Bvector  256) :=  word256NatOp bitSeqArithmeticShiftRight.
(* [?]: removed value specification. *)

Definition word256Lsr   : (Bvector  256)  -> nat  -> (Bvector  256) :=  word256NatOp bitSeqLogicalShiftRight.
(* [?]: removed value specification. *)

Definition word256Lsl   : (Bvector  256)  -> nat  -> (Bvector  256) :=  word256NatOp bitSeqShiftLeft.


Instance x17_NumNegate : NumNegate (Bvector  256) := {
   numNegate  :=  word256Negate
}.


Instance x16_NumAdd : NumAdd (Bvector  256) := {
   numAdd  :=  word256Add
}.


Instance x15_NumMinus : NumMinus (Bvector  256) := {
   numMinus  :=  word256Minus
}.


Instance x14_NumSucc : NumSucc (Bvector  256) := {
   succ  :=  word256Succ
}.


Instance x13_NumPred : NumPred (Bvector  256) := {
   pred  :=  word256Pred
}.


Instance x12_NumMult : NumMult (Bvector  256) := {
   numMult  :=  word256Mult
}.


Instance x11_NumPow : NumPow (Bvector  256) := {
   numPow  :=  word256Power
}.


Instance x10_NumIntegerDivision : NumIntegerDivision (Bvector  256) := { 
   numIntegerDivision  :=  word256IntegerDivision
}.


Instance x9_NumDivision : NumDivision (Bvector  256) := { 
   numDivision  :=  word256Division
}.


Instance x8_NumRemainder : NumRemainder (Bvector  256) := { 
   numRemainder  :=  word256Remainder
}.


Instance x7_OrdMaxMin : OrdMaxMin (Bvector  256) := { 
   max  :=  word256Max;
   min  :=  word256Min
}.


Instance x6_WordNot : WordNot (Bvector  256) := { 
   lnot  :=  word256Lnot
}.


Instance x5_WordAnd : WordAnd (Bvector  256) := { 
   conjunction  :=  word256Land
}.


Instance x4_WordOr : WordOr (Bvector  256) := { 
   inclusive_or  :=  word256Lor
}.


Instance x3_WordXor : WordXor (Bvector  256) := { 
   exclusive_or  :=  word256Lxor
}.


Instance x2_WordLsl : WordLsl (Bvector  256) := { 
   left_shift  :=  word256Lsl
}.


Instance x1_WordLsr : WordLsr (Bvector  256) := {
   logicial_right_shift  :=  word256Lsr
}.


Instance x0_WordAsr : WordAsr (Bvector  256) := {
   arithmetic_right_shift  :=  word256Asr
}.

(* [?]: removed value specification. *)

Definition word256UGT  (a : (Bvector  256) ) (b : (Bvector  256) )  : bool :=  nat_gtb (word256ToNatural a) (word256ToNatural b).
(* [?]: removed value specification. *)

Definition word256ULT  (a : (Bvector  256) ) (b : (Bvector  256) )  : bool :=  nat_ltb (word256ToNatural a) (word256ToNatural b).
(* [?]: removed value specification. *)

Definition word256UGE  (a : (Bvector  256) ) (b : (Bvector  256) )  : bool :=  nat_gteb (word256ToNatural a) (word256ToNatural b).

