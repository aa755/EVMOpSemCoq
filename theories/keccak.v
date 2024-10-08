(* Generated by Lem from lem/keccak.lem. *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Program.Wf.

Require Import Lem.coqharness.

Open Scope nat_scope.
Open Scope string_scope.

(**)
(* Copyright 2016 Sami MÃ¤kelÃ¤ *)
(**)
(* Licensed under the Apache License; Version 2.0 (the "License"); *)
(* you may not use this file except in compliance with the License. *)
(* You may obtain a copy of the License at *)
(* *)
(*     http://www.apache.org/licenses/LICENSE-2.0 *)
(* *)
(* Unless required by applicable law or agreed to in writing; software *)
(* distributed under the License is distributed on an "AS IS" BASIS; *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND; either express or implied. *)
(* See the License for the specific language governing permissions and *)
(* limitations under the License. *)

Require Import Lem.lem_pervasives.
Require Export Lem.lem_pervasives.

Require Import word8.
Require Export word8.

Require Import word256.
Require Export word256.

Require Import word64.
Require Export word64.

(* [?]: removed value specification. *)

Definition rotl64  (w : word64 ) (n : nat )  : word64 :=  word64Lor ( word64Lsr w ( Coq.Init.Peano.minus( 64%nat) n)) ( word64Lsl w n).
(* [?]: removed value specification. *)

Definition big   : word64 :=  word64Lsl(word64FromNumeral 1%nat)( 63%nat).
(* [?]: removed value specification. *)

Definition two31   : word64 :=  word64Lsl(word64FromNumeral 1%nat)( 31%nat).
(* [?]: removed value specification. *)

Definition two15   : word64 :=  word64Lsl(word64FromNumeral 1%nat)( 15%nat).
(* [?]: removed value specification. *)

Definition keccakf_randc   : list (word64 ):=  [word64FromNumeral 1%nat; word64Lor(word64FromNumeral 130%nat) two15; word64Lor (word64Lor(word64FromNumeral 138%nat) big) two15; word64Lor (word64Lor (word64Lor(word64FromNumeral 0%nat) big) two31) two15; word64Lor(word64FromNumeral 139%nat) two15; word64Lor(word64FromNumeral 1%nat) two31; word64Lor (word64Lor (word64Lor(word64FromNumeral 129%nat) big) two31) two15; word64Lor (word64Lor(word64FromNumeral 9%nat) big) two15;word64FromNumeral 138%nat;word64FromNumeral 136%nat; word64Lor (word64Lor(word64FromNumeral 9%nat) two31) two15;  word64Lor(word64FromNumeral 10%nat) two31; word64Lor (word64Lor(word64FromNumeral 139%nat) two31) two15; word64Lor(word64FromNumeral 139%nat) big; word64Lor (word64Lor(word64FromNumeral 137%nat) big) two15; word64Lor (word64Lor(word64FromNumeral 3%nat) big) two15; word64Lor (word64Lor(word64FromNumeral 2%nat) big) two15; word64Lor(word64FromNumeral 128%nat) big; word64Lor(word64FromNumeral 10%nat) two15; word64Lor (word64Lor(word64FromNumeral 10%nat) big) two31; word64Lor (word64Lor (word64Lor(word64FromNumeral 129%nat) big) two31) two15; word64Lor (word64Lor(word64FromNumeral 128%nat) big) two15; word64Lor(word64FromNumeral 1%nat) two31; word64Lor (word64Lor (word64Lor(word64FromNumeral 8%nat) big) two31) two15]
.
(* [?]: removed value specification. *)

Definition keccakf_rotc   : list (nat ):=  [ 1%nat; 3%nat; 6%nat; 10%nat; 15%nat; 21%nat; 28%nat; 36%nat; 45%nat; 55%nat; 2%nat; 14%nat; 27%nat; 41%nat; 56%nat; 8%nat; 25%nat; 43%nat; 62%nat; 18%nat; 39%nat; 61%nat; 20%nat; 44%nat]
.
(* [?]: removed value specification. *)

Definition keccakf_piln   : list (nat ):=  [ 10%nat; 7%nat; 11%nat; 17%nat; 18%nat; 3%nat; 5%nat; 16%nat; 8%nat; 21%nat; 24%nat; 4%nat; 15%nat; 23%nat; 19%nat; 13%nat; 12%nat; 2%nat; 20%nat; 14%nat; 22%nat; 9%nat; 6%nat; 1%nat]
.
(* [?]: removed value specification. *)

Definition get  (lst : list (word64 )) (n : nat )  : word64 :=  match ( index lst n) with 
 | Some x => x
 | None =>word64FromNumeral 0%nat
end.
(* [?]: removed value specification. *)

Definition get_n  (lst : list (nat )) (n : nat )  : nat :=  match ( index lst n) with 
 | Some x => x
 | None => 0%nat
end.
(* [?]: removed value specification. *)

Definition setf  (lst : list (word64 )) (n : nat ) (w : word64 )  : list (word64 ):= 
  if nat_ltb (List.length lst) n then  (@ List.app _) ((@ List.app _)lst (genlist (fun ( _ : nat ) =>word64FromNumeral 0%nat) ( Coq.Init.Peano.minus (Coq.Init.Peano.minus(List.length lst) n)( 1%nat)))) [w]
  else  (@ List.app _) ((@ List.app _)(take n lst) [w]) (drop (Coq.Init.Peano.plus n( 1%nat)) lst).
(* [?]: removed value specification. *)

Definition theta1  (i : nat ) (st : list (word64 ))  : word64 :=  word64Lxor (word64Lxor (word64Lxor (word64Lxor
  (get st i)
  (get st ( Coq.Init.Peano.plus i( 5%nat))))
  (get st ( Coq.Init.Peano.plus i( 10%nat))))
  (get st ( Coq.Init.Peano.plus i( 15%nat))))
  (get st ( Coq.Init.Peano.plus i( 20%nat))).
(* [?]: removed value specification. *)

Definition theta_t  (i : nat ) (bc : list (word64 ))  : word64 :=  word64Lxor
  (get bc ( Nat.modulo( Coq.Init.Peano.plus i( 4%nat))( 5%nat))) (rotl64 (get bc ( Nat.modulo( Coq.Init.Peano.plus i( 1%nat))( 5%nat)))( 1%nat)).
(* [?]: removed value specification. *)

Definition theta  (st : list (word64 ))  : list (word64 ):= 
  let bc := genlist (fun (i : nat ) => theta1 i st)( 5%nat) in
  let t := genlist (fun (i : nat ) => theta_t i bc)( 5%nat) in
  genlist (fun (ji : nat ) => word64Lxor (get st ji) (get t ( Nat.modulo ji( 5%nat))))( 25%nat).
(* [?]: removed value specification. *)

Definition rho_pi_inner  (t_st : (word64 *list (word64 )) % type) (i : nat )  : (word64 *list (word64 )) % type:= 
  let j := get_n keccakf_piln i in
  let bc := get ((@ snd _ _) t_st) j in
  (bc, setf ((@ snd _ _) t_st) j (rotl64 ((@ fst _ _) t_st) (get_n keccakf_rotc i))).
(* [?]: removed value specification. *)

Definition rho_pi_changes  (i : nat ) (t_st : (word64 *list (word64 )) % type)  : (word64 *list (word64 )) % type:=  List.fold_left rho_pi_inner (genlist (fun (x : nat ) => x) i) t_st.
(* [?]: removed value specification. *)

Definition rho_pi  (st : list (word64 ))  : list (word64 ):=  (@ snd _ _) (rho_pi_changes( 24%nat) (get st( 1%nat), st)).
(* [?]: removed value specification. *)

Definition chi_for_j  (st_slice : list (word64 ))  : list (word64 ):= 
  genlist (fun (i : nat ) => word64Lxor (get st_slice i) ( word64Land(word64Lnot (get st_slice ( Nat.modulo( Coq.Init.Peano.plus i( 1%nat))( 5%nat)))) (get st_slice ( Nat.modulo( Coq.Init.Peano.plus i( 2%nat))( 5%nat)))))( 5%nat).
(* [?]: removed value specification. *)

Definition filterI {a : Type}  (lst : list a) (pred : nat  -> bool )  : list a:= 
  List.map (@ fst _ _) (List.filter (fun (p : (a*nat ) % type) => pred ((@ snd _ _) p)) (zip lst (genlist (fun (i : nat ) => i) (List.length lst)))).
(* [?]: removed value specification. *)

Definition chi  (st : list (word64 ))  : list (word64 ):= 
  lem_list.concat (genlist (fun (j : nat ) => chi_for_j (filterI st (fun (i : nat ) => nat_lteb (Coq.Init.Peano.mult j( 5%nat)) i && nat_lteb i (Coq.Init.Peano.plus(Coq.Init.Peano.mult j( 5%nat))( 5%nat)))))( 5%nat)).
(* [?]: removed value specification. *)

Definition iota  (r : nat ) (st : list (word64 ))  : list (word64 ):=  setf st( 0%nat) ( word64Lxor(get st( 0%nat)) (get keccakf_randc r)).
(* [?]: removed value specification. *)

Definition for_inner  (st : list (word64 )) (r : nat )  : list (word64 ):=  iota r (chi (rho_pi (theta st))).

Definition keccakf_rounds    :  nat :=  24%nat.

Definition byte : Type :=  word8 .
Definition byte_default: byte  := word8_default.
(* [?]: removed value specification. *)

Program Fixpoint word_rsplit_aux  (lst : list (bool )) (n : nat )  : list (word8 ):=  match ( n) with 
 | 0%nat => []
 |S (n) => word8FromBoollist (take( 8%nat) lst) :: word_rsplit_aux (drop( 8%nat) lst) n
end.
(* [?]: removed value specification. *)

Definition word_rsplit  (w : word64 )  : list (byte ):=  word_rsplit_aux (boolListFromWord64 w)( 8%nat).
(* [?]: removed value specification. *)

Definition word_rcat_k  (lst : list (word8 ))  : word64 :=  word64FromBoollist (lem_list.concat (List.map boolListFromWord8 lst)).
(* [?]: removed value specification. *)

Definition invert_endian  (w : word64 )  : word64 :=  word_rcat_k (List.rev (word_rsplit w)).
(* [?]: removed value specification. *)

Definition keccakf  (st : list (word64 ))  : list (word64 ):=  List.fold_left for_inner (genlist (fun (i : nat ) => i) keccakf_rounds) st.

Definition mdlen    :  nat :=  Nat.div( 256%nat)( 8%nat).
Definition rsiz    :  nat :=  Coq.Init.Peano.minus( 200%nat) (Coq.Init.Peano.mult mdlen( 2%nat)).
(* [?]: removed value specification. *)

Definition word8_to_word64  (w : word8 )  : word64 :=  word64FromNat (word8ToNat w).
(* [?]: removed value specification. *)

Definition update_byte  (i : word8 ) (p : nat ) (st : list (word64 ))  : list (word64 ):=  setf st ( Nat.div p( 8%nat)) ( word64Lxor(get st ( Nat.div p( 8%nat))) ( word64Lsl(word8_to_word64 i) ( Coq.Init.Peano.mult( 8%nat) ( Nat.modulo p( 8%nat))))).
(* [?]: removed value specification. *)

Program Fixpoint sha3_update  (lst : list (word8 )) (pos : nat ) (st : list (word64 ))  : (nat *list (word64 )) % type:=  match ( lst) with 
 | [] => (pos, st)
 | c :: rest =>
    if ( nat_lteb pos rsiz) then sha3_update rest ( Coq.Init.Peano.plus pos( 1%nat)) (update_byte c pos st)
   else sha3_update rest( 0%nat) (keccakf (update_byte c pos st))
end.
(* [?]: removed value specification. *)

Definition keccak_final  (p : nat ) (st : list (word64 ))  : list (word8 ):= 
   let st0 := update_byte(word8FromNumeral 1%nat) p st in
   let st1 := update_byte(word8FromNumeral 128%nat) ( Coq.Init.Peano.minus rsiz( 1%nat)) st0 in
   let st2 := take( 4%nat) (keccakf st1) in
   lem_list.concat (List.map (fun (x : word64 ) => List.rev (word_rsplit x)) st2).

Definition initial_st    :  list  word64 :=  genlist (fun ( _ : nat ) =>word64FromNumeral 0%nat)( 25%nat).

Definition initial_pos    :  nat :=  0%nat.
(* [?]: removed value specification. *)

Definition keccak'  (input : list (byte ))  : list (byte ):= 
   let mid := sha3_update input initial_pos initial_st in
   keccak_final ((@ fst _ _) mid) ((@ snd _ _) mid).

Definition w256 : Type :=  (Bvector  256) .
Definition w256_default: w256  := word256_default.
(* [?]: removed value specification. *)

Definition list_fill_right  (filled : bool ) (target : nat ) (orig : list (bool ))  : list (bool ):= 
  if nat_gteb (List.length orig) target then orig else
  let filling_len := Coq.Init.Peano.minus target (List.length orig) in
  (@ List.app _) orig (replicate filling_len filled).
(* [?]: removed value specification. *)

Definition list_fill_left  (filled : bool ) (target : nat ) (orig : list (bool ))  : list (bool ):= 
  if nat_gteb (List.length orig) target then orig else
  let filling_len := Coq.Init.Peano.minus target (List.length orig) in
  (@ List.app _) (replicate filling_len filled) orig.
(* [?]: removed value specification. *)

Definition word_of_bytes  (lst : list (word8 ))  : (Bvector  256) :=  word256FromBoollist
                          (list_fill_left false( 256%nat)
                            (lem_list.concat (List.map boolListFromWord8 lst))).
(* [?]: removed value specification. *)

Definition keccak  (input : list (byte ))  : (Bvector  256) :=  word_of_bytes (keccak' input).


