(* Generated by Lem from list.lem. *)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import String.
Require Import Program.Wf.

Require Import coqharness.

Open Scope nat_scope.
Open Scope string_scope.

 

Require Import lem_bool.
Require Export lem_bool.
Require Import lem_maybe.
Require Export lem_maybe.
Require Import lem_basic_classes.
Require Export lem_basic_classes.
Require Import lem_function.
Require Export lem_function.
Require Import lem_tuple.
Require Export lem_tuple.
Require Import lem_num.
Require Export lem_num.


Require Import Coq.Lists.List.
Require Export Coq.Lists.List.



(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

Definition null {a : Type}  (l : list a)  : bool :=  match ( l) with  [] => true | _ => false end.
(* [?]: removed value specification. *)

(* 
Program Fixpoint length {a : Type}  (l : list a)  : nat := 
  match ( l) with 
    | [] => 0%nat
    | x :: xs => instance_Num_NumAdd_nat.+ List.length xs 1%nat
  end. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

(* 

Program Fixpoint listEqualBy {a : Type}  (eq : a -> a -> bool ) (l1 : list a) (l2 : list a)  : bool :=  match ( (l1,l2)) with 
  | ([],  []) => true
  | ([], ( _::_)) => false
  | ((_::_),  []) => false
  | (x::xs,  y :: ys) => (eq x y && list_equal_by eq xs ys)
end. *)
(* [?]: removed top-level value definition. *)

Instance x145_Eq{a: Type} `{Eq a}: Eq (list  a):= {
   isEqual  :=  (list_equal_by (fun x y => x = y));
   isInequal   l1  l2 :=  negb ((list_equal_by (fun x y => x = y) l1 l2))
}.

(* [?]: removed value specification. *)

(* [?]: removed value specification. *)


Program Fixpoint lexicographicCompareBy {a : Type}  (cmp : a -> a -> ordering ) (l1 : list a) (l2 : list a)  : ordering :=  match ( (l1,l2)) with 
  | ([],  []) => EQ
  | ([],  _::_) => LT
  | (_::_,  []) => GT
  | (x::xs,  y::ys) => (* begin block *)
      match ( cmp x y) with  
        | LT => LT
        | GT => GT
        | EQ => lexicographicCompareBy cmp xs ys
      end
    (* end block *)
end.
(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

Program Fixpoint lexicographicLessBy {a : Type}  (less : a -> a -> bool ) (less_eq : a -> a -> bool ) (l1 : list a) (l2 : list a)  : bool :=  match ( (l1,l2)) with 
  | ([],  []) => false
  | ([],  _::_) => true
  | (_::_,  []) => false
  | (x::xs,  y::ys) => ((less x y) || ((less_eq x y) && (lexicographicLessBy less less_eq xs ys)))
end.
(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)

Program Fixpoint lexicographicLessEqBy {a : Type}  (less : a -> a -> bool ) (less_eq : a -> a -> bool ) (l1 : list a) (l2 : list a)  : bool :=  match ( (l1,l2)) with 
  | ([],  []) => true
  | ([],  _::_) => true
  | (_::_,  []) => false
  | (x::xs,  y::ys) => (less x y || (less_eq x y && lexicographicLessEqBy less less_eq xs ys))
end.
(* [?]: removed top-level value definition. *)


Instance x144_Ord{a: Type} `{Ord a}: Ord (list  a):= {
   compare  :=  (lexicographicCompareBy compare);
   isLess  :=  (lexicographicLessBy isLess isLessEqual);
   isLessEqual  :=  (lexicographicLessEqBy isLess isLessEqual);
   isGreater   x  y :=  (lexicographicLessBy isLess isLessEqual y x);
   isGreaterEqual   x  y :=  (lexicographicLessEqBy isLess isLessEqual y x)
}.

(* [?]: removed value specification. *)

(*  (* originally append *)
Program Fixpoint append {a : Type}  (xs : list a) (ys : list a)  : list a:=  match ( xs) with 
                     | [] => ys
                     | x :: xs' => x :: ( (@ List.app _)xs' ys)
                   end. *)
(* [?]: removed value specification. *)

(* 
Definition snoc {a : Type}  (e : a) (l : list a)  : list a:=  (@ List.app _) l [e]. *)
(* [?]: removed value specification. *)
 (* originally named rev_append *)
Program Fixpoint reverseAppend {a : Type}  (l1 : list a) (l2 : list a)  : list a:=  match ( l1) with  
                                | [] => l2
                                | x :: xs => reverseAppend xs (x :: l2)
                               end.
(* [?]: removed value specification. *)

(*  (* originally named rev *)
Definition reverse {a : Type}  (l : list a)  : list a:=  reverseAppend l []. *)
(* [?]: removed value specification. *)

Program Fixpoint map_tr {a b : Type}  (rev_acc : list b) (f : a -> b) (l : list a)  : list b:=  match ( l) with 
  | [] => List.rev rev_acc
  | x :: xs => map_tr ((f x) :: rev_acc) f xs
end.
(* [?]: removed value specification. *)

Program Fixpoint count_map {a b : Type}  (f : a -> b) (l : list a) (ctr : nat )  : list b:=   
  match ( l) with   
  | []       => []  
  | hd :: tl => f hd :: 
    (if nat_ltb ctr( 5000%nat) then count_map f tl ( Coq.Init.Peano.plus ctr( 1%nat)) 
    else map_tr [] f tl)
  end.
(* [?]: removed value specification. *)

(* 
Definition map {a b : Type}  (f : a -> b) (l : list a)  : list b:=  count_map f l 0%nat. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(*  (* originally foldl *)

Program Fixpoint foldl {a b : Type}  (f : a -> b -> a) (b : a) (l : list b)  : a:=  match ( l) with 
  | []      => b
  | x :: xs => List.fold_left f xs (f b x)
end. *)
(* [?]: removed value specification. *)

(*  (* originally foldr with different argument order *)
Program Fixpoint foldr {a b : Type}  (f : a -> b -> b) (b : b) (l : list a)  : b:=  match ( l) with 
  | []      => b
  | x :: xs => f x (List.fold_right f b xs)
end. *)
(* [?]: removed value specification. *)
 (* before also called "flatten" *)
Definition concat {a : Type}   : list (list a) -> list a:=  List.fold_right (@ List.app _) [].
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(*  (* originally for_all *)
Definition all {a : Type}  (P : a -> bool ) (l : list a)  : bool :=  List.fold_left (fun (r : bool ) (e : a) => P e && r) l true. *)
(* [?]: removed value specification. *)

(*  (* originally exist *)
Definition any {a : Type}  (P : a -> bool ) (l : list a)  : bool :=  List.fold_left (fun (r : bool ) (e : a) => P e || r) l false. *)
(* [?]: removed value specification. *)
 

Program Fixpoint dest_init_aux {a : Type}  (rev_init : list a) (last_elem_seen : a) (to_process : list a)  : (list a*a) % type:= 
  match ( to_process) with 
    | []    => (List.rev rev_init, last_elem_seen)
    | x::xs => dest_init_aux (last_elem_seen::rev_init) x xs
  end.

Definition dest_init {a : Type}  (l : list a)  : option ((list a*a) % type) :=  match ( l) with 
  | [] => None
  | x::xs => Some (dest_init_aux [] x xs)
end.
(* [?]: removed value specification. *)


Program Fixpoint index {a : Type}  (l : list a) (n : nat )  : option a :=  match ( l) with  
  | []      => None
  | x :: xs => if beq_nat n( 0%nat) then Some x else index xs (Coq.Init.Peano.minus n( 1%nat))
end.
(* [?]: removed value specification. *)


Program Fixpoint findIndices_aux {a : Type}   (i:nat ) (P : a -> bool ) (l : list a)  : list (nat ):= 
  match ( l) with 
    | []      => []
    | x :: xs => if P x then i :: findIndices_aux ( Coq.Init.Peano.plus i( 1%nat)) P xs else findIndices_aux ( Coq.Init.Peano.plus i( 1%nat)) P xs
 end.
Definition findIndices {a : Type}  (P : a -> bool ) (l : list a)  : list (nat ):=  findIndices_aux( 0%nat) P l.
(* [?]: removed value specification. *)

Definition findIndex {a : Type}  (P : a -> bool ) (l : list a)  : option (nat ) :=  match ( findIndices P l) with 
  | [] => None
  | x :: _ => Some x
end.
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)



Program Fixpoint genlist {a : Type}  (f : nat  -> a)  (n : nat )  : list a:= 
  match ( (n :  nat )) with 
    | 0%nat => []
    | S (n') =>  (@ List.app _)(genlist f n') [(f n')]
  end.
(* [?]: removed value specification. *)

Program Fixpoint replicate {a : Type}  (n : nat ) (x : a)  : list a:= 
  match ( n) with 
    | 0%nat => []
    | S (n') => x :: replicate n' x
  end.
(* [?]: removed value specification. *)

Program Fixpoint splitAtAcc {a : Type}  (revAcc : list a) (n : nat ) (l : list a)  : (list a*list a) % type:=  
  match ( l) with 
    | []    => (List.rev revAcc, [])
    | x::xs => if nat_lteb n( 0%nat) then (List.rev revAcc, l) else splitAtAcc (x::revAcc) (Coq.Init.Peano.minus n( 1%nat)) xs
  end.
(* [?]: removed value specification. *)

Definition splitAt {a : Type}  (n : nat ) (l : list a)  : (list a*list a) % type:=  
   splitAtAcc [] n l.
(* [?]: removed value specification. *)

Definition take {a : Type}  (n : nat ) (l : list a)  : list a:=  (@ fst _ _) (splitAt n l).
(* [?]: removed value specification. *)

Definition drop {a : Type}  (n : nat ) (l : list a)  : list a:=  (@ snd _ _) (splitAt n l).
(* [?]: removed value specification. *)

Program Fixpoint splitWhile_tr {a : Type}  (p : a -> bool ) (xs : list a) (acc : list a)  : (list a*list a) % type:=  match ( xs) with 
  | []    =>
    (List.rev acc, [])
  | x::xs =>
    if p x then
      splitWhile_tr p xs (x::acc)
    else
      (List.rev acc, (x::xs))
end.
(* [?]: removed value specification. *)

Definition splitWhile {a : Type}  (p : a -> bool ) (xs : list a)  : (list a*list a) % type:=  splitWhile_tr p xs [].
(* [?]: removed value specification. *)

Definition takeWhile {a : Type}  (p : a -> bool ) (l : list a)  : list a:=  (@ fst _ _) (splitWhile p l).
(* [?]: removed value specification. *)

Definition dropWhile {a : Type}  (p : a -> bool ) (l : list a)  : list a:=  (@ snd _ _) (splitWhile p l).
(* [?]: removed value specification. *)

Program Fixpoint isPrefixOf {a : Type} `{Eq a}  (l1 : list a) (l2 : list a)  : bool :=  match ( (l1, l2)) with 
  | ([],  _) => true
  | (_::_,  []) => false
  | (x::xs,  y::ys) => (x = y) && isPrefixOf xs ys
end.
(* [?]: removed value specification. *)

Program Fixpoint update {a : Type}  (l : list a) (n : nat ) (e : a)  : list a:=  
  match ( l) with 
    | []      => []
    | x :: xs => if beq_nat n( 0%nat) then e :: xs else x :: (update xs ( Coq.Init.Peano.minus n( 1%nat)) e)
end.
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)


Definition elemBy {a : Type}  (eq : a -> a -> bool ) (e : a) (l : list a)  : bool :=  List.existsb (eq e) l.
Definition elem {a : Type} `{Eq a}   : a -> list a -> bool :=  elemBy (fun x y => x = y).
(* [?]: removed value specification. *)
 (* previously not of maybe type *)
Program Fixpoint find {a : Type}  (P : a -> bool ) (l : list a)  : option a :=  match ( l) with  
  | []      => None
  | x :: xs => if P x then Some x else find P xs
end.
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)


(* DPM: eta-expansion for Coq backend type-inference. *)
Definition lookupBy {a b : Type}  (eq : a -> a -> bool ) (k : a) (m : list ((a*b) % type))  : option b :=  option_map (fun (x : (a*b) % type) => (@ snd _ _) x) (find (
  fun (p : (a*b) % type) => match ( (p) ) with ( (k',  _)) => eq k k' end) m).
(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)

(* 
Program Fixpoint filter {a : Type}  (P : a -> bool ) (l : list a)  : list a:=  match ( l) with 
                       | [] => []
                       | x :: xs => if (P x) then x :: (List.filter P xs) else List.filter P xs
                     end. *)
(* [?]: removed value specification. *)

Definition partition {a : Type}  (P : a -> bool ) (l : list a)  : (list a*list a) % type:=  (List.filter P l, List.filter (fun (x : a) => negb (P x)) l).
(* [?]: removed value specification. *)

Definition reversePartition {a : Type}  (P : a -> bool ) (l : list a)  : (list a*list a) % type:=  partition P (List.rev l).
(* [?]: removed value specification. *)
 
Program Fixpoint deleteFirst {a : Type}  (P : a -> bool ) (l : list a)  : option (list a) :=  match ( l) with 
                            | [] => None
                            | x :: xs => if (P x) then Some xs else option_map (fun (xs' : list a) => x :: xs') (deleteFirst P xs)
                          end.
(* [?]: removed value specification. *)

(* [?]: removed value specification. *)


Definition deleteBy {a : Type}  (eq : a -> a -> bool ) (x : a) (l : list a)  : list a:=  fromMaybe l (deleteFirst (eq x) l).
(* [?]: removed top-level value definition. *)
(* [?]: removed value specification. *)
 (* before combine *)
Program Fixpoint zip {a b : Type}  (l1 : list a) (l2 : list b)  : list ((a*b) % type):=  match ( (l1, l2)) with 
  | (x :: xs,  y :: ys) => (x, y) :: zip xs ys
  | _ => []
end.
(* [?]: removed value specification. *)

Program Fixpoint unzip {a b : Type}  (l : list ((a*b) % type))  : (list a*list b) % type:=  match ( l) with 
  | [] => ([], [])
  | (x,  y) :: xys => 
  match ( unzip xys) with (xs,  ys) => ((x :: xs), (y :: ys)) end
end.


Instance x143_SetType{a: Type} `{SetType a}: SetType (list  a):= {
  setElemCompare  :=  lexicographicCompareBy setElemCompare
}.

(* [?]: removed value specification. *)

Program Fixpoint allDistinct {a : Type} `{Eq a}  (l : list a)  : bool :=  
  match ( l) with 
    | [] => true
    |( x::l') => negb (elem x l') && allDistinct l'
  end.
(* [?]: removed value specification. *)

Program Fixpoint mapMaybe {a b : Type}  (f : a -> option b ) (xs : list a)  : list b:= 
  match ( xs) with 
  | [] => []
  | x::xs =>
      match ( f x) with 
      | None => mapMaybe f xs
      | Some y => y :: (mapMaybe f xs)
      end
  end.
(* [?]: removed value specification. *)

Program Fixpoint mapiAux {a b : Type}  (f : nat  -> b -> a)  (n : nat ) (l : list b)  : list a:=  match ( l) with 
  | [] => []
  | x :: xs => (f n x) :: mapiAux f ( Coq.Init.Peano.plus n( 1%nat)) xs
end.
Definition mapi {a b : Type}  (f : nat  -> a -> b) (l : list a)  : list b:=  mapiAux f( 0%nat) l.
(* [?]: removed value specification. *)

Definition deletes {a : Type} `{Eq a}  (xs : list a) (ys : list a)  : list a:= 
  List.fold_left (flip (deleteBy (fun x y => x = y))) ys xs.
(* [?]: removed value specification. *)

Program Fixpoint catMaybes {a : Type}  (xs : list (option a ))  : list a:= 
  match ( xs) with 
    | [] =>
        []
    |( None :: xs') =>
        catMaybes xs'
    |( Some x :: xs') =>
        x :: catMaybes xs'
  end.
