(* week-01_about-reversing-a-list-and-mirroring-a-tree.v *)
(* MR 2024 - YSC4217 2024-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 15 Aug 2024 *)

(* ********** *)

(* This warmup exercise is a study of list reversal and tree mirroring. *)

(* About style:

   - when you use the Light of Inductil,
     make sure to provide the argument(s) of the induction hypothesis when you apply it

   - there is no need to provide the arguments of most of the other lemmas you apply,
     unless you feel that

     + it is necessary, or

     + it makes the proof clearer. *)

(* Note:
   The point of this warmup exercise is not to do everything in a stressed hurry.
   The point is to do well what you have the time to do, and to re-acquire basic tCPA reflexes. *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List.

(* ********** *)

(* Background material, Part I/II: lists.

   list_append, list_reverse, and list_reverse_alt,
   their associated fold-unfold lemmas,
   and some of their properties *)

(* ***** *)

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
    nil =>
    match v2s with
      nil =>
      true
    | v2 :: v2s' =>
      false
    end
  | v1 :: v1s' =>
    match v2s with
      nil =>
      false
    | v2 :: v2s' =>
      eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
    end
  end.

Definition test_list_append (candidate : forall V : Type, list V -> list V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil nil)
     nil)
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate nat (1 :: 2 :: nil) (3 :: 4 :: nil))
     (1 :: 2 :: 3 :: 4 :: nil))
  (* etc. *)
  .

Fixpoint list_append (V : Type) (v1s v2s : list V) : list V :=
  match v1s with
    nil =>
    v2s
  | v1 :: v1s' =>
    v1 :: list_append V v1s' v2s
end.

Compute (test_list_append list_append).

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    list_append V nil v2s =
    v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    list_append V (v1 :: v1s') v2s =
    v1 :: list_append V v1s' v2s.
Proof.
  fold_unfold_tactic list_append.
Qed.

Property nil_is_left_neutral_for_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V nil vs = vs.
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

Property nil_is_right_neutral_for_list_append :
  forall (V : Type)
         (vs : list V),
    list_append V vs nil = vs.
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

Property list_append_is_associative :
  forall (V : Type)
         (v1s v2s v3s : list V),
    list_append V v1s (list_append V v2s v3s)
    =
    list_append V (list_append V v1s v2s) v3s.
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

Property about_applying_list_append_to_a_singleton_list :
  forall (V : Type)
         (v1 : V)
         (v2s : list V),
    list_append V (v1 :: nil) v2s = v1 :: v2s.
Proof.
  intros V v1 v2s.
  rewrite -> fold_unfold_list_append_cons.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.
Qed.  

(* ***** *)

Definition test_list_reverse (candidate : forall V : Type, list V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate nat nil)
     nil)
  &&
  (eqb_list
     nat
     Nat.eqb
     (candidate nat (1 :: 2 :: nil))
     (2 :: 1 :: nil))
  (* etc. *)
  .

Fixpoint list_reverse (V : Type) (vs : list V) : list V :=
  match vs with
    nil =>
    nil
  | v :: vs' =>
    list_append V (list_reverse V vs') (v :: nil)
  end.

Compute (test_list_reverse list_reverse).

Lemma fold_unfold_list_reverse_nil :
  forall (V : Type),
    list_reverse V nil =
    nil.
Proof.
  fold_unfold_tactic list_reverse.
Qed.

Lemma fold_unfold_list_reverse_cons :
  forall (V : Type)
         (v : V)
         (vs' : list V),
    list_reverse V (v :: vs') =
    list_append V (list_reverse V vs') (v :: nil).
Proof.
  fold_unfold_tactic list_reverse.
Qed.

Property about_applying_list_reverse_to_a_singleton_list :
  forall (V : Type)
         (v : V),
    list_reverse V (v :: nil) = v :: nil.
Proof.
  intros V v.
  rewrite -> fold_unfold_list_reverse_cons.
  rewrite -> fold_unfold_list_reverse_nil.
  rewrite -> fold_unfold_list_append_nil.
  reflexivity.
Qed.

Property list_append_and_list_reverse_commute_with_each_other :
  forall (V : Type)
         (v1s v2s : list V),
    list_reverse V (list_append V v1s v2s)
    =
    list_append V (list_reverse V v2s) (list_reverse V v1s).
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

(* ***** *)

Fixpoint list_reverse_acc (V : Type) (v1s a : list V) : list V :=
  match v1s with
    nil =>
    a
  | v1 :: v1s' =>
    list_reverse_acc V v1s' (v1 :: a)
  end.

Lemma fold_unfold_list_reverse_acc_nil :
  forall (V : Type)
         (a : list V),
    list_reverse_acc V nil a =
    a.
Proof.
  fold_unfold_tactic list_reverse_acc.
Qed.

Lemma fold_unfold_list_reverse_acc_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' a : list V),
    list_reverse_acc V (v1 :: v1s') a =
    list_reverse_acc V v1s' (v1 :: a).
Proof.
  fold_unfold_tactic list_reverse_acc.
Qed.

Definition list_reverse_alt (V : Type) (vs : list V) : list V :=
  list_reverse_acc V vs nil.

Compute (test_list_reverse list_reverse).

Property about_applying_list_reverse_acc_to_a_singleton_list :
  forall (V : Type)
         (v : V)
         (a : list V),
    list_reverse_acc V (v :: nil) a = v :: a.
Proof.
  intros V v a.
  rewrite -> fold_unfold_list_reverse_acc_cons.
  rewrite -> fold_unfold_list_reverse_acc_nil.
  reflexivity.
Qed.

Property list_append_and_list_reverse_acc_commute_with_each_other :
  forall (V : Type)
         (v1s v2s a : list V),
    list_reverse_acc V (list_append V v1s v2s) a
    =
    list_reverse_acc V v2s (list_reverse_acc V v1s a).
Proof.
Admitted. (* was proved in the FPP/LPP midterm project *)

(* ********** *)

(* Background material, Part II/II: binary trees.

   mirror, flatten, and flatten_alt
   and their associated fold-unfold lemmas *)

(* ***** *)

Inductive binary_tree (V : Type) : Type :=
  Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

Fixpoint eqb_binary_tree (V : Type) (eqb_V : V -> V -> bool) (t1 t2 : binary_tree V) : bool :=
  match t1 with
    Leaf _ v1 =>
    match t2 with
      Leaf _ v2 =>
      eqb_V v1 v2
    | Node _ t21 t22 =>
      false
    end
  | Node _ t11 t12 =>
    match t2 with
      Leaf _ v2 =>
      false
    | Node _ t21 t22 =>
      eqb_binary_tree V eqb_V t11 t21 && eqb_binary_tree V eqb_V t12 t22
    end
  end.

(* ***** *)

Definition test_binary_tree_mirror (candidate : forall V : Type, binary_tree V -> binary_tree V) : bool :=
  (eqb_binary_tree
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat (Leaf nat 1) (Leaf nat 2)))
     (Node nat (Leaf nat 2) (Leaf nat 1)))
  (* etc. *)
  .

Fixpoint binary_tree_mirror (V : Type) (t : binary_tree V) : binary_tree V :=
  match t with
    Leaf _ v =>
    Leaf V v
  | Node _ t1 t2 =>
    Node V (binary_tree_mirror V t2) (binary_tree_mirror V t1)
  end.

Compute (test_binary_tree_mirror binary_tree_mirror).

Lemma fold_unfold_binary_tree_mirror_Leaf :
  forall (V : Type)
         (v : V),
    binary_tree_mirror V (Leaf V v) =
    Leaf V v.
Proof.
  fold_unfold_tactic binary_tree_mirror.
Qed.

Lemma fold_unfold_binary_tree_mirror_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    binary_tree_mirror V (Node V t1 t2) =
    Node V (binary_tree_mirror V t2) (binary_tree_mirror V t1).
Proof.
  fold_unfold_tactic binary_tree_mirror.
Qed.

(* ***** *)

Definition test_binary_tree_flatten (candidate : forall V : Type, binary_tree V -> list V) : bool :=
  (eqb_list
     nat
     Nat.eqb
     (candidate
        nat
        (Node nat (Leaf nat 1) (Leaf nat 2)))
     (1 :: 2 :: nil))
  (* etc. *)
  .

Fixpoint binary_tree_flatten (V : Type) (t : binary_tree V) : list V :=
  match t with
    Leaf _ v =>
    v :: nil
  | Node _ t1 t2 =>
    list_append V (binary_tree_flatten V t1) (binary_tree_flatten V t2)
  end.

Compute (test_binary_tree_flatten binary_tree_flatten).

Lemma fold_unfold_binary_tree_flatten_Leaf :
  forall (V : Type)
         (v : V),
    binary_tree_flatten V (Leaf V v) =
    v :: nil.
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

Lemma fold_unfold_binary_tree_flatten_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V),
    binary_tree_flatten V (Node V t1 t2) =
    list_append V (binary_tree_flatten V t1) (binary_tree_flatten V t2).
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

(* ***** *)

Fixpoint binary_tree_flatten_acc (V : Type) (t : binary_tree V) (a : list V) : list V :=
  match t with
    Leaf _ v =>
    v :: a
  | Node _ t1 t2 =>
    binary_tree_flatten_acc V t1 (binary_tree_flatten_acc V t2 a)
  end.

Lemma fold_unfold_binary_tree_flatten_acc_Leaf :
  forall (V : Type)
         (v : V)
         (a : list V),
    binary_tree_flatten_acc V (Leaf V v) a =
    v :: a.
Proof.
  fold_unfold_tactic binary_tree_flatten_acc.
Qed.

Lemma fold_unfold_binary_tree_flatten_acc_Node :
  forall (V : Type)
         (t1 t2 : binary_tree V)
         (a : list V),
    binary_tree_flatten_acc V (Node V t1 t2) a =
    binary_tree_flatten_acc V t1 (binary_tree_flatten_acc V t2 a).
Proof.
  fold_unfold_tactic binary_tree_flatten.
Qed.

Definition binary_tree_flatten_alt (V : Type) (t : binary_tree V) : list V :=
  binary_tree_flatten_acc V t nil.

Compute (test_binary_tree_flatten binary_tree_flatten_alt).

Property about_binary_tree_flatten_acc :
  forall (V : Type)
         (t : binary_tree V)
         (a1 a2 : list V),
    binary_tree_flatten_acc V t (list_append V a1 a2) =
    list_append V (binary_tree_flatten_acc V t a1) a2.
Proof.
  Compute (let V := nat in
           let t := Node nat 
                         (Node nat (Leaf nat 1) (Leaf nat 2))
                         (Node nat (Leaf nat 3) (Leaf nat 4)) in
           let a1 := 10 :: 20 :: nil in
           let a2 := 30 :: 40 :: nil in
           binary_tree_flatten_acc V t (list_append V a1 a2) =
           list_append V (binary_tree_flatten_acc V t a1) a2).
Admitted. (* Time permitting, prove this helpful property. *)

(* ********** *)

(* 0. Concisely describe
      list_append, list_reverse, and list_reverse_alt
      and
      mirror, flatten, and flatten_alt
      as well as their associated properties. *)

(* ********** *)

(* 1.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v1 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse V (binary_tree_flatten V t).
Proof.
(*
   Compute (let V := nat in
            let t := ...put a telling tree here... in
            binary_tree_flatten V (binary_tree_mirror V t) =
            list_reverse V (binary_tree_flatten V t)).
*)
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 1.b Prove Theorem about_mirroring_and_flattening_v1. *)

Theorem about_mirroring_and_flattening_v1 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse V (binary_tree_flatten V t).
Proof.
Abort.

(* ********** *)

(* 2.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse_alt V (binary_tree_flatten V t).
Proof.
(*
   Compute (let V := nat in
            let t := ...put a telling tree here... in
            binary_tree_flatten V (binary_tree_mirror V t) =
            list_reverse_alt V (binary_tree_flatten V t)).
*)
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 2.b Prove Theorem about_mirroring_and_flattening_v2. *)

(*
Lemma about_mirroring_and_flattening_v2_aux :
  ...a suitable auxiliary lemma for about_mirroring_and_flattening_v2...
*)

Theorem about_mirroring_and_flattening_v2 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten V (binary_tree_mirror V t) =
    list_reverse_alt V (binary_tree_flatten V t).
Proof.
Abort.

(* Of course you can also prove about_mirroring_and_flattening_v2
   as a corollary of about_mirroring_and_flattening_v1
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* 3.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
    list_reverse_alt V (binary_tree_flatten_alt V t).
Proof.
(*
   Compute (let V := nat in
            let t := ...put a telling tree here... in
            binary_tree_flatten_alt V (binary_tree_mirror V t) =
            list_reverse_alt V (binary_tree_flatten_alt V t)).
*)
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 3.b Prove Theorem about_mirroring_and_flattening_v3. *)

(*
Lemma about_mirroring_and_flattening_v3_aux :
  ...a suitable auxiliary lemma for about_mirroring_and_flattening_v2...
*)

Theorem about_mirroring_and_flattening_v3 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
    list_reverse_alt V (binary_tree_flatten_alt V t).
Proof.
Abort.

(* Of course you can also prove about_mirroring_and_flattening_v3
   as a corollary of about_mirroring_and_flattening_v1 or of about_mirroring_and_flattening_v2
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* 4.a Explain the following theorem. *)

Theorem about_mirroring_and_flattening_v4 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
    list_reverse V (binary_tree_flatten_alt V t).
Proof.
(*
   Compute (let V := nat in
            let t := ...put a telling tree here... in
            binary_tree_flatten_alt V (binary_tree_mirror V t) =
            list_reverse V (binary_tree_flatten_alt V t)).
*)
Abort. (* Don't prove this theorem, you will do that just below. *)

(* ***** *)

(* 4.b Prove Theorem about_mirroring_and_flattening_v4. *)

(*
Lemma about_mirroring_and_flattening_v4_aux :
  ...a suitable auxiliary lemma for about_mirroring_and_flattening_v4...
*)

Theorem about_mirroring_and_flattening_v4 :
  forall (V : Type)
         (t : binary_tree V),
    binary_tree_flatten_alt V (binary_tree_mirror V t) =
    list_reverse V (binary_tree_flatten_alt V t).
Proof.
Abort.

(* Of course you can also prove about_mirroring_and_flattening_v4
   as a corollary of about_mirroring_and_flattening_v1 or of about_mirroring_and_flattening_v2 or of about_mirroring_and_flattening_v3
   but that is not the point: the point is to make you reason
   about functions that use an accumulator. *)

(* ********** *)

(* end of week-01_about-reversing-a-list-and-mirroring-a-tree.v *)
