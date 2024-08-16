(* term-project.v *)

(* MR 2024 - YSC 2024-2025, Sem1 *)
(* Continued from FPP 2023 - YSC 2023-2024, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 15 Aug 2024 *)

(* ********** *)

(* Three language processors for arithmetic expressions. *)

(* ********** *)

(* student name: Alan Matthew Anggara
   e-mail address: alan.matthew@u.yale-nus.edu.sg
   student ID number: A0207754B
 *)

(* student name: Kim Young Il
   e-mail address: youngil.kim@u.yale-nus.edu.sg
   student ID number: A0207809Y
 *)

(* student name: Vibilan Jayanth
   e-mail address: vibilan@u.yale-nus.edu.sg
   student ID number: A0242417L
 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Bool List String Ascii.

(* caution: only use natural numbers up to 5000 *)
Definition string_of_nat (q0 : nat) : string :=
  let s0 := String (ascii_of_nat (48 + (q0 mod 10))) EmptyString
  in if q0 <? 10
     then s0
     else let q1 := q0 / 10
          in let s1 := String (ascii_of_nat (48 + (q1 mod 10))) s0
             in if q1 <? 10
                then s1
                else let q2 := q1 / 10
                     in let s2 := String (ascii_of_nat (48 + (q2 mod 10))) s1
                        in if q2 <? 10
                           then s2
                           else let q3 := q2 / 10
                                in let s2 := String (ascii_of_nat (48 + (q3 mod 10))) s2
                        in if q3 <? 10
                           then s2
                           else "00000".

(* ********** *)

Lemma fold_unfold_list_append_nil :
  forall (V : Type)
         (v2s : list V),
    nil ++ v2s = v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

Lemma fold_unfold_list_append_cons :
  forall (V : Type)
         (v1 : V)
         (v1s' v2s : list V),
    (v1 :: v1s') ++ v2s = v1 :: v1s' ++ v2s.
Proof.
  fold_unfold_tactic List.app.
Qed.

(* ********** *)

(* Arithmetic expressions: *)

Inductive arithmetic_expression : Type :=
  Literal : nat -> arithmetic_expression
| Plus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Minus : arithmetic_expression -> arithmetic_expression -> arithmetic_expression
| Times : arithmetic_expression -> arithmetic_expression -> arithmetic_expression.

(* Source programs: *)

Inductive source_program : Type :=
  Source_program : arithmetic_expression -> source_program.

(* ********** *)

(* Semantics: *)

Inductive expressible_value : Type :=
  Expressible_nat : nat -> expressible_value
| Expressible_msg : string -> expressible_value.

(* ********** *)

Definition specification_of_evaluate (evaluate : arithmetic_expression -> expressible_value) :=
  (forall n : nat,
     evaluate (Literal n) = Expressible_nat n)
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Plus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Plus ae1 ae2) = Expressible_nat (n1 + n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Minus ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = true ->
       evaluate (Minus ae1 ae2) = Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1))))
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       n1 <? n2 = false ->
       evaluate (Minus ae1 ae2) = Expressible_nat (n1 - n2)))
  /\
  ((forall (ae1 ae2 : arithmetic_expression)
           (s1 : string),
       evaluate ae1 = Expressible_msg s1 ->
       evaluate (Times ae1 ae2) = Expressible_msg s1)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 : nat)
           (s2 : string),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_msg s2 ->
       evaluate (Times ae1 ae2) = Expressible_msg s2)
   /\
   (forall (ae1 ae2 : arithmetic_expression)
           (n1 n2 : nat),
       evaluate ae1 = Expressible_nat n1 ->
       evaluate ae2 = Expressible_nat n2 ->
       evaluate (Times ae1 ae2) = Expressible_nat (n1 * n2))).
    
Definition specification_of_interpret (interpret : source_program -> expressible_value) :=
  forall evaluate : arithmetic_expression -> expressible_value,
    specification_of_evaluate evaluate ->
    forall ae : arithmetic_expression,
      interpret (Source_program ae) = evaluate ae.

(* Task 1:
   a. time permitting, prove that each of the definitions above specifies at most one function;
   b. implement these two functions; and
   c. verify that each of your functions satisfies its specification.
 *)

(* Task 1a evaluate *)

Proposition there_is_at_most_one_evaluate_function :
  forall (evaluate1 evaluate2 : arithmetic_expression -> expressible_value),
    specification_of_evaluate evaluate1 ->
    specification_of_evaluate evaluate2 ->
    forall ae : arithmetic_expression,
      evaluate1 ae = evaluate2 ae.
Proof.
  intros evaluate1 evaluate2.
  intros S_evaluate1 S_evaluate2.
  intro ae.
  induction ae as [n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2].
    - destruct S_evaluate1 as [fold_unfold_evaluate1_Literal _].
      destruct S_evaluate2 as [fold_unfold_evaluate2_Literal _].
      rewrite -> (fold_unfold_evaluate2_Literal n).
      exact (fold_unfold_evaluate1_Literal n).
    - case (evaluate1 ae1) as [n11 | s11] eqn:E1_ae1;
        case (evaluate2 ae1) as [n21 | s21] eqn:E2_ae1;
        case (evaluate1 ae2) as [n12 | s12] eqn:E1_ae2;
        case (evaluate2 ae1) as [n22 | s22] eqn:E2_ae2.
      + destruct S_evaluate1 as [_ [[_ [_ fold_unfold_evaluate1_Plus]] _]].
        destruct S_evaluate2 as [_ [[_ [_ fold_unfold_evaluate2_Plus]] _]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 n21 n12 E1_ae1 E1_ae2).
        rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 n21 n12 E2_ae2 (eq_sym IHae2)).
        reflexivity.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [[_ [fold_unfold_evaluate1_Plus _]] _]].
        destruct S_evaluate2 as [_ [[_ [fold_unfold_evaluate2_Plus _]] _]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 n21 s12 E1_ae1 E1_ae2).
        rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 n21 s12 E2_ae2 (eq_sym IHae2)).
        reflexivity.
      + discriminate E2_ae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate E2_ae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [[fold_unfold_evaluate1_Plus [_ _]] _]].
        destruct S_evaluate2 as [_ [[fold_unfold_evaluate2_Plus [_ _]] _]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 s21 E1_ae1).
        rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 s21 E2_ae2).
        reflexivity.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [[fold_unfold_evaluate1_Plus [_ _]] _]].
        destruct S_evaluate2 as [_ [[fold_unfold_evaluate2_Plus [_ _]] _]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Plus ae1 ae2 s21 E1_ae1).
        rewrite -> (fold_unfold_evaluate2_Plus ae1 ae2 s21 E2_ae2).
        reflexivity.
    - case (evaluate1 ae1) as [n11 | s11] eqn:E1_ae1;
        case (evaluate2 ae1) as [n21 | s21] eqn:E2_ae1;
        case (evaluate1 ae2) as [n12 | s12] eqn:E1_ae2;
        case (evaluate2 ae1) as [n22 | s22] eqn:E2_ae2.
      + destruct S_evaluate1 as [_ [_ [[_ [_ [fold_unfold_evaluate1_Minus_lt fold_unfold_evaluate1_Minus_gte]]] _]]].
        destruct S_evaluate2 as [_ [_ [[_ [_ [fold_unfold_evaluate2_Minus_lt fold_unfold_evaluate2_Minus_gte]]] _]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        destruct (n21 <? n12) eqn:H_eq.
        * rewrite -> (fold_unfold_evaluate1_Minus_lt ae1 ae2 n21 n12 E1_ae1 E1_ae2 H_eq).
          rewrite -> (fold_unfold_evaluate2_Minus_lt ae1 ae2 n21 n12 E2_ae2 (eq_sym IHae2) H_eq).
          reflexivity.
        * rewrite -> (fold_unfold_evaluate1_Minus_gte ae1 ae2 n21 n12 E1_ae1 E1_ae2 H_eq).
          rewrite -> (fold_unfold_evaluate2_Minus_gte ae1 ae2 n21 n12 E2_ae2 (eq_sym IHae2) H_eq).
          reflexivity.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [_ [[_ [fold_unfold_evaluate1_Minus _]] _]]].
        destruct S_evaluate2 as [_ [_ [[_ [fold_unfold_evaluate2_Minus _]] _]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Minus ae1 ae2 n21 s12 E1_ae1 E1_ae2).
        rewrite -> (fold_unfold_evaluate2_Minus ae1 ae2 n21 s12 E2_ae2 (eq_sym IHae2)).
        reflexivity.
      + discriminate E2_ae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [_ [[fold_unfold_evaluate1_Minus _] _]]].
        destruct S_evaluate2 as [_ [_ [[fold_unfold_evaluate2_Minus _] _]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Minus ae1 ae2 s21 E1_ae1).
        rewrite -> (fold_unfold_evaluate2_Minus ae1 ae2 s21 E2_ae2).
        reflexivity.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [_ [[fold_unfold_evaluate1_Minus _] _]]].
        destruct S_evaluate2 as [_ [_ [[fold_unfold_evaluate2_Minus _] _]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Minus ae1 ae2 s21 E1_ae1).
        rewrite -> (fold_unfold_evaluate2_Minus ae1 ae2 s21 E2_ae2).
        reflexivity.
    - case (evaluate1 ae1) as [n11 | s11] eqn:E1_ae1;
        case (evaluate2 ae1) as [n21 | s21] eqn:E2_ae1;
        case (evaluate1 ae2) as [n12 | s12] eqn:E1_ae2;
        case (evaluate2 ae1) as [n22 | s22] eqn:E2_ae2.
      + destruct S_evaluate1 as [_ [_ [_ [_ [_ fold_unfold_evaluate1_Times]]]]].
        destruct S_evaluate2 as [_ [_ [_ [_ [_ fold_unfold_evaluate2_Times]]]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Times ae1 ae2 n21 n12 E1_ae1 E1_ae2).
        rewrite -> (fold_unfold_evaluate2_Times ae1 ae2 n21 n12 E2_ae2 (eq_sym IHae2)).
        reflexivity.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [_ [_ [_ [fold_unfold_evaluate1_Times _]]]]].
        destruct S_evaluate2 as [_ [_ [_ [_ [fold_unfold_evaluate2_Times _]]]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Times ae1 ae2 n21 s12 E1_ae1 E1_ae2).
        rewrite -> (fold_unfold_evaluate2_Times ae1 ae2 n21 s12 E2_ae2 (eq_sym IHae2)).
        reflexivity.
      + discriminate E2_ae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate E2_ae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate IHae1.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [_ [_ [fold_unfold_evaluate1_Times _]]]].
        destruct S_evaluate2 as [_ [_ [_ [fold_unfold_evaluate2_Times _]]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Times ae1 ae2 s21 E1_ae1).
        rewrite -> (fold_unfold_evaluate2_Times ae1 ae2 s21 E2_ae2).
        reflexivity.
      + discriminate E2_ae1.
      + destruct S_evaluate1 as [_ [_ [_ [fold_unfold_evaluate1_Times _]]]].
        destruct S_evaluate2 as [_ [_ [_ [fold_unfold_evaluate2_Times _]]]].
        rewrite -> IHae1 in E1_ae1.
        rewrite -> E2_ae1 in E2_ae2.
        rewrite -> (fold_unfold_evaluate1_Times ae1 ae2 s21 E1_ae1).
        rewrite -> (fold_unfold_evaluate2_Times ae1 ae2 s21 E2_ae2).
        reflexivity.
Qed.

(* Task 1a interpret *)

Proposition there_is_at_most_one_interpret_function :
  forall (interpret1 interpret2 : source_program -> expressible_value)
         (evaluate : arithmetic_expression -> expressible_value),
    specification_of_evaluate evaluate ->
    specification_of_interpret interpret1 ->
    specification_of_interpret interpret2 ->
    forall sp : source_program,
      interpret1 sp = interpret2 sp.
Proof.
  intros interpret1 interpret2 evaluate S_evaluate.
  unfold specification_of_interpret.
  intros S_interpret1 S_interpret2 [ae].
  rewrite -> (S_interpret1 evaluate S_evaluate ae).
  rewrite -> (S_interpret2 evaluate S_evaluate ae).
  reflexivity.
Qed.

(* Task 1b evaluate *)

Definition expressible_value_eqb (ev1 ev2 : expressible_value) : bool :=
  match ev1 with
  | Expressible_nat n1 =>
      match ev2 with
      | Expressible_nat n2 =>
          Nat.eqb n1 n2
      | Expressible_msg s2 =>
          false
      end
  | Expressible_msg s1 =>
      match ev2 with
      | Expressible_nat n2 =>
          false
      | Expressible_msg s2 =>
          String.eqb s1 s2
      end
  end.

Definition test_evaluate (candidate : arithmetic_expression -> expressible_value) : bool :=
  (expressible_value_eqb (candidate (Minus (Minus (Literal 1) (Literal 5)) (Minus (Literal 1) (Literal 4)))) (Expressible_msg "numerical underflow: -4"))
  && (expressible_value_eqb (candidate (Literal 5)) (Expressible_nat 5))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Literal 5))) (Expressible_nat 10))
  && (expressible_value_eqb (candidate (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))) (Expressible_nat 6))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 5))) (Expressible_nat 0))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 4))) (Expressible_nat 1))
  && (expressible_value_eqb (candidate (Minus (Literal 4) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1")).

Definition test_evaluate_rtl (candidate : arithmetic_expression -> expressible_value) : bool :=
  (expressible_value_eqb (candidate (Minus (Minus (Literal 1) (Literal 5)) (Minus (Literal 1) (Literal 4)))) (Expressible_msg "numerical underflow: -3"))
  && (expressible_value_eqb (candidate (Literal 5)) (Expressible_nat 5))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Literal 5))) (Expressible_nat 10))
  && (expressible_value_eqb (candidate (Plus (Plus (Literal 1) (Literal 2)) (Literal 3))) (Expressible_nat 6))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 5))) (Expressible_nat 0))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Literal 4))) (Expressible_nat 1))
  && (expressible_value_eqb (candidate (Minus (Literal 4) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Minus (Literal 4) (Literal 5)) (Literal 5))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Minus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Plus (Literal 5) (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1")).

Fixpoint evaluate (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      end
  | Minus ae1 ae2 =>
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          end
      end
  end.

Fixpoint evaluate_rtl (ae : arithmetic_expression) : expressible_value :=
  match ae with
  | Literal n =>
      Expressible_nat n
  | Plus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_msg s2 =>
          Expressible_msg s2
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_msg s1 =>
              Expressible_msg s1
          | Expressible_nat n1 =>
              Expressible_nat (n1 + n2)
          end
      end
  | Minus ae1 ae2 =>
      match evaluate_rtl ae2 with
      | Expressible_msg s2 =>
          Expressible_msg s2
      | Expressible_nat n2 =>
          match evaluate_rtl ae1 with
          | Expressible_msg s1 =>
              Expressible_msg s1
          | Expressible_nat n1 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          end
      end
  end.

Compute (test_evaluate evaluate = true).

Compute (test_evaluate evaluate_rtl = false).

Compute (test_evaluate_rtl evaluate = false).

Compute (test_evaluate_rtl evaluate_rtl = true).

Lemma fold_unfold_evaluate_Literal :
  forall (n : nat),
    evaluate (Literal n) =
      Expressible_nat n.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Plus ae1 ae2) =
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              Expressible_nat (n1 + n2)
          end
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

Lemma fold_unfold_evaluate_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    evaluate (Minus ae1 ae2) =
      match evaluate ae1 with
      | Expressible_msg s1 =>
          Expressible_msg s1
      | Expressible_nat n1 =>
          match evaluate ae2 with
          | Expressible_msg s2 =>
              Expressible_msg s2
          | Expressible_nat n2 =>
              if n1 <? n2
              then Expressible_msg (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              else Expressible_nat (n1 - n2)
          end
      end.
Proof.
  fold_unfold_tactic evaluate.
Qed.

(* Task 1b interpret *)

Definition test_interpret_alt (candidate : source_program -> expressible_value) : bool:=
  test_evaluate (fun ae => candidate (Source_program(ae))).

Definition test_interpret (candidate : source_program -> expressible_value) : bool :=
  (expressible_value_eqb (candidate (Source_program (Literal 5))) (Expressible_nat 5))
  && (expressible_value_eqb (candidate (Source_program (Plus (Literal 5) (Literal 5)))) (Expressible_nat 10))
  && (expressible_value_eqb (candidate (Source_program (Plus (Plus (Literal 1) (Literal 2)) (Literal 3)))) (Expressible_nat 6))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 5) (Literal 5)))) (Expressible_nat 0))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 5) (Literal 4)))) (Expressible_nat 1))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 4) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Minus (Minus (Literal 4) (Literal 5)) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Plus (Minus (Literal 4) (Literal 5)) (Literal 5)))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Minus (Literal 5) (Minus (Literal 4)(Literal 5))))) (Expressible_msg "numerical underflow: -1"))
  && (expressible_value_eqb (candidate (Source_program (Plus (Literal 5) (Minus (Literal 4) (Literal 5))))) (Expressible_msg "numerical underflow: -1")).

Definition interpret (sp : source_program) : expressible_value :=
  match sp with
  | Source_program ae => evaluate ae
  end.

Compute (test_interpret interpret = true).
Compute (test_interpret_alt interpret = true).

(* Task 1c evaluate *)

Theorem evaluate_satisfies_the_specification_of_evaluate :
  specification_of_evaluate evaluate.
Proof.
  unfold specification_of_evaluate.
  split.
  - intro n.
    rewrite -> fold_unfold_evaluate_Literal.
    reflexivity.
  - split.
    + split.
      { 
        intros ae1 ae2 s1 H_ae1.
        rewrite -> fold_unfold_evaluate_Plus.
        rewrite -> H_ae1.
        reflexivity.
       }

      split;
        intros ae1 ae2 e1 e2 H_ae1 H_ae2;
        rewrite -> fold_unfold_evaluate_Plus, H_ae1, H_ae2;
        reflexivity.

    + split.
      { 
        intros ae1 ae2 s1 H_ae1.
        rewrite -> fold_unfold_evaluate_Minus.
        rewrite -> H_ae1.
        reflexivity.
       }

      split.
      { 
        intros ae1 ae2 n1 s2 H_ae1 H_ae2.
        rewrite -> fold_unfold_evaluate_Minus, H_ae1, H_ae2.
        reflexivity.
       }

      split;
        intros ae1 ae2 n1 n2 H_ae1 H_ae2 H_n1_n2;
        rewrite -> fold_unfold_evaluate_Minus, H_ae1, H_ae2, H_n1_n2;
        reflexivity.
Qed.

(* Task 1c interpret *)

Theorem interpret_satisfies_the_specification_of_interpret :
  specification_of_interpret interpret.
Proof.
  - unfold specification_of_interpret, interpret.
    intros evaluate' S_evaluate ae.
    rewrite -> (there_is_at_most_one_evaluate_function
                  evaluate evaluate'
                  evaluate_satisfies_the_specification_of_evaluate
                  S_evaluate
      ).
    reflexivity.
Qed.

(* ********** *)

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  PUSH : nat -> byte_code_instruction
| ADD : byte_code_instruction
| SUB : byte_code_instruction.

(* Target_Program programs: *)

Inductive target_program : Type :=
  Target_program : list byte_code_instruction -> target_program.

(* Data stack: *)

Definition data_stack := list nat.

(* ********** *)

Inductive result_of_decoding_and_execution : Type :=
  OK : data_stack -> result_of_decoding_and_execution
| KO : string -> result_of_decoding_and_execution.

(* Informal specification of decode_execute : byte_code_instruction -> data_stack -> result_of_decoding_and_execution

 * given a nat n and a data_stack ds,
   evaluating
     decode_execute (PUSH n) ds
   should successfully return a stack where n is pushed on ds

 * given a data stack ds that contains at least 2 nats,
   evaluating
     decode_execute ADD ds
   should
   - pop these 2 nats off the data stack,
   - add them,
   - push the result of the addition on the data stack, and
   - successfully return the resulting data stack

   if the data stack does not contain at least 2 nats,
   evaluating
     decode_execute ADD ds
   should return the error message "ADD: stack underflow"

 * given a data stack ds that contains at least 2 nats,
   evaluating
     decode_execute SUB ds
   should
   - pop these 2 nats off the data stack,
   - subtract one from the other if the result is non-negative,
   - push the result of the subtraction on the data stack, and
   - successfully return the resulting data stack

   if the data stack does not contain at least 2 nats
   evaluating
     decode_execute SUB ds
   should return the error message "SUB: stack underflow"

   if the data stack contain at least 2 nats
   and
   if subtracting one nat from the other gives a negative result,
   evaluating
     decode_execute SUB ds
   should return the same error message as the evaluator
*)

(* Task 2:
   implement decode_execute
*)

Definition test_eqb_list_nat (candidate : list nat -> list nat -> bool) : bool :=
  (Bool.eqb (candidate nil nil) true)
  && (Bool.eqb (candidate (1 :: nil) (1 :: nil)) true)
  && (Bool.eqb (candidate (2 :: 1 :: nil) (2 :: 1 :: nil)) true)
  && (Bool.eqb (candidate (2 :: 1 :: nil) (1 :: 1 :: nil)) false).

Fixpoint eqb_list (V : Type) (eqb_V : V -> V -> bool) (v1s v2s : list V) : bool :=
  match v1s with
  | nil =>
      match v2s with
      | nil =>
          true
      | v2 :: v2s' =>
          false
      end
  | v1 :: v1s' =>
      match v2s with
      | nil =>
          false
      | v2 :: v2s' =>
          eqb_V v1 v2 && eqb_list V eqb_V v1s' v2s'
      end
  end.

Definition eqb_list_nat (v1s v2s : list nat) : bool :=
  eqb_list nat Nat.eqb v1s v2s.

Compute (test_eqb_list_nat eqb_list_nat = true).

Definition eqb_result_of_decoding_and_execution (rde1 rde2 : result_of_decoding_and_execution) : bool :=
  match rde1 with
  | OK vs1 =>
      match rde2 with
      | OK vs2 =>
          eqb_list_nat vs1 vs2
      | KO s2 =>
          false
      end
  | KO s1 =>
      match rde2 with
      | OK vs2 =>
          false
      | KO s2 =>
          String.eqb s1 s2
      end
  end.

Definition test_decode_execute (candidate : byte_code_instruction -> data_stack -> result_of_decoding_and_execution) : bool :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 42) (1 :: 2 :: 3 :: nil)) (OK (42 :: 1 :: 2 :: 3 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (1 :: 5 :: nil)) (OK (4 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (5 :: 1 :: nil)) (KO "numerical underflow: -4"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (1 :: nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (nil)) (KO "SUB: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (ADD) (4 :: 3 :: 2 :: 1 :: nil)) (OK (7 :: 2 :: 1 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (SUB) (3 :: 4 :: 2 :: 5 :: nil)) (OK (1 :: 2 :: 5 :: nil))).

Definition decode_execute (bci : byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bci with
  | PUSH n => OK (n :: ds)
  | ADD =>
      match ds with
      | nil => KO "ADD: stack underflow"
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' => OK ((n1 + n2) :: ds'')
          | nil => KO "ADD: stack underflow"
          end
      end
  | SUB =>
      match ds with
      | nil => KO "SUB: stack underflow"
      | n2 :: ds' =>
          match ds' with
          | n1 :: ds'' =>
              match n1 <? n2 with
              | true =>
                  KO (String.append "numerical underflow: -" (string_of_nat (n2 - n1)))
              | false =>
                  OK ((n1 - n2) :: ds'')
              end
          | nil => KO "SUB: stack underflow"
          end
      end
  end.

Compute (test_decode_execute decode_execute = true).

(* ********** *)

(* Specification of the virtual machine: *)

Definition specification_of_fetch_decode_execute_loop (fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution) :=
  (forall ds : data_stack,
      fetch_decode_execute_loop nil ds = OK ds)
  /\
  (forall (bci : byte_code_instruction)
          (bcis' : list byte_code_instruction)
          (ds ds' : data_stack),
      decode_execute bci ds = OK ds' ->
      fetch_decode_execute_loop (bci :: bcis') ds =
      fetch_decode_execute_loop bcis' ds')
  /\
  (forall (bci : byte_code_instruction)
          (bcis' : list byte_code_instruction)
          (ds : data_stack)
          (s : string),
      decode_execute bci ds = KO s ->
      fetch_decode_execute_loop (bci :: bcis') ds =
      KO s).

(* Task 3:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

(* Task 3a *)

Proposition there_is_at_most_one_fetch_decode_execute_loop_function :
  forall (fetch_decode_execute_loop_1 fetch_decode_execute_loop_2 : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution),
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_1 ->
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop_2 ->
    forall (bcis : list byte_code_instruction) (ds : data_stack),
      fetch_decode_execute_loop_1 bcis ds = fetch_decode_execute_loop_2 bcis ds.
Proof.
  intros fetch_decode_execute_loop_1 fetch_decode_execute_loop_2.
  intros S_1 S_2.
  induction bcis as [ | bci bcis' IHbcis'];
    unfold specification_of_fetch_decode_execute_loop in S_1, S_2;
    destruct S_1 as [S_nil1 [S_OK1 S_KO1]];
    destruct S_2 as [S_nil2 [S_OK2 S_KO2]].
  - intros ds.
    rewrite -> (S_nil1 ds).
    rewrite -> (S_nil2 ds).
    reflexivity.
  - intros [ | d ds'].
    + Check (S_OK1 bci bcis' nil nil).
      destruct (decode_execute bci nil) as [ds | s] eqn:H_decode.
      * Check (S_OK1 bci bcis' nil ds H_decode).
        rewrite -> (S_OK1 bci bcis' nil ds H_decode).
        rewrite -> (S_OK2 bci bcis' nil ds H_decode).
        exact (IHbcis' ds).
      * Check (S_KO1 bci bcis' nil s H_decode).
        rewrite -> (S_KO1 bci bcis' nil s H_decode).
        rewrite -> (S_KO2 bci bcis' nil s H_decode).
        reflexivity.
    + Check (S_OK1 bci bcis' nil nil).
      destruct (decode_execute bci (d :: ds')) as [ds | s] eqn:H_decode.
      * Check (S_OK1 bci bcis' (d :: ds') ds H_decode).
        rewrite -> (S_OK1 bci bcis' (d :: ds') ds H_decode).
        rewrite -> (S_OK2 bci bcis' (d :: ds') ds H_decode).
        exact (IHbcis' ds).
      * Check (S_KO1 bci bcis' (d :: ds') s).
        Check(S_KO1 bci bcis' (d :: ds') s).
        rewrite -> (S_KO1 bci bcis' (d :: ds') s H_decode).
        rewrite -> (S_KO2 bci bcis' (d :: ds') s H_decode).
        reflexivity.
Qed.

(* Task 3b. Implement the function *)

Definition test_fetch_decode_execute_loop (candidate : (list byte_code_instruction) -> data_stack -> result_of_decoding_and_execution) :=
  (eqb_result_of_decoding_and_execution (candidate (PUSH 42 :: PUSH 21 :: nil) (2 :: 4 :: nil)) (OK (21 :: 42 :: 2 :: 4 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (PUSH 42 :: PUSH 21 :: nil) (nil)) (OK (21 :: 42 :: nil)))
  && (eqb_result_of_decoding_and_execution (candidate (ADD :: SUB :: nil) (nil)) (KO "ADD: stack underflow"))
  && (eqb_result_of_decoding_and_execution (candidate (PUSH 3 :: PUSH 10 :: SUB :: nil) nil) (KO "numerical underflow: -7"))
  && (eqb_result_of_decoding_and_execution (candidate (PUSH 3 :: PUSH 1 :: SUB :: PUSH 3 :: PUSH 2 :: ADD :: SUB :: nil) nil) (KO "numerical underflow: -3")).

Fixpoint fetch_decode_execute_loop (bcis : list byte_code_instruction) (ds : data_stack) : result_of_decoding_and_execution :=
  match bcis with
  | nil => OK ds
  | bci :: bcis' =>
    match decode_execute bci ds with
    | OK ds' => fetch_decode_execute_loop bcis' ds'
    | KO s => KO s
    end
  end.

Compute (test_fetch_decode_execute_loop fetch_decode_execute_loop).

Lemma fold_unfold_fetch_decode_execute_loop_nil :
  forall (ds: data_stack),
    fetch_decode_execute_loop nil ds =
      OK ds.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

Lemma fold_unfold_fetch_decode_execute_loop_cons :
  forall (bci : byte_code_instruction) (bcis' : list byte_code_instruction) (ds : data_stack),
    fetch_decode_execute_loop (bci :: bcis') ds =
      match decode_execute bci ds with
      | OK ds' => fetch_decode_execute_loop bcis' ds'
      | KO s => KO s
      end.
Proof.
  fold_unfold_tactic fetch_decode_execute_loop.
Qed.

(* Task 3c. Verify that your function satisfies the specification *)

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  split.
  - intro ds.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - split.
    + intros bci bcis' ds ds'.
      intro H_fde_OK.
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      rewrite -> H_fde_OK.
      reflexivity.
    + intros bci bcis' ds s.
      intro H_fde_KO.
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      rewrite -> H_fde_KO.
      reflexivity.
Qed.

Theorem fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop_v2 :
  specification_of_fetch_decode_execute_loop fetch_decode_execute_loop.
Proof.
  unfold specification_of_fetch_decode_execute_loop.
  split.
  - intro ds.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - split;
      intros bci bcis' ds res_exec H_fde;
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons;
      rewrite -> H_fde;
      reflexivity.
Qed.

(* ********** *)

(* Task 4:
   Prove that for any lists of byte-code instructions bci1s and bci2s,
   and for any data stack ds,
   executing the concatenation of bci1s and bci2s (i.e., bci1s ++ bci2s) with ds
   gives the same result as
   (1) executing bci1s with ds, and then
   (2) executing bci2s with the resulting data stack, if there exists one.
 *)

(* This is more operational (v1), but it's better to write something more logical (v2) *)

Theorem fetch_decode_execute_loop_concatenation_v1 :
  forall (bci1s bci2s : list byte_code_instruction) (ds : data_stack),
    fetch_decode_execute_loop (bci1s ++ bci2s) ds =
    match fetch_decode_execute_loop bci1s ds with
    | OK ds' => fetch_decode_execute_loop bci2s ds'
    | KO s => KO s
    end.
Proof.
  (* Let's test first *)
  Compute (let bci1s := (PUSH 42 :: PUSH 23 :: nil) in
           let bci2s :=  (ADD :: SUB :: nil) in
           let ds := (2 :: 1 :: nil) in
           fetch_decode_execute_loop (bci1s ++ bci2s) ds =
             match fetch_decode_execute_loop bci1s ds with
             | OK ds' => fetch_decode_execute_loop bci2s ds'
             | KO s => KO s
             end).
  Compute (let bci1s := (ADD :: SUB :: nil)  in
           let bci2s := (PUSH 42 :: PUSH 23 :: nil)  in
           let ds := (nil) in
           fetch_decode_execute_loop (bci1s ++ bci2s) ds =
             match fetch_decode_execute_loop bci1s ds with
             | OK ds' => fetch_decode_execute_loop bci2s ds'
             | KO s => KO s
             end).
  intros bci1s.
  induction bci1s as [ | bci1 bci1s' IHbci1s'].
  - intros bci2s ds.
    rewrite -> fold_unfold_list_append_nil.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    reflexivity.
  - intros [ | bci2 bci2s'].
    + intro ds.
      Search (_ ++ nil = _).
      Check (app_nil_r).
      rewrite -> (app_nil_r).
      Check (fold_unfold_fetch_decode_execute_loop_cons).
      rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
      destruct (decode_execute bci1 ds) as [ds1' | s1].
      * Check (IHbci1s' nil ds1').
        rewrite <- (app_nil_r bci1s') at 1.
        Check (IHbci1s' nil ds1').
        exact (IHbci1s' nil ds1').
      * reflexivity.
    + intro ds.
      Check (fold_unfold_fetch_decode_execute_loop_cons).
      rewrite -> fold_unfold_list_append_cons.
      rewrite -> 2 fold_unfold_fetch_decode_execute_loop_cons.
      destruct (decode_execute bci1 ds) as [ds1' | s1].
      * Check (IHbci1s').
        Check (IHbci1s' (bci2 :: bci2s')).
        exact (IHbci1s' (bci2 :: bci2s') ds1').
      * reflexivity.
Qed.

(* This is more logical *)

Theorem fetch_decode_execute_loop_concatenation_v2 :
  forall (bci1s bci2s : list byte_code_instruction) (ds : data_stack),
    (forall ds1 : data_stack,
       fetch_decode_execute_loop bci1s ds = OK ds1 ->
       fetch_decode_execute_loop (bci1s ++ bci2s) ds =
       fetch_decode_execute_loop bci2s ds1)
    /\
    (forall s1 : string,
       fetch_decode_execute_loop bci1s ds = KO s1 ->
       fetch_decode_execute_loop (bci1s ++ bci2s) ds =
       KO s1).
Proof.
  intros bci1s.
  induction bci1s as [ | bci bci1s' IHbci1s'].
  - intros [ | bci2 bci2s'].
    + intro ds.
      split.
      * intro ds1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        rewrite -> S_fde_nil.
        rewrite <- fold_unfold_fetch_decode_execute_loop_nil.
        reflexivity.
      * intro s1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        exact S_fde_nil.
    + intro ds.
      split.
      * intro ds1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        rewrite -> (fold_unfold_fetch_decode_execute_loop_nil) in S_fde_nil.
        injection S_fde_nil as S_fde_nil.
        rewrite -> S_fde_nil.
        reflexivity.
      * intro s1.
        intro S_fde_nil.
        rewrite -> fold_unfold_list_append_nil.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil in S_fde_nil.
        discriminate S_fde_nil.
  - intros [ | bci2 bci2s'].
    + intro ds.
      split.
      * intro ds1.
        intro S_nil.
        Search (_ ++ nil).
        rewrite -> app_nil_r.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        exact S_nil.
      * intro s1.
        intro S_KO.
        rewrite -> app_nil_r.
        exact S_KO.
    + intro ds.
      split.
      * intro ds1.
        intro S_OK.
        rewrite -> fold_unfold_list_append_cons.
        destruct (decode_execute bci ds) as [ds' | s'] eqn:H_decode.
        -- destruct (IHbci1s' (bci2 :: bci2s') ds') as [S_ds _].
           Check (fold_unfold_fetch_decode_execute_loop_cons).
           Check (fold_unfold_fetch_decode_execute_loop_cons bci (bci1s' ++ bci2 :: bci2s')).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_OK.
           rewrite -> H_decode in S_OK.
           Check (S_ds ds1).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           Check (S_ds ds1 S_OK).
           exact (S_ds ds1 S_OK).
        -- destruct (IHbci1s' (bci2 :: bci2s') ds) as [S_ds _].
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_OK.
           rewrite -> H_decode in S_OK.
           discriminate S_OK.
      * intro s1.
        intro S_KO.
        rewrite -> fold_unfold_list_append_cons.
        destruct (decode_execute bci ds) as [ds' | s'] eqn:H_decode.
        -- destruct (IHbci1s' (bci2 :: bci2s') ds') as [_ S_s].
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_KO.
           rewrite -> H_decode in S_KO.
           Check (S_s s1 S_KO).
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           exact (S_s s1 S_KO).
        -- destruct (IHbci1s' (bci2 :: bci2s') ds) as [_ S_s].
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
           rewrite -> H_decode.
           rewrite -> fold_unfold_fetch_decode_execute_loop_cons in S_KO.
           rewrite -> H_decode in S_KO.
           exact S_KO.
Qed.

(* ********** *)

Definition specification_of_run (run : target_program -> expressible_value) :=
  forall fetch_decode_execute_loop : list byte_code_instruction -> data_stack -> result_of_decoding_and_execution,
    specification_of_fetch_decode_execute_loop fetch_decode_execute_loop ->
    (forall (bcis : list byte_code_instruction),
       fetch_decode_execute_loop bcis nil = OK nil ->
       run (Target_program bcis) = Expressible_msg "no result on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (n : nat),
       fetch_decode_execute_loop bcis nil = OK (n :: nil) ->
       run (Target_program bcis) = Expressible_nat n)
    /\
    (forall (bcis : list byte_code_instruction)
            (n n' : nat)
            (ds'' : data_stack),
       fetch_decode_execute_loop bcis nil = OK (n :: n' :: ds'') ->
       run (Target_program bcis) = Expressible_msg "too many results on the data stack")
    /\
    (forall (bcis : list byte_code_instruction)
            (s : string),
       fetch_decode_execute_loop bcis nil = KO s ->
       run (Target_program bcis) = Expressible_msg s).

(* Task 5:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
*)

(* Task 5a *)

(* Task 5b. Implement this function *)

Definition test_run (candidate : target_program -> expressible_value) : bool :=
  (expressible_value_eqb
     (candidate (Target_program (PUSH 42 :: nil)))
     (Expressible_nat 42))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 42 :: ADD :: SUB :: nil)))
        (Expressible_msg "ADD: stack underflow"))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 42 :: ADD :: SUB :: PUSH 20 :: PUSH 10 :: PUSH 5 :: nil)))
        (Expressible_msg "ADD: stack underflow"))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 20 :: PUSH 42 :: ADD :: PUSH 20 :: PUSH 30 :: PUSH 40 :: nil)))
        (Expressible_msg "too many results on the data stack"))
  && (expressible_value_eqb
        (candidate (Target_program (PUSH 42 :: PUSH 1 :: ADD :: PUSH 100 :: ADD :: nil)))
        (Expressible_nat 143)).

Definition run (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | OK nil => Expressible_msg "no result on the data stack"
    | OK (n :: nil) => Expressible_nat n
    | OK (n :: _ :: _) => Expressible_msg "too many results on the data stack"
    | KO s => Expressible_msg s
    end
  end.

Compute (test_run run = true).

(* A more verbose version,
reflects the structure of the there is at most one run function proof *)
Definition run_v2 (tp : target_program) : expressible_value :=
  match tp with
  | Target_program bcis =>
    match fetch_decode_execute_loop bcis nil with
    | OK ds =>
        match ds with
        | nil => Expressible_msg "no result on the data stack"
        | (n :: ds') =>
            match ds' with
            | nil =>  Expressible_nat n
            | (n' :: ds'') => Expressible_msg "too many results on the data stack"
            end
        end
    | KO s => Expressible_msg s
    end
  end.

Compute (test_run run_v2 = true).

(* Task 5c. verify that your function satisfies the specification. *)

Theorem run_satisfies_the_specification_of_run :
  specification_of_run run.
Proof.
  unfold specification_of_run.
  intro fetch_decode_execute_loop0.
  intro S_fetch_decode_execute_loop0.
  assert (loop_equality :=
            there_is_at_most_one_fetch_decode_execute_loop_function
              fetch_decode_execute_loop fetch_decode_execute_loop0
              fetch_decode_execute_loop_satisfies_the_specification_of_fetch_decode_execute_loop
              S_fetch_decode_execute_loop0).
  split.
  - case bcis as [ | bci bcis']; intro H_decode.
    + unfold run.
      rewrite -> loop_equality.
      rewrite -> H_decode.
      reflexivity.
    + unfold run.
      rewrite -> loop_equality.
      rewrite -> H_decode.
      reflexivity.
  - split.
    + intros bcis n.
      intro H_decode.
      unfold run.
      rewrite -> loop_equality.
      rewrite -> H_decode.
      reflexivity.
    + split.
      * intros bcis n n' ds'' H_decode.
        unfold run.
        rewrite -> loop_equality.
        rewrite -> H_decode.
        reflexivity.
      * intros bcis s H_decode.
        unfold run.
        rewrite -> loop_equality.
        rewrite -> H_decode.
        reflexivity.
Qed.

(* ********** *)

Definition specification_of_compile_aux (compile_aux : arithmetic_expression -> list byte_code_instruction) :=
  (forall n : nat,
     compile_aux (Literal n) = PUSH n :: nil)
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Plus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (ADD :: nil))
  /\
  (forall ae1 ae2 : arithmetic_expression,
     compile_aux (Minus ae1 ae2) = (compile_aux ae1) ++ (compile_aux ae2) ++ (SUB :: nil)).

(* Task 6:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function using list concatenation, i.e., ++; and
   c. verify that your function satisfies the specification.
*)

(* Task 6a *)

Proposition there_is_at_most_one_compile_aux_function :
  forall (compile_aux_1 compile_aux_2 : arithmetic_expression -> list byte_code_instruction),
    specification_of_compile_aux compile_aux_1 ->
    specification_of_compile_aux compile_aux_2 ->
    forall ae : arithmetic_expression,
      compile_aux_1 ae = compile_aux_2 ae.
Proof.
  intros compile_aux_1 compile_aux_2 H_compile_aux_1 H_compile_aux_2.
  unfold specification_of_compile_aux in H_compile_aux_1, H_compile_aux_2.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ].

  (* Case 1: Literal*)
  - destruct H_compile_aux_1 as [H_compile_aux_1_Literal_nil [_ _]].
    destruct H_compile_aux_2 as [H_compile_aux_2_Literal_nil [_ _]].
    rewrite -> H_compile_aux_2_Literal_nil.
    exact (H_compile_aux_1_Literal_nil n).

  (* Case 2: Plus *)
  - destruct H_compile_aux_1 as [_ [H_compile_aux_1_Plus _]].
    destruct H_compile_aux_2 as [_ [H_compile_aux_2_Plus _]].
    rewrite -> H_compile_aux_1_Plus.
    rewrite -> H_compile_aux_2_Plus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.

    (* Case 3: Minus *)
  - destruct H_compile_aux_1 as [_ [_ H_compile_aux_1_Minus]].
    destruct H_compile_aux_2 as [_ [_ H_compile_aux_2_Minus]].
    rewrite -> H_compile_aux_1_Minus.
    rewrite -> H_compile_aux_2_Minus.
    rewrite -> IHae1.
    rewrite -> IHae2.
    reflexivity.
Qed.

(* Task 6b *)

Fixpoint compile_aux (ae : arithmetic_expression) : list byte_code_instruction :=
    match ae with
    | Literal n => PUSH n :: nil
    | Plus ae1 ae2 => compile_aux ae1 ++ compile_aux ae2 ++ (ADD :: nil)
    | Minus ae1 ae2 => compile_aux ae1 ++ compile_aux ae2 ++ (SUB :: nil)
    end.

Definition test_eqb_byte_code_instruction (candidate : byte_code_instruction -> byte_code_instruction -> bool) :=
  (Bool.eqb (candidate ADD ADD) true)
  && (Bool.eqb (candidate ADD SUB) false)
  && (Bool.eqb (candidate ADD (PUSH 1)) false)
  && (Bool.eqb (candidate SUB ADD) false)
  && (Bool.eqb (candidate SUB SUB) true)
  && (Bool.eqb (candidate SUB (PUSH 1)) false)
  && (Bool.eqb (candidate (PUSH 1) (PUSH 1)) true)
  && (Bool.eqb (candidate (PUSH 2) (PUSH 1)) false).

Definition eqb_byte_code_instruction (bci1 bci2 : byte_code_instruction) :=
  match bci1 with
  | PUSH n1 =>
      match bci2 with
      | PUSH n2 =>
          Nat.eqb n1 n2
      | _ =>
          false
      end
  | ADD =>
      match bci2 with
      | ADD =>
          true
      | _ =>
          false
      end
  | SUB =>
      match bci2 with
      | SUB =>
          true
      | _ =>
          false
      end
  end.

Compute (test_eqb_byte_code_instruction eqb_byte_code_instruction).

Definition eqb_list_byte_code_instruction (bcis1 bcis2 : list byte_code_instruction) : bool :=
  eqb_list byte_code_instruction eqb_byte_code_instruction bcis1 bcis2.

Definition test_compile_aux (candidate : arithmetic_expression -> (list byte_code_instruction)) :=
  (eqb_list_byte_code_instruction (candidate (Literal 2))
     (PUSH 2 :: nil))
  && (eqb_list_byte_code_instruction (candidate (Plus (Literal 5) (Literal 2)))
        (PUSH 5 :: PUSH 2 :: ADD :: nil))
  && (eqb_list_byte_code_instruction (candidate (Minus (Literal 5) (Literal 2)))
        (PUSH 5 :: PUSH 2 :: SUB :: nil)).

Compute (test_compile_aux compile_aux = true).

(* Task 6c *)

Lemma fold_unfold_compile_aux_Literal :
  forall (n : nat),
    compile_aux (Literal n) =
      PUSH n :: nil.
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Plus ae1 ae2) =
       compile_aux ae1 ++ compile_aux ae2 ++ (ADD :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Lemma fold_unfold_compile_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression),
    compile_aux (Minus ae1 ae2) =
       compile_aux ae1 ++ compile_aux ae2 ++ (SUB :: nil).
Proof.
  fold_unfold_tactic compile_aux.
Qed.

Theorem compile_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  - intro n.
    exact (fold_unfold_compile_aux_Literal n).
  - split.
    + intros ae1 ae2.
      exact (fold_unfold_compile_aux_Plus ae1 ae2).
    + intros ae1 ae2.
      exact (fold_unfold_compile_aux_Minus ae1 ae2).
Qed.

(*********)

Definition specification_of_compile (compile : source_program -> target_program) :=
  forall compile_aux : arithmetic_expression -> list byte_code_instruction,
    specification_of_compile_aux compile_aux ->
    forall ae : arithmetic_expression,
      compile (Source_program ae) = Target_program (compile_aux ae).

(* Task 7:
   a. time permitting, prove that the definition above specifies at most one function;
   b. implement this function; and
   c. verify that your function satisfies the specification.
 *)

(* Task 7a *)

Proposition there_is_at_most_one_compile_function :
  forall (compile1 compile2 : source_program -> target_program),
    specification_of_compile compile1 ->
    specification_of_compile compile2 ->
    forall ae : arithmetic_expression,
      compile1 (Source_program ae) = compile2 (Source_program ae).
Proof.
  intros compile1 compile2 H_compile1 H_compile2.
  unfold specification_of_compile in H_compile1, H_compile2.
  case ae as [ n | ae1 ae2 | ae1 ae2 ].

  (* Case 1: Literal *)
  - Check (H_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Literal n)).
    rewrite -> (H_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Literal n)).
    Check (H_compile2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Literal n)).
    rewrite -> (H_compile2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Literal n)).
    reflexivity.

  (* Case 2: Plus *)
  - Check (H_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Plus ae1 ae2)).
    rewrite -> (H_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Plus ae1 ae2)).
    rewrite -> (H_compile2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Plus ae1 ae2)).
    reflexivity.

  (* Case 3: Minus *)
  - Check (H_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Minus ae1 ae2)).
    rewrite -> (H_compile1 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Minus ae1 ae2)).
    rewrite -> (H_compile2 compile_aux compile_aux_satisfies_the_specification_of_compile_aux (Minus ae1 ae2)).
    reflexivity.
Qed.

(* Task 7b. Implement this function *)

Definition eqb_target_program (tp1 tp2 : target_program) : bool :=
  match tp1 with
  | Target_program bcis1 =>
      match tp2 with
      | Target_program bcis2 =>
          eqb_list_byte_code_instruction bcis1 bcis2
      end
  end.

Compute (eqb_target_program (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil))
           (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil))).
Compute (eqb_target_program (Target_program (PUSH 3 :: PUSH 10 :: ADD :: nil))
           (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil))).

Definition test_compile_alt (candidate : source_program -> target_program) : bool :=
  test_compile_aux (fun ae => match candidate (Source_program(ae)) with
                              | Target_program bcis =>
                                  bcis
                              end).

Definition test_compile (candidate : source_program -> target_program) : bool :=
  (eqb_target_program
     (candidate (Source_program (Minus (Literal 3) (Literal 10))))
     (Target_program (PUSH 3 :: PUSH 10 :: SUB :: nil)))
  && (eqb_target_program
        (candidate (Source_program (Minus (Minus (Literal 3) (Literal 1)) (Plus (Literal 3) (Literal 2)))))
        (Target_program (PUSH 3 :: PUSH 1 :: SUB :: PUSH 3 :: PUSH 2 :: ADD :: SUB :: nil))).

Definition compile (sp : source_program) : target_program :=
  match sp with
  | Source_program ae => Target_program (compile_aux ae)
  end.

Compute (test_compile compile = true).
Compute (test_compile_alt compile = true).

(* Task 7c. verify that your function satisfies the specification. *)

Theorem compile_satisfies_the_specification_of_compile :
  specification_of_compile compile.
Proof.
  unfold specification_of_compile.
  intros compile_aux' H_spec ae.
  unfold compile.
  Check (there_is_at_most_one_compile_aux_function).
  Check (there_is_at_most_one_compile_aux_function compile_aux compile_aux').
  Check (there_is_at_most_one_compile_aux_function compile_aux compile_aux'
           compile_aux_satisfies_the_specification_of_compile_aux
           H_spec
           ae).
  rewrite -> (there_is_at_most_one_compile_aux_function
                compile_aux compile_aux'
                compile_aux_satisfies_the_specification_of_compile_aux
                H_spec ae).
  reflexivity.
Qed.

(* Task 8:
   implement an alternative compiler
   using an auxiliary function with an accumulator
   and that does not use ++ but :: instead,
   and prove that it satisfies the specification.

   Subsidiary question:
   Are your compiler and your alternative compiler equivalent?
   How can you tell?
 *)

Fixpoint compile_alt_aux_aux (ae : arithmetic_expression) (a : list byte_code_instruction) : list byte_code_instruction :=
  match ae with
  | Literal n => PUSH n :: a
  | Plus ae1 ae2 => compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (ADD :: a))
  | Minus ae1 ae2 => compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (SUB :: a))
  end.

Lemma fold_unfold_compile_alt_aux_aux_Literal :
  forall (n : nat)
         (a : list byte_code_instruction),
    compile_alt_aux_aux (Literal n) a =
      PUSH n :: a.
Proof.
  fold_unfold_tactic compile_alt_aux_aux.
Qed.

Lemma fold_unfold_compile_alt_aux_aux_Plus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_alt_aux_aux (Plus ae1 ae2) a =
      compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (ADD :: a)).
Proof.
  fold_unfold_tactic compile_alt_aux_aux.
Qed.

Lemma fold_unfold_compile_alt_aux_aux_Minus :
  forall (ae1 ae2 : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_alt_aux_aux (Minus ae1 ae2) a =
      compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (SUB :: a)).
Proof.
  fold_unfold_tactic compile_alt_aux_aux.
Qed.

Lemma about_compile_alt_aux_aux :
  forall (ae : arithmetic_expression)
         (a : list byte_code_instruction),
    compile_alt_aux_aux ae a = (compile_alt_aux_aux ae nil) ++ a.
Proof.
  Compute (let ae := (Plus (Literal 5) (Literal 2)) in
           let a := (PUSH 50 :: PUSH 20 :: nil) in
           compile_alt_aux_aux ae a = (compile_alt_aux_aux ae nil) ++ a).
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro a.
  - rewrite -> 2(fold_unfold_compile_alt_aux_aux_Literal).
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - Check (fold_unfold_compile_alt_aux_aux_Plus).
    rewrite -> 2fold_unfold_compile_alt_aux_aux_Plus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: a))).
    Search ((_ ++ _) ++ _ = _).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (ADD :: a)).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite -> 2fold_unfold_compile_alt_aux_aux_Minus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: a))).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (SUB :: a)).
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
Qed.

Definition make_Eureka_lemma (A : Type) (id_A : A) (combine_A : A -> A -> A) (c : A -> A) (a : A) : Prop :=
  c a = combine_A (c id_A) a.

Lemma about_compile_alt_aux_aux_alt :
  (* expressed using make_Eureka_lemma *)
  forall (ae : arithmetic_expression) (a : list byte_code_instruction),
    make_Eureka_lemma (list byte_code_instruction) nil (fun x y => x ++ y) (compile_alt_aux_aux ae) a.
Proof.
  unfold make_Eureka_lemma.
  intro ae.
  induction ae as [ n | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intro a.
  - rewrite -> 2(fold_unfold_compile_alt_aux_aux_Literal).
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - Check (fold_unfold_compile_alt_aux_aux_Plus).
    rewrite -> 2fold_unfold_compile_alt_aux_aux_Plus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (ADD :: a))).
    Search ((_ ++ _) ++ _ = _).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (ADD :: a)).
    rewrite -> (IHae2 (ADD :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
  - rewrite -> 2fold_unfold_compile_alt_aux_aux_Minus.
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: nil))).
    rewrite -> (IHae1 (compile_alt_aux_aux ae2 (SUB :: a))).
    rewrite -> app_assoc_reverse.
    rewrite -> (IHae2 (SUB :: a)).
    rewrite -> (IHae2 (SUB :: nil)).
    rewrite -> app_assoc_reverse.
    rewrite -> fold_unfold_list_append_cons.
    rewrite -> fold_unfold_list_append_nil.
    reflexivity.
Qed.

Definition compile_alt_aux (ae : arithmetic_expression) : list byte_code_instruction :=
   (compile_alt_aux_aux ae nil).

Compute (test_compile_aux compile_alt_aux = true).

Definition compile_alt (sp : source_program) : target_program :=
  match sp with
  | Source_program ae => Target_program (compile_alt_aux ae)
  end.

Theorem compile_alt_aux_satisfies_the_specification_of_compile_aux :
  specification_of_compile_aux compile_alt_aux.
Proof.
  unfold specification_of_compile_aux.
  split.
  - intro n.
    unfold compile_alt_aux.
    rewrite -> fold_unfold_compile_alt_aux_aux_Literal.
    reflexivity.
  - split.
    + unfold compile_alt_aux.
      intros ae1 ae2.
      rewrite -> fold_unfold_compile_alt_aux_aux_Plus.
      Check (about_compile_alt_aux_aux).
      Check (about_compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (ADD :: nil))).
      rewrite -> (about_compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (ADD :: nil))).
      rewrite -> (about_compile_alt_aux_aux ae2 (ADD :: nil)).
      reflexivity.
    + unfold compile_alt_aux.
      intros ae1 ae2.
      rewrite -> fold_unfold_compile_alt_aux_aux_Minus.
      rewrite -> (about_compile_alt_aux_aux ae1 (compile_alt_aux_aux ae2 (SUB :: nil))).
      rewrite -> (about_compile_alt_aux_aux ae2 (SUB :: nil)).
      reflexivity.
Qed.

Check (compile_aux).

Theorem compile_aux_and_compile_alt_aux_are_equivalent :
  forall ae : arithmetic_expression,
    compile_aux ae = compile_alt_aux ae.
Proof.
  exact (there_is_at_most_one_compile_aux_function
           compile_aux
           compile_alt_aux
           compile_aux_satisfies_the_specification_of_compile_aux
           compile_alt_aux_satisfies_the_specification_of_compile_aux).
Qed.

(* ********** *)

(* Task 9 (the capstone):
   Prove that interpreting an arithmetic expression gives the same result
   as first compiling it and then executing the compiled program.
 *)

Lemma about_ae_OK :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (n : nat),
        evaluate ae = Expressible_nat n -> fetch_decode_execute_loop (compile_aux ae) ds = OK (n :: ds)).
Proof.
  intro ae.
  induction ae as [ n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intros ds n H_ae.
  - rewrite -> fold_unfold_compile_aux_Literal.
    rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
    unfold decode_execute.
    rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
    rewrite -> fold_unfold_evaluate_Literal in H_ae.
    injection H_ae as eq_n'_n.
    rewrite -> eq_n'_n.
    reflexivity.
  - rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fetch_decode_execute_loop_concatenation_v1.
    rewrite -> fold_unfold_evaluate_Plus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + Check (IHae1 ds n1 eq_refl).
       rewrite -> (IHae1 ds n1 eq_refl).
       rewrite -> fetch_decode_execute_loop_concatenation_v1.
       Check (IHae2 (n1 :: ds) n2 eq_refl).
       rewrite -> (IHae2 (n1 :: ds) n2 eq_refl).
       rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
       unfold decode_execute.
       rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
       injection H_ae as eq_sum_n1_n2_n.
       rewrite -> eq_sum_n1_n2_n.
       reflexivity.
    + discriminate H_ae.
    + discriminate H_ae.
  - rewrite -> fold_unfold_compile_aux_Minus.
    rewrite -> fetch_decode_execute_loop_concatenation_v1.
    rewrite -> fold_unfold_evaluate_Minus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + case (n1 <? n2) as [ | ] eqn:H_n1_n2.
      * discriminate H_ae.
      * Check (IHae1 ds n1 eq_refl).
        rewrite -> (IHae1 ds n1 eq_refl).
        rewrite -> fetch_decode_execute_loop_concatenation_v1.
        Check (IHae2 (n1 :: ds) n2 eq_refl).
        rewrite -> (IHae2 (n1 :: ds) n2 eq_refl).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> H_n1_n2.
        rewrite -> fold_unfold_fetch_decode_execute_loop_nil.
        injection H_ae as eq_sub_n1_n2_n.
        rewrite -> eq_sub_n1_n2_n.
        reflexivity.
    + discriminate H_ae.
    + discriminate H_ae.
Qed.

Lemma about_ae_KO :
  forall (ae : arithmetic_expression)
         (ds : data_stack),
    (forall (s : string),
        evaluate ae = Expressible_msg s -> fetch_decode_execute_loop (compile_aux ae) ds = KO s).
Proof.
  intro ae.
  induction ae as [ n' | ae1 IHae1 ae2 IHae2 | ae1 IHae1 ae2 IHae2 ]; intros ds s H_ae.
  - rewrite -> fold_unfold_evaluate_Literal in H_ae.
    discriminate H_ae.
  - rewrite -> fold_unfold_compile_aux_Plus.
    rewrite -> fetch_decode_execute_loop_concatenation_v1.
    rewrite -> fold_unfold_evaluate_Plus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + discriminate H_ae.
    + Check (about_ae_OK).
      Check (about_ae_OK ae1 ds n1).
      Check (about_ae_OK ae1 ds n1 H_ev_ae1).
      rewrite -> (about_ae_OK ae1 ds n1 H_ev_ae1).
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      Check (IHae2 (n1 :: ds) s H_ae).
      rewrite -> (IHae2 (n1 :: ds) s H_ae).
      reflexivity.
    + Check (IHae1 ds s H_ae).
      rewrite -> (IHae1 ds s H_ae).
      reflexivity.
  - rewrite -> fold_unfold_evaluate_Minus in H_ae.
    case (evaluate ae1) as [ n1 | s1 ] eqn:H_ev_ae1.
    case (evaluate ae2) as [ n2 | s2 ] eqn:H_ev_ae2.
    + case (n1 <? n2) as [ | ] eqn:H_n1_n2.
      * rewrite -> fold_unfold_compile_aux_Minus.
        rewrite -> fetch_decode_execute_loop_concatenation_v1.
        Check (about_ae_OK).
        Check (about_ae_OK ae1 ds n1).
        Check (about_ae_OK ae1 ds n1 H_ev_ae1).
        rewrite -> (about_ae_OK ae1 ds n1 H_ev_ae1).
        rewrite -> fetch_decode_execute_loop_concatenation_v1.
        Check (about_ae_OK ae2 (n1 :: ds) n2 H_ev_ae2).
        rewrite -> (about_ae_OK ae2 (n1 :: ds) n2 H_ev_ae2).
        rewrite -> fold_unfold_fetch_decode_execute_loop_cons.
        unfold decode_execute.
        rewrite -> H_n1_n2.
        injection H_ae as H_s.
        rewrite <- H_s.
        reflexivity.
      * discriminate H_ae.
    + rewrite -> fold_unfold_compile_aux_Minus.
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      rewrite -> (about_ae_OK ae1 ds n1 H_ev_ae1).
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      rewrite -> (IHae2 (n1 :: ds) s H_ae).
      reflexivity.
    + rewrite -> fold_unfold_compile_aux_Minus.
      rewrite -> fetch_decode_execute_loop_concatenation_v1.
      rewrite -> (IHae1 ds s1 eq_refl).
      injection H_ae as eq_s1_s.
      rewrite -> eq_s1_s.
      reflexivity.
Qed.

Theorem the_commuting_diagram :
  forall sp : source_program,
    interpret sp = run (compile sp).
Proof.
  intro sp.
  destruct sp as [ae].
  unfold compile.
  unfold run.
  unfold interpret.
  case (evaluate ae) as [n' | s] eqn:H_ae.
  - rewrite -> (about_ae_OK ae nil n' H_ae).
    reflexivity.
  - rewrite -> (about_ae_KO ae nil s H_ae).
    reflexivity.
Qed.

(* end of term-project *)

(* from the ashes, rises another *)

Proposition Literal_0_is_neutral_for_Plus_on_the_left :
  forall ae : arithmetic_expression,
    evaluate (Plus (Literal 0) ae) = evaluate ae.
Proof.
  intro ae.
  rewrite -> fold_unfold_evaluate_Plus.
  rewrite -> fold_unfold_evaluate_Literal.
  case (evaluate ae) as [n | s].
  - rewrite -> (Nat.add_0_l n).
    reflexivity.
  - reflexivity.
Qed.

Proposition Literal_0_is_neutral_for_Plus_on_the_right :
  forall ae : arithmetic_expression,
    evaluate (Plus ae (Literal 0)) = evaluate ae.
Proof.
  intro ae.
  rewrite -> fold_unfold_evaluate_Plus.
  rewrite -> fold_unfold_evaluate_Literal.
  case (evaluate ae) as [n | s].
  - rewrite -> (Nat.add_0_r n).
    reflexivity.
  - reflexivity.
Qed.

Proposition Plus_is_associative :
  forall ae1 ae2 ae3 : arithmetic_expression,
    evaluate (Plus ae1 (Plus ae2 ae3)) = evaluate (Plus (Plus ae1 ae2) ae3).
Proof.
  intros ae1 ae2 ae3.
  rewrite ->4 fold_unfold_evaluate_Plus.
  case (evaluate ae1) as [n1 | s1].
  - case (evaluate ae2) as [n2 | s2].
    + case (evaluate ae3) as [n3 | s3].
      * rewrite -> Nat.add_assoc.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Proposition Plus_is_commutative :
  forall ae1 ae2 : arithmetic_expression,
    evaluate (Plus ae1 ae2) = evaluate (Plus ae2 ae1).
Proof.
  intros ae1 ae2.
  rewrite ->2 fold_unfold_evaluate_Plus.
  case (evaluate ae1) as [n1 | s1].
  - case (evaluate ae2) as [n2 | s2].
    + rewrite -> Nat.add_comm.
      reflexivity.
    + reflexivity.
  - case (evaluate ae2) as [n2 | s2].
    + reflexivity.
    + (* not commutative if messages are different.*)
Abort.

Proposition Plus_is_not_commutative :
  exists ae1 ae2: arithmetic_expression,
    evaluate ae1 <> evaluate ae2.
Proof.
  exists (Minus (Literal 1) (Literal 3)).
  exists (Minus (Literal 2) (Literal 3)).
  rewrite ->2 fold_unfold_evaluate_Minus.
  rewrite ->3 fold_unfold_evaluate_Literal.
  compute.
  discriminate.
Qed.

Proposition Plus_is_conditionally_commutative :
  forall ae1 ae2,
  forall n : nat,
    ((forall n1 : nat,
         evaluate ae1 = Expressible_nat n1) \/
       (forall n2 : nat,
           evaluate ae2 = Expressible_nat n2)) ->
    evaluate (Plus ae1 ae2) = evaluate (Plus ae2 ae1).
Proof.
  intros ae1 ae2 n H_n1_nat_or_n2_nat.
  destruct H_n1_nat_or_n2_nat as [H_n1_nat | H_n2_nat];
    rewrite ->2 fold_unfold_evaluate_Plus.
  - rewrite -> (H_n1_nat n). 
    case (evaluate ae2) as [n2 | s2].
    + rewrite -> Nat.add_comm.
      reflexivity.
    + reflexivity.
  - rewrite -> (H_n2_nat n). 
    case (evaluate ae1) as [n1 | s1].
    + rewrite -> Nat.add_comm.
      reflexivity.
    + reflexivity.
Qed.
