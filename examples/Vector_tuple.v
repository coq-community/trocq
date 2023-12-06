(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *           Copyright (C) 2023 MERCE           *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From Coq Require Import ssreflect.
From Coq Require Import Vectors.VectorDef.
From Trocq Require Import Trocq.

Set Universe Polymorphism.

Module Vector.

Inductive t (A : Type) : nat -> Type :=
  | nil : t A 0
  | cons : forall (n : nat), A -> t A n -> t A (S n).
Arguments nil {_}.
Arguments cons {_ _}.

Definition const : forall {A : Type} (a : A) (n : nat), t A n :=
  fun A a =>
    fix F n :=
      match n with
      | O => nil
      | S n' => cons a (F n')
      end.

Definition append :
  forall {A : Type} {n1 n2 : nat} (v1 : t A n1) (v2 : t A n2),
    t A (n1 + n2) :=
  fun A n1 n2 v1 v2 =>
    (fix F n (v : t A n) {struct v} : t A (n + n2) :=
      match v with
      | nil => v2
      | @cons _ n a v => cons a (F n v)
      end) n1 v1.

Lemma append_const {A : Type} (a : A) (n1 n2 : nat) :
  append (const a n1) (const a n2) = const a (n1 + n2).
Proof.
  induction n1.
  - reflexivity.
  - simpl. apply ap. assumption.
Qed.

End Vector.

Definition tuple (A : Type) : nat -> Type :=
  fix F n :=
    match n with
    | O => Unit
    | S n' => F n' * A
    end.

Definition const : forall {A : Type} (a : A) (n : nat), tuple A n :=
  fun A a =>
    fix F n :=
      match n with
      | O => tt
      | S n' => (F n', a)
    end.

Definition append :
  forall {A : Type} {n1 n2 : nat} (t1 : tuple A n1) (t2 : tuple A n2),
    tuple A (n1 + n2) :=
  fun A =>
    fix F n1 :=
      match n1 with
      | O => fun n2 _ t2 => t2
      | S n =>
        fun n2 t1 t2 =>
          match t1 with
          | (t, a) => (F n n2 t t2, a)
          end
      end.

(* ========================================================================== *)

(* tuple ~ vector *)

Inductive tuple_vectorR (A A' : Type) (AR : A -> A' -> Type) :
  forall (n n' : nat) (nR : natR n n'),
    tuple A n -> Vector.t A' n' -> Type :=
  | emptyR : tuple_vectorR A A' AR O O OR tt (@Vector.nil A')
  | consR :
    forall
      (n n' : nat) (nR : natR n n') (a : A) (a' : A') (aR : AR a a')
      (t : tuple A n) (v : Vector.t A' n'),
        tuple_vectorR A A' AR n n' nR t v ->
          tuple_vectorR A A' AR (S n) (S n') (SR n n' nR)
            (t, a) (Vector.cons a' v).

Definition tuple_to_vector
  (A A' : Type) (map : A -> A') (n : nat) : tuple A n -> Vector.t A' n.
Proof.
  intro t.
  induction n.
  - exact Vector.nil.
  - destruct t as (t', a). apply Vector.cons.
    + exact (map a).
    + exact (IHn t').
Defined.

Definition vector_to_tuple
  (A A' : Type) (map : A -> A') (n : nat) : Vector.t A n -> tuple A' n.
Proof.
  intro v. induction v.
  - exact tt.
  - simpl. exact (IHv, map a).
Defined.

Axiom cheat : forall A, A.
Ltac cheat := apply cheat.

Definition Param02b_tuple_vector
  (A A' : Type) (AR : Param00.Rel A A') (n n' : nat) (nR : natR n n') :
    Param02b.Rel (tuple A n) (Vector.t A' n').
Proof.
  unshelve econstructor.
  - apply (tuple_vectorR A A' AR n n' nR).
  - constructor.
  - unshelve econstructor.
    + cheat.
    + cheat.
Defined.

Definition Param_append
  (A A' : Type) (AR : Param00.Rel A A')
  (n1 n1' : nat) (n1R : natR n1 n1') (n2 n2' : nat) (n2R : natR n2 n2')
  (t1 : tuple A n1) (v1 : Vector.t A' n1')
  (tv1R : tuple_vectorR A A' AR n1 n1' n1R t1 v1)
  (t2 : tuple A n2) (v2 : Vector.t A' n2')
  (tv2R : tuple_vectorR A A' AR n2 n2' n2R t2 v2) :
    tuple_vectorR
      A A' AR (n1 + n2) (n1' + n2') (Param_add n1 n1' n1R n2 n2' n2R)
        (append t1 t2) (Vector.append v1 v2).
Proof.
  cheat.
Defined.

Definition Param_const
  (A A' : Type) (AR : Param00.Rel A A') (a : A) (a' : A') (aR : AR a a')
  (n n' : nat) (nR : natR n n') :
    tuple_vectorR A A' AR n n' nR (const a n) (Vector.const a' n').
Proof.
  cheat.
Defined.

Trocq Use Param00_nat.
Trocq Use Param2a0_nat.
Trocq Use Param_add.
Trocq Use Param02b_tuple_vector.
Trocq Use Param_append.
Trocq Use Param_const.
Trocq Use Param01_paths.

Lemma append_const : forall {A : Type} (a : A) (n1 n2 : nat),
  append (const a n1) (const a n2) = const a (n1 + n2).
Proof.
  trocq. exact @Vector.append_const.
Qed.
