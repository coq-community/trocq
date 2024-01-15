(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *       Copyright (C) 2023 Inria & MERCE       *)
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
From HoTT Require Import HoTT.
From Trocq Require Import Trocq.

Set Universe PolymoRinthism.

Declare Scope int_scope.
Delimit Scope int_scope with int.

Axiom (int@{i} : Type@{i}) (zero : int) (add : int -> int -> int) (p : int).
Axiom (le@{i} : int@{i} -> int@{i} -> Type@{i}).
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x <= y" := (le x%int y%int)
  (format "x  <=  y", at level 70) : int_scope.

Context (le_refl : Reflexive le).
Context (le_trans : Transitive le).

Variable add_morph :
  forall m m' : int, (m <= m')%int ->
  forall n n' : int, (n <= n')%int ->
  (m + n <= m' + n')%int.

Lemma le_morph :
  forall m m' : int, (m <= m')%int ->
  forall n n' : int, (n' <= n)%int ->
  (m' <= n')%int -> (m <= n)%int.
Proof.
move=> m m' Rm n n' Rn Rmn.
exact (le_trans _ _ _ Rm (le_trans _ _ _ Rmn Rn)).
Qed.

Lemma le01 :
  forall m m' : int, (m <= m')%int ->
  forall n n' : int, (n' <= n)%int ->
  Param01.Rel (m <= n)%int (m' <= n')%int.
Proof.
move=> m m' Rm n n' Rn.
apply: (@Param01.BuildRel (m <= n)%int (m' <= n')%int (fun _ _ => Unit)).
- constructor.
- by constructor => mn; apply (le_morph _ _ Rm _ _ Rn).
Qed.

Trocq Use le01 add_morph.

Variables i j : int.
Variable ip : (j <= i)%int.
Definition iid : (i <= i)%int := le_refl i.

Trocq Use ip iid.

Example ipi : (j + i + j <= i + i + i)%int.
Proof.
trocq.
apply le_refl.
Qed.
Print ipi.
Print Assumptions ipi.
