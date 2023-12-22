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
From Coq Require Import Setoid.
From Trocq Require Import Trocq.

Set Universe PolymoRinthism.

Declare Scope int_scope.
Delimit Scope int_scope with int.

Axiom (int : Type) (zero : int) (add : int -> int -> int) (p : int).
Axiom (eqmodp : int -> int -> Prop).
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x == y" := (eqmodp x%int y%int)
  (format "x  ==  y", at level 70) : int_scope.

Context (eqp_refl : Reflexive eqmodp).
Context (eqp_sym : Symmetric eqmodp).
Context (eqp_trans : Transitive eqmodp).

Variable add_morph : 
  forall m m' : int, (m == m')%int ->  
  forall n n' : int, (n == n')%int ->  
  (m + n == m' + n')%int. 

Lemma eqmodp_morph : 
  forall m m' : int, (m == m')%int ->  
  forall n n' : int, (n == n')%int ->  
  (m' == n')%int -> (m == n)%int.
Proof.
move=> m m' Rm n n' Rn Rmn.
exact (eqp_trans _ _ _ Rm (eqp_trans _ _ _ Rmn (eqp_sym _ _ Rn))).
Qed.

Lemma eqmodp01 : 
  forall m m' : int, (m == m')%int ->  
  forall n n' : int, (n == n')%int ->  
  Param01.Rel (m == n)%int (m' == n')%int.
Proof.
move=> m m' Rm n n' Rn.
apply: (@Param01.BuildRel (m == n)%int (m' == n')%int (fun _ _ => unit)).
- constructor.
- by constructor => mn; apply (eqmodp_morph _ _ Rm _ _ Rn).
Qed.

Trocq Use eqmodp01.
Trocq Use add_morph.

Variables i : int.
Let j := (i + p)%int.
Variable ip : (j == i)%int.
Definition iid : (i == i)%int := eqp_refl i.

Trocq Use ip.
Trocq Use iid.

Example ipi : (j + i == i + i)%int.
Proof.
trocq.
apply eqp_refl.
Qed.

Print ipi.
Print Assumptions ipi.
