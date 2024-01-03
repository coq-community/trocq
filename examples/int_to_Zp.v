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
From Trocq Require Import Trocq.

Set Universe Polymorphism.

Declare Scope int_scope.
Delimit Scope int_scope with int.
Declare Scope Zmodp_scope.
Delimit Scope Zmodp_scope with Zmodp.

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(***
We setup an axiomatic context in order not to develop
arithmetic modulo in Coq/HoTT.
**)
Axiom (int@{i} : Type@{i}) (zero : int) (add : int -> int -> int)
      (mul : int -> int -> int).
Axiom (addC : forall m n, add m n = add n m).
Axiom (Zmodp : Type) (zerop : Zmodp) (addp : Zmodp -> Zmodp -> Zmodp)
      (mulp : Zmodp -> Zmodp -> Zmodp).
Axiom (modp : int -> Zmodp) (reprp : Zmodp -> int)
      (reprpK : forall x, modp (reprp x) = x).

Definition eqmodp (x y : int) := modp x = modp y.

(* Axiom (eqp_refl : Reflexive eqmodp). *)
(* Axiom (eqp_sym : Symmetric eqmodp). *)
(* Axiom (eqp_trans : Transitive eqmodp). *)

Notation "x == y" := (eqmodp x%int y%int)
  (format "x  ==  y", at level 70) : int_scope.
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zmodp y%Zmodp) : Zmodp_scope.
Notation "x * y" := (mul x%int y%int) : int_scope.
Notation "x * y" := (mulp x%Zmodp y%Zmodp) : Zmodp_scope.

Module IntToZmodp.

Definition Rp := SplitSurj.toParam
  (SplitSurj.Build_type modp reprp reprpK).

Axiom Rzero' : Rp zero zerop.
Variable Radd' : binop_param Rp Rp Rp add addp.
Variable Rmul' : binop_param Rp Rp Rp mul mulp.

Trocq Use Rmul'.
Trocq Use Rzero'.
Trocq Use Param10_paths.
Trocq Use Rp.

Definition eq_Zmodp (x y : Zmodp) := (x = y).
(* Bug if we inline the previous def in the following axiom *)
Axiom Reqmodp01 : forall (m : int) (x : Zmodp), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmodp x y).
Trocq Use Reqmodp01.
Arguments eq_Zmodp /.

Hypothesis RedZmodpEq0 :
  (forall (m n p : Zmodp), (m = n * n)%Zmodp -> m = (p * p * p)%Zmodp ->
    m = zerop).

Lemma IntRedModZp : forall (m n p : int),
  (m = n * n)%int -> m = (p * p * p)%int -> eqmodp m zero.
Proof.
trocq; simpl.
exact @RedZmodpEq0.
Qed.

(* Print Assumptions IntRedModZp. (* No Univalence *) *)

End IntToZmodp.

Module ZmodpToInt.

Definition Rp x n := eqmodp (reprp x) n.

Definition Rp2a2b@{i} : Param2a2b.Rel Zmodp@{i} int@{i}.
Proof.
unshelve econstructor.
- exact Rp.
- unshelve econstructor.
  + exact reprp.
  + move=> a b; move=> /(ap modp); exact.
- unshelve econstructor.
  + exact modp.
  + by move=> a b; rewrite /Rp/sym_rel/eqmodp reprpK => <-.
Defined.

Axiom Rzero : Rp zerop zero.
Variable Radd : binop_param Rp Rp Rp addp add.
Variable paths_to_eqmodp : binop_param Rp Rp iff paths eqmodp.

Trocq Use Rp2a2b.
Trocq Use Param01_paths.
Trocq Use Param10_paths.
Trocq Use Radd.
Trocq Use Rzero.

Goal (forall x y, x + y = y + x)%Zmodp.
Proof.
  trocq.
  exact addC.
Qed.

Goal (forall x y z, x + y + z = y + x + z)%Zmodp.
Proof.
  intros x y z.
  suff addpC: forall x y, (x + y = y + x)%Zmodp. {
    by rewrite (addpC x y). }
  trocq.
  exact addC.
Qed.

End ZmodpToInt.
