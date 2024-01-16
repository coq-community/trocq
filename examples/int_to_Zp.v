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
Local Open Scope int_scope.
Declare Scope Zmodp_scope.
Delimit Scope Zmodp_scope with Zmodp.
Local Open Scope Zmodp_scope.

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

(* for now translations need the support of a global reference: *)
Definition eq_Zmodp (x y : Zmodp) := (x = y).
Arguments eq_Zmodp /.

Notation "0" := zero : int_scope.
Notation "0" := zerop : Zmodp_scope.
Notation "x == y" := (eqmodp x%int y%int)
  (format "x  ==  y", at level 70) : int_scope.
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zmodp y%Zmodp) : Zmodp_scope.
Notation "x * y" := (mul x%int y%int) : int_scope.
Notation "x * y" := (mulp x%Zmodp y%Zmodp) : Zmodp_scope.

Module IntToZmodp.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

Axiom Rzero : Rp zero zerop.
Variable Radd : binop_param Rp Rp Rp add addp.
Variable Rmul : binop_param Rp Rp Rp mul mulp.
Variable Reqmodp01 : forall (m : int) (x : Zmodp), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmodp x y).

Trocq Use Rp Rmul Rzero Param10_paths Reqmodp01.

Lemma IntRedModZp :
 (forall (m n p : Zmodp), (m = n * n)%Zmodp -> m = 0) ->
 forall (m n p : int), (m = n * n)%int -> (m == 0)%int.
Proof.
move=> Hyp.
trocq; simpl.
exact: Hyp.
Qed.

(* Print Assumptions IntRedModZp. (* No Univalence *) *)

End IntToZmodp.

Module ZmodpToInt.

Definition Rp := SplitSurj.toParamSym (SplitSurj.Build reprpK).

Axiom Rzero : Rp zerop zero.
Variable Radd : binop_param Rp Rp Rp addp add.
Variable paths_to_eqmodp : binop_param Rp Rp iff paths eqmodp.

Trocq Use Rp Param01_paths Param10_paths Radd Rzero.

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
