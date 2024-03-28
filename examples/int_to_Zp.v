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
Delimit Scope int_scope with ℤ.
Local Open Scope int_scope.
Declare Scope Zmod7_scope.
Delimit Scope Zmod7_scope with Zmod7.
Local Open Scope Zmod7_scope.

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(***
We setup an axiomatic context in order not to develop
arithmetic modulo in Coq/HoTT.
**)
Axiom (int@{i} : Type@{i}) (zero : int) (add : int -> int -> int)
      (mul : int -> int -> int) (one : int).
Axiom (addC : forall m n, add m n = add n m).
Axiom (Zmod7 : Type) (zerop : Zmod7) (addp : Zmod7 -> Zmod7 -> Zmod7)
      (mulp : Zmod7 -> Zmod7 -> Zmod7) (onep : Zmod7).
Axiom (modp : int -> Zmod7) (reprp : Zmod7 -> int)
      (reprpK : forall x, modp (reprp x) = x).

Definition eqmodp (x y : int) := modp x = modp y.

(* for now translations need the support of a global reference: *)
Definition eq_Zmod7 (x y : Zmod7) := (x = y).
Arguments eq_Zmod7 /.

Notation "0" := zero : int_scope.
Notation "0" := zerop : Zmod7_scope.
Notation "1" := one : int_scope.
Notation "1" := onep : Zmod7_scope.
Notation "x == y" := (eqmodp x%int y%int)
  (format "x  ==  y", at level 70) : int_scope.
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zmod7 y%Zmod7) : Zmod7_scope.
Notation "x * y" := (mul x%int y%int) : int_scope.
Notation "x * y" := (mulp x%Zmod7 y%Zmod7) : Zmod7_scope.
Notation "m ²" := (m * m)%int (at level 2) : int_scope.
Notation "m ²" := (m * m)%Zmod7 (at level 2) : Zmod7_scope.
Notation "m ³" := (m * m * m)%int (at level 2) : int_scope.
Notation "m ³" := (m * m * m)%Zmod7 (at level 2) : Zmod7_scope.
Notation "x ≡ y" := (eqmodp x%int y%int)
  (format "x  ≡  y", at level 70) : int_scope.
Notation "x ≢ y" := (not (eqmodp x%int y%int))
  (format "x  ≢  y", at level 70) : int_scope.
Notation "x ≠ y" := (not (x = y)).
Notation "ℤ/7ℤ" := Zmod7.
Notation ℤ := int.
Notation "P ∨ Q" := (P + Q)%type.

Module IntToZmod7.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

Axiom Rzero : Rp zero zerop.
Axiom Rone : Rp one onep.
Variable Radd : binop_param Rp Rp Rp add addp.
Variable Rmul : binop_param Rp Rp Rp mul mulp.
Variable Reqmodp01 : forall (m : int) (x : Zmod7), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmod7 x y).

Trocq Use Rp Rmul Rzero Rone Param10_paths Reqmodp01.
Trocq Use Param01_sum.

Lemma IntRedModZp : forall (m n p : ℤ),
  m = n²%ℤ -> m = p³%ℤ  -> m ≡ 0 ∨ m ≡ 1.
Proof.
trocq=> /=.
Admitted.

(* Print Assumptions IntRedModZp. (* No Univalence *) *)

End IntToZmod7.

Module Zmod7ToInt.

Definition Rp := SplitSurj.toParamSym (SplitSurj.Build reprpK).

Axiom Rzero : Rp zerop zero.
Variable Radd : binop_param Rp Rp Rp addp add.
Variable paths_to_eqmodp : binop_param Rp Rp iff paths eqmodp.

Trocq Use Rp Param01_paths Param10_paths Radd Rzero.

Goal (forall x y, x + y = y + x)%Zmod7.
Proof.
  trocq.
  exact addC.
Qed.

Goal (forall x y z, x + y + z = y + x + z)%Zmod7.
Proof.
  intros x y z.
  suff addpC: forall x y, (x + y = y + x)%Zmod7. {
    by rewrite (addpC x y). }
  trocq.
  exact addC.
Qed.

End Zmod7ToInt.
