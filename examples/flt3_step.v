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
Declare Scope Zmod9_scope.
Delimit Scope Zmod9_scope with Zmod9.
Local Open Scope Zmod9_scope.

Definition unop_param {X X'} RX {Y Y'} RY
   (f : X -> Y) (g : X' -> Y') :=
  forall x x', RX x x' -> RY (f x) (g x').

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(***
We setup an axiomatic context in order not to develop
arithmetic modulo in Coq/HoTT.
**)
Axiom (int@{i} : Type@{i}) (zero : int) (add : int -> int -> int)
      (mul : int -> int -> int) (one : int)
      (mod3 : int -> int).
Axiom (addC : forall m n, add m n = add n m).
Axiom (Zmod9 : Type) (zerop : Zmod9) (addp : Zmod9 -> Zmod9 -> Zmod9)
      (mulp : Zmod9 -> Zmod9 -> Zmod9) (onep : Zmod9).
Axiom (modp : int -> Zmod9) (reprp : Zmod9 -> int)
      (reprpK : forall x, modp (reprp x) = x)
      (modp3 : Zmod9 -> Zmod9).

Definition eqmodp (x y : int) := modp x = modp y.

(* for now translations need the support of a global reference: *)
Definition eq_Zmod9 (x y : Zmod9) := (x = y).
Arguments eq_Zmod9 /. 

Notation "0" := zero : int_scope.
Notation "0" := zerop : Zmod9_scope.
Notation "1" := one : int_scope.
Notation "1" := onep : Zmod9_scope.
Notation "x == y" := (eqmodp x%int y%int)
  (format "x  ==  y", at level 70) : int_scope.
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zmod9 y%Zmod9) : Zmod9_scope.
Notation "x * y" := (mul x%int y%int) : int_scope.
Notation "x * y" := (mulp x%Zmod9 y%Zmod9) : Zmod9_scope.

Module IntToZmod9.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

Axiom Rzero : Rp zero zerop.
Axiom Rone : Rp one onep.
Variable Rmod3 : unop_param Rp Rp mod3 modp3.
Variable Radd : binop_param Rp Rp Rp add addp.
Variable Rmul : binop_param Rp Rp Rp mul mulp.
Variable Reqmodp01 : forall (m : int) (x : Zmod9), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmod9 x y).

Trocq Use Rp Rmul Rzero Rone Radd Rmod3 Param10_paths Reqmodp01.
Trocq Use Param01_sum.
Notation not A := (A -> Empty). 

Variable Param01_Empty : Param01.Rel Empty Empty.
Variable Param10_Empty : Param10.Rel Empty Empty.

Trocq Use Param01_Empty.
Trocq Use Param10_Empty.

Lemma flt3_step : forall (m n p : int),
   (not (eqmodp (mod3 (m * n * p)%int) 0%int)) ->
  not ((m * m * m) + (n * n * n) = (p * p * p))%int.
Proof.
trocq; simpl.
Admitted.


(* Print Assumptions IntRedModZp. (* No Univalence *) *)

End IntToZmod9.

Module Zmod9ToInt.

Definition Rp := SplitSurj.toParamSym (SplitSurj.Build reprpK).

Axiom Rzero : Rp zerop zero.
Variable Radd : binop_param Rp Rp Rp addp add.
Variable paths_to_eqmodp : binop_param Rp Rp iff paths eqmodp.

Trocq Use Rp Param01_paths Param10_paths Radd Rzero.

Goal (forall x y, x + y = y + x)%Zmod9.
Proof.
  trocq.
  exact addC.
Qed.

Goal (forall x y z, x + y + z = y + x + z)%Zmod9.
Proof.
  intros x y z.
  suff addpC: forall x y, (x + y = y + x)%Zmod9. {
    by rewrite (addpC x y). }
  trocq.
  exact addC.
Qed.

End Zmod9ToInt.
