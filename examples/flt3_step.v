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
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zmod9 y%Zmod9) : Zmod9_scope.
Notation "x * y" := (mul x%int y%int) : int_scope.
Notation "x * y" := (mulp x%Zmod9 y%Zmod9) : Zmod9_scope.
Notation not A := (A -> Empty). 
Notation "m ^ 2" := (m * m)%int (at level 2) : int_scope.
Notation "m ^ 2" := (m * m)%Zmod9 (at level 2) : Zmod9_scope.
Notation "m ^ 3" := (m * m * m)%int (at level 2) : int_scope.
Notation "m ^ 3" := (m * m * m)%Zmod9 (at level 2) : Zmod9_scope.
Notation "m % 3" := (mod3 m)%int (at level 2) : int_scope.
Notation "m % 3" := (modp3 m)%Zmod9 (at level 2) : Zmod9_scope.
Notation "x ≡ y" := (eqmodp x%int y%int)
  (format "x  ≡  y", at level 70) : int_scope.
Notation "x ≢ y" := (not (eqmodp x%int y%int))
  (format "x  ≢  y", at level 70) : int_scope.
Notation "x ≠ y" := (not (x = y)).
Notation "ℤ/9ℤ" := Zmod9.
Notation ℤ := int.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

Axiom Rzero : Rp zero zerop.
Axiom Rone : Rp one onep.
Variable Rmod3 : unop_param Rp Rp mod3 modp3.
Variable Radd : binop_param Rp Rp Rp add addp.
Variable Rmul : binop_param Rp Rp Rp mul mulp.
Variable Reqmodp01 : forall (m : int) (x : Zmod9), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmod9 x y).



Trocq Use Rp Rmul Rzero Rone Radd Rmod3 Param10_paths Reqmodp01.
Trocq Use Param01_sum Param01_Empty Param10_Empty.

Lemma flt3_step : forall (m n p : ℤ),
  m * n * p % 3 ≢ 0 -> (m^3 + n^3)%ℤ  ≠ p^3%ℤ.
Proof.
trocq=> /=.
Admitted.
