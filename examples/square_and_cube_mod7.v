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
From mathcomp Require Import all_ssreflect all_algebra.
From Trocq Require Import Trocq.

Import GRing.Theory.
Open Scope ring_scope.

Set Universe Polymorphism.

Declare Scope int_scope.
Delimit Scope int_scope with int.
Delimit Scope int_scope with ℤ.
Local Open Scope int_scope.
Declare Scope Zmod7_scope.
Delimit Scope Zmod7_scope with Zmod7.
Local Open Scope Zmod7_scope.

(* Helper predicates *)
Definition unop_param {X X'} RX {Y Y'} RY
   (f : X -> Y) (g : X' -> Y') :=
  forall x x', RX x x' -> RY (f x) (g x').

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(* For now translations need the support of monomorphic identifiers: *)

(* Arithmetic on Z_7*)
Definition Zmod7 := 'Z_7.
Notation "ℤ/7ℤ" := Zmod7.

Definition zerop : ℤ/7ℤ := @Zp0 6.
Definition addp : ℤ/7ℤ -> ℤ/7ℤ -> ℤ/7ℤ := @Zp_add 6.
Definition mulp : ℤ/7ℤ -> ℤ/7ℤ -> ℤ/7ℤ := @Zp_mul 6.
Definition onep : ℤ/7ℤ := Zp1.

(* Quotient *)
Definition modp : int -> ℤ/7ℤ := fun x => (x)%:~R.
Definition reprp : ℤ/7ℤ -> int := idmap.

Lemma reprpK : forall x, modp (reprp x) = x. Proof. exact: natr_Zp. Qed.

(* Mod 3 in Z7 *)
Lemma mk_mod7_mod3 (n : 'I_7) : (n %% 3 < 7)%N.
Proof. apply: (@ltn_trans 3) => //; exact: ltn_pmod. Qed.

Definition modp3 : ℤ/7ℤ -> ℤ/7ℤ := fun n => Ordinal (mk_mod7_mod3 n).

(* Equality on integers *)
Definition eqmodp (x y : int) := modp x = modp y.

Definition eq_Zmod7 (x y : ℤ/7ℤ) := (x = y).
Arguments eq_Zmod7 /.

Definition zero : int := 0.
Definition one : int := 1.

Definition add : int -> int -> int := fun x y => x + y.
Definition mul : int -> int -> int := fun x y => x * y.

Notation "0" := zero : int_scope.
Notation "0" := zerop : Zmod7_scope.
Notation "1" := one : int_scope.
Notation "1" := onep : Zmod7_scope.
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zmod7 y%Zmod7) : Zmod7_scope.
Notation "x * y" := (mul x%int y%int) : int_scope.
Notation "x * y" := (mulp x%Zmod7 y%Zmod7) : Zmod7_scope.
Notation not A := (A -> Empty).
Notation "m ²" := (m * m)%int (at level 2) : int_scope.
Notation "m ²" := (m * m)%Zmod7 (at level 2) : Zmod7_scope.
Notation "m ³" := (m * m * m)%int (at level 2) : int_scope.
Notation "m ³" := (m * m * m)%Zmod7 (at level 2) : Zmod7_scope.
Notation "m % 3" := (modp3 m)%Zmod7 (at level 2) : Zmod7_scope.
Notation "x ≡ y" := (eqmodp x%int y%int)
  (format "x  ≡  y", at level 70) : int_scope.
Notation "x ≢ y" := (not (eqmodp x%int y%int))
  (format "x  ≢  y", at level 70) : int_scope.
Notation "x ≠ y" := (not (x = y)) (at level 70).
Notation "A ∨ B" := ((not A) -> B) (at level 85) : type_scope.
Notation ℤ := int.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

Lemma Rzero : Rp zero zerop. Proof. done. Qed.

Lemma Rone : Rp one onep. Proof. done. Qed.


(* These lemmas are about congruence mod 7, of + and * *)
Lemma Radd : binop_param Rp Rp Rp add addp.
Proof.
rewrite /Rp /= /graph /==> x1 y1 <- x2 y2 <-.
by rewrite /modp rmorphE.
Qed.

Lemma Rmul : binop_param Rp Rp Rp mul mulp.
Proof.
rewrite /Rp /= /graph /= => x1 y1 <- x2 y2 <-.
by rewrite /modp rmorphM.
Qed.

Lemma Reqmodp01 : forall (m : int) (x : ℤ/7ℤ), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmod7 x y).
Proof.
rewrite /Rp /= /graph /=.
move=> x k exk y l eyl.
apply: (@Param01.BuildRel (x ≡ y) (k = l) (fun _ _ => unit)) => //.
by constructor; rewrite -exk -eyl.
Qed.

Trocq Use Rp Rmul Rzero Rone Radd Param10_paths Reqmodp01.
Trocq Use Param01_Empty.
Trocq Use Param10_Empty.

Lemma square_and_cube_mod7 : forall (m n p : ℤ),
  (m = n²)%Z -> (m = p³)%Z -> m ≡ 0 ∨ m ≡ 1.
Proof.
trocq => /=.

(* the following should be a call to troq to compute *)
move=> m n p /eqP mn /eqP mp /eqP m0. apply/eqP; move: m n p mn mp m0.
do 3![case; do 7?[case=> //=] => ?] => /=.

(* Ultimately, it should be:

by rewrite (mod 7); decide.

*)
Qed.
Print Assumptions square_and_cube_mod7.
