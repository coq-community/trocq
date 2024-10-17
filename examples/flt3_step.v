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
Declare Scope Zmod9_scope.
Delimit Scope Zmod9_scope with Zmod9.
Local Open Scope Zmod9_scope.

(* Helper predicates *)
Definition unop_param {X X'} RX {Y Y'} RY
   (f : X -> Y) (g : X' -> Y') :=
  forall x x', RX x x' -> RY (f x) (g x').

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(* For now translations need the support of monomorphic identifiers: *)

(* Arithmetic on Z_9*)
Definition Zmod9 := 'Z_9.
Definition zerop : Zmod9 := Zp0.
Definition addp : Zmod9 -> Zmod9 -> Zmod9 := @Zp_add 8.
Definition mulp : Zmod9 -> Zmod9 -> Zmod9 := @Zp_mul 8.
Definition onep : Zmod9 := Zp1.

(* Quotient *)
Definition modp : int -> Zmod9 := fun x => (x)%:~R.
Definition reprp : Zmod9 -> int := idmap.

Lemma reprpK : forall x, modp (reprp x) = x. Proof. exact: natr_Zp. Qed.

(* Mod 3 in Z9 *)
Lemma mk_mod9_mod3 (n : 'I_9) : (n %% 3 < 9)%N.
Proof. apply: (@ltn_trans 3) => //; exact: ltn_pmod. Qed.

Definition modp3 : Zmod9 -> Zmod9 := fun n => Ordinal (mk_mod9_mod3 n).

(* Equality on integers *)
Definition eqmodp (x y : int) := modp x = modp y.

Definition eq_Zmod9 (x y : Zmod9) := (x = y).
Arguments eq_Zmod9 /.

(* Definition mod3 : int -> int := TODO *)
Definition mod3 : int -> int := (fun x => x %% 3).

Definition zero : int := 0.
Definition one : int := 1.

Definition add : int -> int -> int := fun x y => x + y.
Definition mul : int -> int -> int := fun x y => x * y.

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
Notation "m ³" := (m * m * m)%int (at level 2) : int_scope.
Notation "m ³" := (m * m * m)%Zmod9 (at level 2) : Zmod9_scope.
Notation "m % 3" := (mod3 m)%int (at level 2) : int_scope.
Notation "m % 3" := (modp3 m)%Zmod9 (at level 2) : Zmod9_scope.
Notation "x ≡ y" := (eqmodp x%int y%int)
  (format "x  ≡  y", at level 70) : int_scope.
Notation "x ≢ y" := (not (eqmodp x%int y%int))
  (format "x  ≢  y", at level 70) : int_scope.
Notation "x ≠ y" := (not (x = y)) (at level 70).
Notation "ℤ/9ℤ" := Zmod9.
Notation ℤ := int.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprpK).

Lemma Rzero : Rp zero zerop. Proof. done. Qed.

Lemma Rone : Rp one onep. Proof. done. Qed.


(* These lemmas are about congruence mod 9, of + and * *)
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

(* This lemma says that mod-ing by 3 is the same as first mod-ing by 9 and then
   mod-ing by 3. Can probably be streamlined... *)
Lemma Rmod3 : unop_param Rp Rp mod3 modp3.
Proof.
rewrite /Rp /= /graph /= => x y <- {y}.
rewrite /modp /mod3 /modp3.
apply: val_inj=> /=.
wlog : x / exists n, x = Posz n.
  move=> hwlog.
  case: x => n.
  - by apply: hwlog; exists n.
  - rewrite modNz_nat //.
    rewrite -[Posz (1 +  _)%N - 1]/(2%int) -[(1 + _)%N]/(3%N) NegzE rmorphN /=.
    rewrite -[_.+2]/(9%N) modn_dvdm //.
    rewrite modnB //=; last by rewrite [_%:~R]Zp_nat ltnW.
    set x : 'I_9 := _.+1%:~R.
    rewrite -[(9 %% 3)%N]/(0%N) addn0.
    have {x} -> : x = (n.+1 %% 9)%N :> nat by rewrite {}/x [_%:~R]Zp_nat //.
    rewrite modn_dvdm // modnS; case: ifP => //= hn.
    - by rewrite mul0n subn0 -[n]/(n.+1.-1) modn_pred // hn.
    - rewrite -[n]/(n.+1.-1) modn_pred // hn mul1n subSS subzn; last first.
        by apply: (@leq_trans (n.+1 %% 3)); rewrite ?leq_pred // -ltnS ltn_pmod.
      rewrite [_%:~R]Zp_nat [LHS]modn_small //=.
      by apply: (@leq_trans 3) => //; rewrite ltnS leq_subr.
case=> n -> {x}.
set u : 'I_9 := _%:~R; set v := (X in (X %% 3)%N).
have {v} -> : v = (n %% 9)%N by exact: val_Zp_nat.
rewrite modn_dvdm //.
have -> : nat_of_ord u = ((n %% 3)%N %% 9)%N.
  by rewrite {}/u modz_nat /= (@val_Zp_nat 9).
rewrite modn_small //; apply: (@ltn_trans 3) => //; exact: ltn_pmod.
Qed.

Lemma Reqmodp01 : forall (m : int) (x : Zmod9), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmod9 x y).
Proof.
rewrite /Rp /= /graph /=.
move=> x k exk y l eyl.
apply: (@Param01.BuildRel (x ≡ y) (k = l) (fun _ _ => unit)) => //.
by constructor; rewrite -exk -eyl.
Qed.

Trocq Use Rp Rmul Rzero Rone Radd Rmod3 Param10_paths Reqmodp01.
Trocq Use Param01_sum.
Trocq Use Param01_Empty.
Trocq Use Param10_Empty.

Lemma flt3_step : forall (m n p : ℤ),
  ((m * n * p)%Z % 3)%Z ≢ 0 -> (m³ + n³)%ℤ  ≠ p³%ℤ.
Proof.
trocq=> /=.

(* the following should be a call to troq to compute *)
move=> + + + /eqP + /eqP.
by do 3![case; do 9?[case=> //=] => ?].
Qed.
Print Assumptions flt3_step.
