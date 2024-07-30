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

From mathcomp Require Import all_ssreflect all_algebra.
From Trocq Require Import Trocq.
Import GRing.Theory.
Local Open Scope bool_scope.

Set Universe Polymorphism.

Lemma Zp_int_mod [p : nat] : 1 < p ->
   forall n : int, ((n %% p)%Z%:~R)%R = (n%:~R)%R :> 'Z_p.
Proof.
move=> p_gt1 n; rewrite [in RHS](divz_eq n p) [in RHS]intrD intrM.
by rewrite [p%:~R%R]char_Zp// mulr0 add0r.
Qed.

Lemma val_Zp_int p : 1 < p ->
  forall n : int, ((n%:~R)%R : 'Z_p)%:Z%R = (n %% p)%Z.
Proof.
move=> p_gt1 n; rewrite -Zp_int_mod//.
have: ((n %% p)%Z >= 0)%R by rewrite modz_ge0//; case: p p_gt1.
rewrite -[RHS]modz_mod; case: (n %% p)%Z => //= k _ /=.
by rewrite val_Zp_nat// modz_nat.
Qed.

Section modp.
Variable (p : nat) (p_gt1 : p > 1).
Let p_gt0 : p > 0. by case: p p_gt1. Qed.

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(***
We setup an axiomatic context in order not to develop
arithmetic modulo in Coq/HoTT.
**)
Definition eqmodp (x y : int) := (x = y %[mod p])%Z.

(* for now translations need the support of a global reference: *)
Definition eq_Zmodp (x y : 'Z_p) := (x = y).

Lemma eq_intZp (m n : int) : (m%:~R == n%:~R :> 'Z_p)%R = (m == n %[mod p])%Z.
Proof.
apply/eqP/eqP.
  by move=> /(congr1 val)/(congr1 Posz); rewrite !val_Zp_int.
by move=> /(congr1 (fun n => n%:~R : 'Z_p)%R); rewrite !Zp_int_mod.
Qed.

Lemma eq_natZp (m n : nat) : (m%:R == n%:R :> 'Z_p)%R = (m == n %[mod p]).
Proof. by rewrite (eq_intZp m n) !modz_nat. Qed.
Locate "==".

Lemma intZp_eq0 (n : int) : (n%:~R == 0 :> 'Z_p)%R = (p %| n)%Z.
Proof. by rewrite -[0%R]/(0%:~R)%R eq_intZp mod0z; apply/eqP/dvdz_mod0P.  Qed.

Lemma natZp_eq0 (n : nat) : (n%:R == 0 :> 'Z_p)%R = (p %| n).
Proof. by rewrite -[0%R]/(0%:R)%R eq_natZp mod0n. Qed.

Search (_ %% _)%N ('I__).
Search GRing.natmul nat_of_ord.

Arguments eq_Zmodp /.

Definition Zp := 'Z_p.
Arguments Zp /.

Lemma reprK : cancel (val : Zp -> int) (intmul 1 : int -> Zp).
Proof. exact: natr_Zp. Qed.

Definition Rp := SplitSurj.toParam (SplitSurj.Build reprK).
Lemma Rzero : Rp 0%R 0%R. Proof. done. Qed.

Arguments graph /.


Definition int_add (x y : int) : int := (x + y)%R.
Definition int_mul (x y : int) : int := (x * y)%R.

Definition Zp_add (x y : Zp) : 'Z_p := (x + y)%R.
Definition Zp_mul (x y : Zp) : 'Z_p := (x * y)%R.

Lemma Radd : binop_param Rp Rp Rp (int_add) (Zp_add).
Proof. by move=> /= m _ <- n _ <- /=; rewrite rmorphD. Qed.

Lemma Rmul : binop_param Rp Rp Rp (int_mul) (Zp_mul).
Proof. by move=> /= m _ <- n _ <- /=; rewrite rmorphM. Qed.

Definition Reqmodp01 : forall (m : int) (x : 'Z_p), Rp m x ->
  forall n y, Rp n y -> Param01.Rel (eqmodp m n) (eq_Zmodp x y).
Proof.
move=> /= m _ <- n _ <-; exists (fun _ _ => True) => //=.
by split=> /eqP; rewrite eq_intZp => /eqP.
Qed.

Lemma RTrue : Param01.Rel True True.
Admitted.
Lemma Runit : Param01.Rel unit unit.
Admitted.
Trocq Use Rp Rmul Rzero Param10_paths Reqmodp01 RTrue Runit.

Local Open Scope ring_scope.

Lemma IntRedModZp : 
 (forall (m n : 'Z_p), m = n * n -> m = n) ->
 forall (m n : int),  m = int_mul n n -> eqmodp m n.
Proof.
move=> Hyp.
trocq; simpl.
exact: Hyp.
Qed.

(* Print Assumptions IntRedModZp. (* No Univalence *) *)

End modp.
