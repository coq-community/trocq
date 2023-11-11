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
From Trocq Require Import Trocq.

Set Universe Polymorphism.

Axiom cheat : forall A, A.
Ltac cheat := apply cheat.

(* what it can do *)
(* Section Test. *)
Declare Scope int_scope.
Delimit Scope int_scope with int.
Declare Scope Zp_scope.
Delimit Scope Zp_scope with Zp.

Axiom (int@{i} : Type@{i}) (zero : int) (add : int -> int -> int).
Axiom (eqmodp : int -> int -> Type).
Axiom (Zp : Type) (zerop : Zp) (addp : Zp -> Zp -> Zp).

Context (eqp_refl : Reflexive eqmodp).
Context (eqp_sym : Symmetric eqmodp).
Context (eqp_trans : Transitive eqmodp).
(* Existing Instance eqp_refl. *)
(* Existing Instance eqp_trans. *)

Context (pmap : Zp -> int) (pcomap : int -> Zp)
  (pmapK : forall x, pcomap (pmap x) = x).
Definition Rp x n := pmap x = n.

Lemma pcomapP :forall (a : int) (b : Zp), sym_rel Rp a b -> pcomap a = b.
Proof. by move=> a b <-; exact: pmapK. Qed.

Definition Rp42b@{i} : Param42b.Rel Zp@{i} int@{i} := Param42b.BuildRel Zp int Rp
   (Map4.BuildHas pmap (fun _ _ => id) (fun _ _ => id) (fun _ _ _ => idpath))
   (Map2b.BuildHas _ _ (sym_rel Rp) pcomap pcomapP).

Definition Rp00 : Param00.Rel Zp int := Rp42b.
Definition Rp01 : Param01.Rel Zp int := Rp42b.
Definition Rp40 : Param40.Rel Zp int := Rp42b.
Definition Rp10 : Param10.Rel Zp int := Rp42b.
Definition Rp02b : Param02b.Rel Zp int := Rp42b.
Definition Rp2b0 : Param2b0.Rel Zp int := Rp42b.
Definition Rp2a0 : Param2a0.Rel Zp int := Rp42b.

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') := 
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

Variable addp_to_add : binop_param Rp Rp Rp addp add.
Variable paths_to_eqmodp : binop_param Rp Rp iff paths eqmodp.

Notation "x == y" := (eqmodp x%int y%int)
  (format "x  ==  y", at level 70) : int_scope.
Notation "x + y" := (add x%int y%int) : int_scope.
Notation "x + y" := (addp x%Zp y%Zp) : Zp_scope.

Definition Radd : forall x x' (xR : Rp x x') y y' (yR : Rp y y'), Rp (x + y)%Zp (x' + y')%int.
Proof. apply addp_to_add. Qed.

Check Param01_paths.

Trocq Use Rp42b.
Trocq Use Rp40.
Trocq Use Rp00.
Trocq Use Rp01.
Trocq Use Rp10.
Trocq Use Rp02b.
Trocq Use Rp2b0.
Trocq Use Rp2a0.

Trocq Use Param01_paths.
Trocq Use Param10_paths.
Trocq Use Radd.

Axiom u : Univalence.
Axiom f : Funext.

Trocq Register Univalence u.
Trocq Register Funext f.

Goal (forall x y, x + y = y + x)%Zp.
Proof.
  trocq.
Abort.

Goal (forall x y, x + y = y + x)%int ->
  (forall x y z, x + y + z = y + x + z)%Zp.
Proof.
  intros addC x y z.
  suff addpC: forall x y, (x + y = y + x)%Zp. {
    by rewrite (addpC x y). }
  trocq.
  exact addC.
Qed.
