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

From mathcomp Require Import ssreflect ssrfun ssrnat.
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive natR : nat -> nat -> Type :=
  | OR : natR O O
  | SR : forall (n n' : nat), natR n n' -> natR (S n) (S n').

Lemma ind (T : Type) (X : T -> Type) t (P : X t -> Type) :
  (forall t' (e : t' = t) (x : X t'), P (transport X e x)) ->
  forall (x : X t), P x.
Proof. by move=> + x => /(_ t erefl); apply. Defined.

Lemma eq_to_refl (T : Type) (x : T) (p : x = x) : unkeyed p = erefl.
Proof. exact: Prop_irrelevance. Qed.

Lemma natR_irrelevant m n : forall (nR nR' : natR m n), nR = nR'.
Proof.
suff: forall (nR : natR m n) m' n'  (nR' : natR m' n') (e : m = m') (e' : n = n') ,
     transport (fun m' => natR m' n') e (transport (fun n' => natR m n') e' nR) = nR'.
    by move=> /(_ _ m n _ erefl erefl); apply.
elim => // [|{}m {}n nR IHnR] m' n' => - [|{}m' {}n' nR'] // e e'.
  by rewrite ?eq_to_refl.
rewrite -[nR']IHnR//; do ?by [case: e|case: e'].
move=> e'' e'''.
by case: _ / e'' in e *; case: _ / e''' in e' *; rewrite ?eq_to_refl.
Qed.

Definition map_nat : nat -> nat := id.

Definition map_in_R_nat : forall {n n' : nat}, map_nat n = n' -> natR n n' :=
  fun n n' e =>
    match e with
    | idpath =>
      (fix F n :=
        match n with
        | O => OR
        | S m => SR m m (F m)
        end) n
    end.

Definition R_in_map_nat : forall {n n' : nat}, natR n n' -> map_nat n = n' :=
  fix F n n' (nR : natR n n') : map_nat n = n' :=
    match nR with
    | OR => idpath
    | SR m m' mR => ap S (F m m' mR)
    end.

Definition R_in_mapK_nat : forall {n n' : nat} (nR : natR n n'),
  map_in_R_nat (R_in_map_nat nR) = nR.
Proof. 
by move=> n n'; case: _ / => //= {}n {}n' nR; apply: natR_irrelevant.
Qed.

Definition Param_nat_sym {n n' : nat} : natR n n' -> natR n' n.
Proof.
  intro nR. induction nR as [|m m' _ IH].
  - exact OR.
  - exact (SR m' m IH).
Defined.

Definition Param_nat_sym_inv {n n' : nat} :
  forall (nR : natR n n'), Param_nat_sym (Param_nat_sym nR) = nR.
Proof. by elim => //= {}n {}n' nR ->. Defined.

Definition natR_sym : forall (n n' : nat), sym_rel natR n n' <->> natR n n'.
Proof.
  intros n n'; unshelve eexists _, _.
  - apply Param_nat_sym.
  - apply Param_nat_sym.
  - intro nR. apply Param_nat_sym_inv.
Defined.

Definition Map4_nat : Map4.Has natR.
Proof.
  unshelve econstructor.
  - exact map_nat.
  - exact @map_in_R_nat.
  - exact @R_in_map_nat.
  - exact @R_in_mapK_nat.
Defined.

Definition Param44_nat : Param44.Rel nat nat.
Proof.
  unshelve econstructor.
  - exact natR.
  - exact Map4_nat.
  - apply (fun e => @eq_Map4 _ _ (sym_rel natR) natR e Map4_nat).
    apply natR_sym.
Defined.

Definition Param00_nat : Param00.Rel nat nat := Param44_nat.
Definition Param2a0_nat : Param2a0.Rel nat nat := Param44_nat.

Definition Param_add :
  forall (n1 n1' : nat) (n1R : natR n1 n1') (n2 n2' : nat) (n2R : natR n2 n2'),
    natR (n1 + n2) (n1' + n2').
Proof.
  intros n1 n1' n1R n2 n2' n2R.
  induction n1R as [|n1 n1' n1R IHn1R].
  - simpl. exact n2R.
  - simpl. apply SR. exact IHn1R.
Defined.
