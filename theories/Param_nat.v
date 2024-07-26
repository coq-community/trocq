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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive natR : nat -> nat -> Type :=
  | OR : natR O O
  | SR : forall (n n' : nat), natR n n' -> natR (S n) (S n').

Lemma natR_irrelevant m n (nR nR' : natR m n) : nR = nR'.
Proof.
have @phi k l (r : natR k l) : eqn k l.
  elim: r => {k l}; first by reflexivity.
  move=> k l r e; exact: e.
have @psi k l (e : eqn k l) : natR k l.
  elim: k l e  => [| k ihk] l e.
  - case: l e => [| l] // _; exact OR.
  - case: l e => [| l] // e. 
    exact: SR (ihk _ e). 
have phiK k l r : psi k l (phi k l r) = r.
  elim: r => {k l} // k l r e /=.
  by rewrite [X in SR _ _ X]e. 
rewrite -[LHS]phiK -[RHS]phiK.
suff -> : phi _ _ nR = phi _ _ nR' by [].
apply: eq_irrelevance. 
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
