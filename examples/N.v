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
From HoTT Require Import HoTT.
From Trocq Require Import Common.

Set Universe Polymorphism.

(* definition of binary natural numbers *)

Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Declare Scope positive_scope.
Delimit Scope positive_scope with positive.
Bind Scope positive_scope with positive.

Notation "1" := xH : positive_scope.
Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Module Pos.
Local Open Scope positive_scope.
Fixpoint succ x :=
  match x with
    | p~1 => (succ p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

Fixpoint map (x : positive) : nat :=
  match x with
    | p~1 => 1 + (map p + map p)
    | p~0 => map p + map p
    | 1 => 1
  end.

Fixpoint add (x y : positive) : positive :=
  match x, y with
  | 1, p | p, 1 => succ p
  | p~0, q~0 => (add p q)~0
  | p~0, q~1 | p~1, q~0 => (add p q)~1
  | p~1, q~1 => succ (add p q)~1
  end.
Infix "+" := add : positive_scope.
Notation "p .+1" := (succ p) : positive_scope.

Lemma addpp x : x + x = x~0. Proof. by elim: x => //= ? ->. Defined.
Lemma addp1 x : x + 1 = x.+1. Proof. by elim: x. Defined.
Lemma addpS x y : x + y.+1 = (x + y).+1.
Proof. by elim: x y => // p IHp [q|q|]//=; rewrite ?IHp ?addp1//. Defined.
Lemma addSp x y : x.+1 + y = (x + y).+1.
Proof. by elim: x y => [p IHp|p IHp|]// [q|q|]//=; rewrite ?IHp//. Defined.

End Pos.
Infix "+" := Pos.add : positive_scope.
Notation "p .+1" := (Pos.succ p) : positive_scope.

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.

Declare Scope N_scope.
Delimit Scope N_scope with N.
Bind Scope N_scope with N.

Notation "0" := N0 : N_scope.

Definition succ_pos (n : N) : positive :=
 match n with
   | N0 => 1%positive
   | Npos p => Pos.succ p
 end.

Definition Nsucc (n : N) := Npos (succ_pos n).

Definition Nadd (m n : N) := match m, n with
| N0, x | x, N0 => x
| Npos p, Npos q => Npos (Pos.add p q)
end.
Infix "+" := Nadd : N_scope.
Notation "n .+1" := (Nsucc n) : N_scope.

(* various possible proofs to fill the fields of a parametricity witness between N and nat *)

Definition Nmap (n : N) : nat :=
  match n with
  | N0 => 0
  | Npos p => Pos.map p
  end.

Fixpoint Ncomap (n : nat) : N :=
  match n with O => 0 | S n => Nsucc (Ncomap n) end.

Lemma Naddpp p : (Npos p + Npos p)%N = Npos p~0.
Proof. by elim: p => //= p IHp; rewrite Pos.addpp. Defined.

Lemma NcomapD i j : Ncomap (i + j) = (Ncomap i + Ncomap j)%N.
Proof.
elim: i j => [|i IHi] [|j]//=; first by rewrite -nat_add_n_O//.
rewrite -nat_add_n_Sm/= IHi.
case: (Ncomap i) => // p; case: (Ncomap j) => //=.
- by rewrite /Nsucc/= Pos.addp1.
- by move=> q; rewrite /Nsucc/= Pos.addpS Pos.addSp.
Defined.

Let NcomapNpos p k : Ncomap k = Npos p -> Ncomap (k + k) = Npos p~0.
Proof. by move=> kp; rewrite NcomapD kp Naddpp. Defined.

Lemma NmapK (n : N) : Ncomap (Nmap n) = n.
Proof. by case: n => //= ; elim=> //= p /NcomapNpos/= ->. Defined.

Lemma NcomapK (n : nat) : Nmap (Ncomap n) = n.
Proof.
elim: n => //= n IHn; rewrite -[in X in _ = X]IHn.
by case: (Ncomap n)=> //; elim=> //= p ->; rewrite /= !add_n_Sm.
Defined.

Definition Niso := Iso.Build NcomapK NmapK.