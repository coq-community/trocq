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

From mathcomp Require Import all_ssreflect.
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

Fixpoint to_nat (x : positive) : nat :=
  match x with
    | p~1 => 1 + (to_nat p + to_nat p)
    | p~0 => to_nat p + to_nat p
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
Coercion Npos : positive >-> N.

Notation "0" := N0 : N_scope.

Module N.
Local Definition succ_subdef (n : N) : positive :=
 match n with
   | N0 => 1%positive
   | Npos p => Pos.succ p
 end.
Arguments succ_subdef /.
Definition succ : N -> N := succ_subdef.

Definition add (m n : N) := match m, n with
| N0, x | x, N0 => x
| Npos p, Npos q => Pos.add p q
end.
Infix "+" := add : N_scope.
Notation "n .+1" := (succ n) : N_scope.

Lemma addpp p : (Npos p + Npos p)%N = Npos p~0.
Proof. by elim: p => //= p IHp; rewrite Pos.addpp. Defined.

Definition to_nat (n : N) : nat :=
  match n with N0 => 0 | Npos p => Pos.to_nat p end.

Fixpoint of_nat (n : nat) : N :=
  match n with O => 0 | S n => succ (of_nat n) end.

Lemma of_natD i j : of_nat (i + j) = (of_nat i + of_nat j)%N.
Proof.
elim: i j => [//|i IHi] [|j]; first by rewrite addn0.
rewrite addSn addnS /= IHi.
case: (of_nat i) => // p; case: (of_nat j) => //=.
- by rewrite /succ/= Pos.addp1.
- by move=> q; rewrite /succ/= Pos.addpS Pos.addSp.
Defined.

Local Definition of_nat_double p k :
  of_nat k = Npos p -> of_nat (k + k) = Npos p~0.
Proof. by move=> kp; rewrite of_natD kp addpp. Defined.

Lemma to_natK (n : N) : of_nat (to_nat n) = n.
Proof. by case: n => //= ; elim=> //= p /of_nat_double/= ->. Defined.

Lemma of_natK (n : nat) : to_nat (of_nat n) = n.
Proof.
elim: n => //= n IHn; rewrite -[in X in _ = X]IHn.
by case: (of_nat n)=> //; elim=> //= p ->; rewrite /= addnS.
Defined.

Definition of_nat_iso := Iso.Build of_natK to_natK.
End N.
Infix "+" := N.add : N_scope.
Notation "n .+1" := (N.succ n) : N_scope.