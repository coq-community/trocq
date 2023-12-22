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

From mathcomp Require Import all_ssreflect.
From Trocq Require Import Trocq.

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

Lemma addpp x : x + x = x~0. Proof. by elim: x => //= ? ->. Qed.
Lemma addp1 x : x + 1 = x.+1. Proof. by elim: x. Qed.
Lemma addpS x y : x + y.+1 = (x + y).+1.
Proof. by elim: x y => // p IHp [q|q|]//=; rewrite ?IHp ?addp1//. Qed.
Lemma addSp x y : x.+1 + y = (x + y).+1.
Proof. by elim: x y => [p IHp|p IHp|]// [q|q|]//=; rewrite ?IHp//. Qed.

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

Definition RN@{} := sym_rel@{Set} (graph Ncomap).

Lemma Naddpp p : (Npos p + Npos p)%N = Npos p~0.
Proof. by elim: p => //= p IHp; rewrite Pos.addpp. Qed.

Lemma NcomapD i j : Ncomap (i + j) = (Ncomap i + Ncomap j)%N.
Proof.
elim: i j => [|i IHi] [|j]//; first by rewrite addn0.
rewrite addnS addSn /= IHi.
case: (Ncomap i) => // p; case: (Ncomap j) => //=.
  by rewrite Pos.addp1.
by move=> q; rewrite Pos.addpS Pos.addSp.
Qed.

Let NcomapNpos p k : Ncomap k = Npos p -> Ncomap (k + k) = Npos p~0.
Proof. by move=> kp; rewrite NcomapD kp Naddpp. Qed.

Lemma NmapK (n : N) : Ncomap (Nmap n) = n.
Proof. by case: n => //= ; elim=> //= p /NcomapNpos/= ->. Qed.

(* the best we can do to link these types is (4,4), but
we only need (2a,3) which is morally that Nmap is a split injection *)
Definition RN2a3 : Param2a4.Rel@{Set} N nat := SplitSurj.toParamSym {|
   SplitSurj.retract := Ncomap;
   SplitSurj.section := Nmap;
   SplitSurj.sectionK := NmapK |}.

(* for brevity, we create witnesses at lower classes by forgetting fields in RN2a3 *)
(* this behaviour can be automated so as to only declare Rn2a3 and get for free all the instances
   reachable by forgetting fields *)
(* in the general case, if a field requires an axiom, it is better to manually recreate instances
   that do not need this field, so that it is not imported before forgetting, and the lower
   instances can be declared without the axiom *)

Definition RN02b : Param02b.Rel N nat := RN2a3.
Definition RN02a : Param02a.Rel N nat := RN2a3.
Definition RN2a0 : Param2a0.Rel N nat := RN2a3.

(* as 0 and Nsucc appear in the goal, we need to link them with nat constructors *)
(* NB: as these are not type formers, only class (0,0) is required, so these proofs amount to what
   would be done in the context of raw parametricity *)

Definition RN0 : RN N0 0. Proof. done. Qed.
Definition RNS : forall m n, RN m n -> RN (Nsucc m) (S n).
Proof. by move=> _ + <-; case=> //=. Qed.

Trocq Use RN02b.
Trocq Use RN02a.
Trocq Use RN2a0.
Trocq Use RN0.
Trocq Use RNS.

Lemma N_Srec : forall (P : N -> Type), P N0 ->
 (forall n, P n -> P (Nsucc n)) -> forall n, P n.
Proof.
  trocq.
  (* the output sort of P' is (1,1) because of the covariant and contravariant occurrences of P in
     the input goal; this annotation was made to be definitionally equal to Type: from there,
     the induction principle of nat can be applied directly *)
  exact nat_rect.
Defined.

Print N_Srec.
Print Assumptions N_Srec.
