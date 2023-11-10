(**************************************************************************************************)
(*                            *                               Trocq                               *)
(*  _______                   *                      Copyright (C) 2023 MERCE                     *)
(* |__   __|                  *               (Mitsubishi Electric R&D Centre Europe)             *)
(*    | |_ __ ___   ___ __ _  *                  Cyril Cohen <cyril.cohen@inria.fr>               *)
(*    | | '__/ _ \ / __/ _` | *                  Enzo Crance <enzo.crance@inria.fr>               *)
(*    | | | | (_) | (_| (_| | *              Assia Mahboubi <assia.mahboubi@inria.fr>             *)
(*    |_|_|  \___/ \___\__, | *********************************************************************)
(*                        | | *           This file is distributed under the terms of the         *)
(*                        |_| *             GNU Lesser General Public License Version 3           *)
(*                            *            (see LICENSE file for the text of the license)         *)
(**************************************************************************************************)

From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
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

Elpi Query param lp:{{
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map4 map2b) [] {{:gref int}} {{:gref Rp42b}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map4 map0) [] {{:gref int}} {{:gref Rp40}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map0 map0) [] {{:gref int}} {{:gref Rp00}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map0 map1) [] {{:gref int}} {{:gref Rp01}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map1 map0) [] {{:gref int}} {{:gref Rp10}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map0 map2b) [] {{:gref int}} {{:gref Rp02b}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map2b map0) [] {{:gref int}} {{:gref Rp2b0}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map2a map0) [] {{:gref int}} {{:gref Rp2a0}})),
  
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref paths}} (pc map0 map1)
        [pc map0 map2b]
        {{:gref paths}} {{:gref Param01_paths}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref paths}} (pc map1 map0)
        [pc map2b map0]
        {{:gref paths}} {{:gref Param10_paths}})),

  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref addp}} (pc map0 map0) [] {{:gref add}} {{:gref Radd}})).
}}.

Axiom u : Univalence.
Axiom f : Funext.

Param Register Univalence u.
Param Register Funext f.

Goal
  (* Zp@{i}. *)
  (* Zp@{i} -> Zp@{i}. *)
  (* forall (P : Zp -> Type) (x : Zp), P x. *)
  (* forall (P : Zp -> Type) (x : Zp), P x -> P x. *)
  (* forall (P : Zp -> Zp -> Type) (x y : Zp), P x y -> P y x. *)
  (* forall (P : Zp -> Type) (x : Zp), P x -> forall (y : Zp), P y. *)
  (* forall (P : Zp -> Type) (x : Zp), P x -> forall (y : Zp), P y -> P x. *)
  (* forall (A : Type) (f : Zp -> A) (P : A -> Type) (x : Zp), P (f x). *)
  (* forall (A : Type) (f : Zp -> A) (P : A -> Type) (x : Zp) (H : forall a, P a -> Type) (J : P (f x)), H (f x) J. *)

  (forall x y, x + y = y + x)%Zp.

  (* forall (X : forall (A : Type@{i}), A -> Type@{i}) (x : Zp), Zp -> X Zp x -> Zp. *)
Proof.
  param.
Abort.

Goal (forall x y, x + y = y + x)%int ->
  (forall x y z, x + y + z = y + x + z)%Zp.
Proof.
  intros addC x y z.
  suff addpC: forall x y, (x + y = y + x)%Zp. {
    by rewrite (addpC x y). }
  param.
  exact addC.
Qed.

Inductive unit@{i} : Type@{i} := tt : unit.

Module Seq.
  Inductive t@{i} (A : Type@{i}) :=
    | snil : t A
    | scons : A -> (unit@{i} -> t A) -> t A.
  Arguments snil {_}.
  Arguments scons {_} _ _.
  
  Fixpoint all@{i} {A : Type@{i}} (P : A -> Type@{i}) (s : t A) : Type@{i} :=
    match s with
    | snil => unit@{i}
    | scons a s' => P a * all P (s' tt)
    end.

  Fixpoint sum@{i} (s : t Zp) : Zp :=
    match s with
    | snil => zerop@{i}
    | scons x s' => (x + sum (s' tt))%Zp
    end.
End Seq.

Fixpoint all@{i} {A : Type@{i}} (P : A -> Type@{i}) (l : list A) : Type@{i} :=
  match l with
  | nil => unit@{i}
  | cons a l' => P a * all P l'
  end.

Definition sum@{i} (l : list@{i} int) : int := List.fold_left@{i i} _ _ add@{i} l zero.

Inductive Rseq@{i}
  (A A' : Type@{i}) (AR : A -> A' -> Type@{i}) : Seq.t@{i} A -> list@{i} A' -> Type@{i} :=
    | Rnil : Rseq A A' AR Seq.snil nil
    | Rcons : forall a a' (aR : AR a a') s l (r : Rseq A A' AR s l),
      Rseq A A' AR (Seq.scons a (fun _ => s)) (cons a' l).

Fixpoint map_seq@{i} (A A' : Type@{i}) (AR : Param10.Rel A A') (s : Seq.t@{i} A) : list@{i} A' :=
  match s with
  | Seq.snil => nil
  | Seq.scons a s' => cons (map AR a) (map_seq A A' AR (s' tt))
  end.

Definition Param2a0_seq_list@{i} (A A' : Type@{i}) (AR : Param2a0.Rel A A') :
  Param2a0.Rel (Seq.t A) (list A').
Proof.
  unshelve econstructor.
  - exact (Rseq A A' AR).
  - apply cheat@{i}.
  - apply cheat@{i}.
Defined.

Definition Param02b_seq_list@{i} (A A' : Type@{i}) (AR : Param02b.Rel A A') :
  Param02b.Rel (Seq.t A) (list A').
Proof.
  unshelve econstructor.
  - exact (Rseq A A' AR).
  - apply cheat@{i}.
  - apply cheat@{i}.
Defined.

Definition Param44_seq_list@{i} (A A' : Type@{i}) (AR : Param44.Rel A A') :
  Param44.Rel (Seq.t A) (list A').
Proof.
  unshelve econstructor.
  - exact (Rseq A A' AR).
  - apply cheat@{i}.
  - apply cheat@{i}.
Defined.

(* Definition Param01_seq_list@{i} :
  forall (A A' : Type@{i}) (AR : Param01.Rel A A'), Param01.Rel (Seq.t A) (list A').
Proof.
  intros A A' AR.
  unshelve econstructor.
  - exact (Rseq A A' AR).
  - constructor.
  - cheat.
Defined. *)

Fixpoint Rall01@{i}
  (A A' : Type@{i}) (AR : Param00.Rel A A')
  (P : A -> Type@{i}) (P' : A' -> Type@{i})
  (PR : forall a a' (aR : AR a a'), Param01.Rel (P a) (P' a'))
  (s : Seq.t A) (l : list A') (slR : Rseq A A' AR s l) :
    Param01.Rel (Seq.all P s) (all P' l).
Proof.
  unshelve econstructor.
  - destruct slR.
    + simpl. exact (fun _ _ => unit@{i}).
    + simpl. intros (pa, ps) (pa', pl).
      exact (PR a a' aR pa pa' * Rall01 A A' AR P P' PR s l slR ps pl).
  - constructor.
  - unshelve econstructor.
    destruct slR.
    + simpl. exact (fun u => u).
    + simpl. intros (pa', pl).
      exact (comap (PR a a' aR) pa', comap (Rall01 A A' AR P P' PR s l slR) pl).
Defined.

Fixpoint Rall10@{i}
  (A A' : Type@{i}) (AR : Param00.Rel A A')
  (P : A -> Type@{i}) (P' : A' -> Type@{i})
  (PR : forall a a' (aR : AR a a'), Param10.Rel (P a) (P' a'))
  (s : Seq.t A) (l : list A') (slR : Rseq A A' AR s l) :
    Param10.Rel (Seq.all P s) (all P' l).
Proof.
  unshelve econstructor.
  - destruct slR.
    + simpl. exact (fun _ _ => unit@{i}).
    + simpl. intros (pa, ps) (pa', pl).
      exact (PR a a' aR pa pa' * Rall10 A A' AR P P' PR s l slR ps pl).
  - unshelve econstructor.
    destruct slR.
    + simpl. exact (fun u => u).
    + simpl. intros (pa, ps).
      exact (map (PR a a' aR) pa, map (Rall10 A A' AR P P' PR s l slR) ps).
  - constructor.
Defined.

Definition Rsum :
  forall (s : Seq.t Zp) (l : list int) (slR : Rseq Zp int Rp00 s l),
    Rp00 (Seq.sum s) (sum l).
Admitted.

Axiom Rzero : Rp zerop zero.

Definition Rp02a : Param02a.Rel Zp int.
Proof.
  unshelve econstructor.
  - exact Rp.
  - constructor.
  - cheat.
Defined.

Elpi Query param lp:{{
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Zp}} (pc map0 map2a) [] {{:gref int}} {{:gref Rp02a}})),

  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref Seq.t}} (pc map2a map0)
        [pc map2a map0]
        {{:gref list}} {{:gref Param2a0_seq_list}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref Seq.t}} (pc map4 map4)
        [pc map4 map4]
        {{:gref list}} {{:gref Param44_seq_list}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref Seq.t}} (pc map0 map2b)
        [pc map0 map2b]
        {{:gref list}} {{:gref Param02b_seq_list}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref Seq.all}} (pc map0 map1)
        [pc map0 map0, pc map0 map1]
        {{:gref all}} {{:gref Rall01}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref Seq.all}} (pc map1 map0)
        [pc map0 map0, pc map1 map0]
        {{:gref all}} {{:gref Rall10}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref Seq.snil}} (pc map0 map0)
        [pc map0 map0]
        {{:gref nil}} {{:gref Rnil}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref zerop}} (pc map0 map0) [] {{:gref zero}} {{:gref Rzero}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref Seq.sum}} (pc map0 map0) [] {{:gref sum}} {{:gref Rsum}})).
}}.

Goal
  (* forall (s : Seq.t Zp), s = s. *)
  (* Seq.all (fun x : Zp => Zp) Seq.snil. *)
  (* forall (s : Seq.t Zp), Seq.all (fun x : Zp => Zp) s. *)
  (* forall (P : Zp -> Type), Seq.all P Seq.snil. *)
  (* forall (P : Zp -> Type) (s : Seq.t Zp), Seq.all P s. *)
  forall (F : (Type@{i} -> Type@{i}) -> Type@{i}), F Seq.t.
  (* forall (P : Zp -> Type) (s : Seq.t Zp),
    (forall x, P x -> x = zerop) -> Seq.all P s -> Seq.sum s = zerop. *)
Proof.
  param.
Abort.
