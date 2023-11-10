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

(* first, we axiomatise non negative reals *)

Axiom (nnreal : Type).
Declare Scope nnreal_scope.
Delimit Scope nnreal_scope with nnreal.
Bind Scope nnreal_scope with nnreal.

Axiom (nnreal_zero : nnreal).
Axiom (nnreal_add : nnreal -> nnreal -> nnreal).
Notation "x + y" := (nnreal_add x%nnreal y%nnreal) : nnreal_scope.

(* the extension is just defined as adding a constructor for infinite reals *)

Inductive xnnreal : Type :=
  | Fin : nnreal -> xnnreal
  | Inf : xnnreal.

Declare Scope xnnreal_scope.
Delimit Scope xnnreal_scope with xnnreal.
Bind Scope xnnreal_scope with xnnreal.

Definition xnnreal_add (re1 re2 : xnnreal) : xnnreal :=
  match re1, re2 with
  | Fin r1, Fin r2 => Fin (r1 + r2)%nnreal
  | _, _ => Inf
  end.
Notation "x + y" := (xnnreal_add x%xnnreal y%xnnreal) : xnnreal_scope.

Definition xnnreal_seq := nat -> xnnreal.
Identity Coercion xnnreal_seq_id : xnnreal_seq >-> Funclass.
Declare Scope xnnreal_seq_scope.
Delimit Scope xnnreal_seq_scope with xnnreal_seq.
Bind Scope xnnreal_seq_scope with xnnreal_seq.

Definition add_xnnreal_seq (u v : xnnreal_seq) : xnnreal_seq :=
  fun n => (u n + v n)%xnnreal.
Infix "+" := add_xnnreal_seq : xnnreal_seq_scope.

Definition nnreal_seq := nat -> nnreal.
Identity Coercion nnreal_seq_id : nnreal_seq >-> Funclass.

(* here we axiomatise the sequence sum and the distributivity lemma *)
(* TODO: expliquer pourquoi? *)

Axiom (xnnreal_sum : xnnreal_seq -> xnnreal).
Notation "'Σ' ue" := (xnnreal_sum ue) (at level 35) : xnnreal_scope.

Axiom xnnreal_sumD :
  forall u v : xnnreal_seq, (Σ (u + v))%xnnreal = (Σ u + Σ v)%xnnreal.

(* the explicit cast functions between both types are a trivial extension and a truncation
   yielding a default value in the case of infinity *)

Definition extend (r : nnreal) : xnnreal := Fin r.

Definition truncate (re : xnnreal) : nnreal :=
  match re with
  | Inf => nnreal_zero
  | Fin r => r
  end.

Definition is_finite (re : xnnreal) : Bool :=
  match re with Inf => false | Fin _ => true end.

Definition cv_sum (u : nnreal_seq) := is_finite
  (Σ (Fin o u))%xnnreal.

(* TODO: expliquer cet encodage? *)

Record nnreal_cv_seq := {
   cv_to_nnreal_seq :> nnreal_seq;
   nnreal_cv_seq_finite_sum : cv_sum cv_to_nnreal_seq = true
}.
Declare Scope nnreal_cv_seq_scope.
Delimit Scope nnreal_cv_seq_scope with nnreal_cv_seq.
Bind Scope nnreal_cv_seq_scope with nnreal_cv_seq.

Axiom add_nnreal_seq_cv :
  forall u v : nnreal_cv_seq, cv_sum (fun n => u n + v n)%nnreal = true.

Definition add_nnreal_cv_seq (u v : nnreal_cv_seq) :=
  Build_nnreal_cv_seq _ (add_nnreal_seq_cv u v).
Infix "+" := add_nnreal_cv_seq : nnreal_cv_seq_scope.

Definition nnreal_sum (u : nnreal_cv_seq) : nnreal :=
  truncate (xnnreal_sum (Fin o u)).
Notation "'Σ' u" := (nnreal_sum u) (at level 35) : nnreal_scope.

(* various proofs to be used as fields of the parametricity witness *)

Definition R_nnreal (r : nnreal) (re : xnnreal) : Type := extend r = re.

Definition truncate_extend : forall (r : nnreal), truncate (extend r) = r.
Proof. reflexivity. Defined.

(* in this way, the composition is an identity only conditionally *)
(* this is why truncate_in_R_nnreal is not provable and the maximum provable class is (4,2b) *)
Definition extend_truncate :
  forall (re : xnnreal), is_finite re = true -> extend (truncate re) = re.
Proof. by case => //=; discriminate. Defined.

Definition extend_in_R_nnreal (r : nnreal) (re : xnnreal) (e : extend r = re) : R_nnreal r re := e.
Definition R_in_extend_nnreal (r : nnreal) (re : xnnreal) (w : R_nnreal r re) : extend r = re := w.
Definition R_in_extendK_nnreal (r : nnreal) (re : xnnreal) (w : R_nnreal r re) :
  extend_in_R_nnreal r re (R_in_extend_nnreal r re w) = w.
Proof. reflexivity. Defined.
Definition truncate_in_R_nnreal (r : nnreal) (re : xnnreal) (e : truncate re = r) : R_nnreal r re.
Proof. rewrite <- e; unfold R_nnreal. apply extend_truncate. Abort.
Definition R_in_truncate_nnreal (re : xnnreal) (r : nnreal) (w : R_nnreal r re) : truncate re = r.
Proof. rewrite <- w. apply truncate_extend. Defined.

(* maximum witness between non negative reals and their extended version *)
Definition Param42b_nnreal : Param42b.Rel nnreal xnnreal.
Proof.
  unshelve econstructor.
  - exact R_nnreal.
  - unshelve econstructor.
    + exact extend.
    + exact extend_in_R_nnreal.
    + exact R_in_extend_nnreal.
    + exact R_in_extendK_nnreal.
  - unshelve econstructor.
    + exact truncate.
    + exact R_in_truncate_nnreal.
Defined.

(* the only level we will need to pre-process the distributivity goal is (0,2b) *)
Definition Param02b_nnreal : Param02b.Rel nnreal xnnreal := Param42b_nnreal.

(* as sequences are encoded with constants, we need to relate them *)

Definition seq_extend (u : nnreal_cv_seq) : xnnreal_seq :=
  fun n => extend (u n).
Definition Rrseq (u : nnreal_cv_seq) (v : xnnreal_seq) : Type :=
  seq_extend u = v.
Definition extend_in_Rrseq
  (r : nnreal_cv_seq) (re : xnnreal_seq) (e : seq_extend r = re) : Rrseq r re := e.
Definition R_in_extend_rseq
  (r : nnreal_cv_seq) (re : xnnreal_seq) (w : Rrseq r re) : seq_extend r = re := w.
Definition R_in_extendK_rseq (r : nnreal_cv_seq) (re : xnnreal_seq) (w : Rrseq r re) :
  extend_in_Rrseq r re (R_in_extend_rseq r re w) = w.
Proof. reflexivity. Defined.

(* TODO: est-ce que (4,0) est le max ou on ne s'est simplement pas embêté? *)
Definition Param40_rseq : Param40.Rel nnreal_cv_seq xnnreal_seq.
Proof.
  unshelve econstructor.
  - exact Rrseq.
  - unshelve econstructor.
    + exact seq_extend.
    + exact extend_in_Rrseq.
    + exact R_in_extend_rseq.
    + exact R_in_extendK_rseq.
  - unshelve econstructor.
Defined.

(* we will only need (2a,0) on sequences to pre-process the distributivity goal *)
Definition Param2a0_rseq : Param2a0.Rel _ _ := Param40_rseq.

(* now we need to relate the various constants at level (0,0) *)

Definition R_xnnreal_add :
  forall (r1 : nnreal) (re1 : xnnreal), R_nnreal r1 re1 ->
  forall (r2 : nnreal) (re2 : xnnreal), R_nnreal r2 re2 ->
    R_nnreal (r1 + r2) (re1 + re2).
Proof.
rewrite /R_nnreal /extend.
move=> r1 [_ []|]; last by discriminate.
by move=> r2 [_ []|]; last by discriminate.
Qed.

Definition R_nnreal_seq_add :
  forall (r1 : nnreal_cv_seq) (re1 : xnnreal_seq), Rrseq r1 re1 ->
  forall (r2 : nnreal_cv_seq) (re2 : xnnreal_seq), Rrseq r2 re2 ->
  Rrseq (r1 + r2) (re1 + re2).
Proof.
move=> [r1 r1cv] re1 <-.
by move=> [r2 r2cv] re2 <-.
Qed.

Definition R_xnnreal_sum :
  forall (u : nnreal_cv_seq) (ue : xnnreal_seq),
     Rrseq u ue -> R_nnreal (Σ u) (Σ ue).
Proof.
rewrite /Rrseq /seq_extend /R_nnreal /nnreal_sum.
move=> u _ <-; rewrite extend_truncate//.
by apply nnreal_cv_seq_finite_sum.
Qed.

Elpi Query param lp:{{
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref
        {{:gref paths}} (pc map0 map1)
        [pc map0 map2b]
        {{:gref paths}} {{:gref Param01_paths}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref nnreal}} (pc map0 map2b) [] {{:gref xnnreal}}
        {{:gref Param02b_nnreal}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref nnreal_cv_seq}} (pc map2a map0) [] {{:gref xnnreal_seq}}
        {{:gref Param2a0_rseq}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref nnreal_sum}} (pc map0 map0) [] {{:gref xnnreal_sum}}
        {{:gref R_xnnreal_sum}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref nnreal_add}} (pc map0 map0) [] {{:gref xnnreal_add}}
        {{:gref R_xnnreal_add}})),
  coq.elpi.accumulate _ "param.db"
    (clause _ (before "default-gref")
      (param.db.gref {{:gref add_nnreal_cv_seq}} (pc map0 map0) [] {{:gref add_xnnreal_seq}}
        {{:gref R_nnreal_seq_add}})).
}}.

(* we get a proof over non negative reals for free,
   from the analogous proof over the extended ones *)
Lemma nnreal_cv_sumD : forall (u v : nnreal_cv_seq), (Σ (u + v) = Σ u + Σ v)%nnreal.
Proof.
  param.
  exact: xnnreal_sumD.
Qed.

Print Assumptions nnreal_cv_sumD.
