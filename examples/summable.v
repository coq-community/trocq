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

(* first, we axiomatise non negative reals *)

Axiom (nnR : Type).
Declare Scope nnR_scope.
Delimit Scope nnR_scope with nnR.
Bind Scope nnR_scope with nnR.

Axiom (zero_nnR : nnR).
Notation "0" := zero_nnR : nnR_scope.

Axiom (add_nnR : nnR -> nnR -> nnR).
Notation "x + y" := (add_nnR x%nnR y%nnR) : nnR_scope.

(* the extension is just defined as adding a constructor for infinite reals *)

Inductive xnnR : Type :=
  | Fin : nnR -> xnnR
  | Inf : xnnR.

Declare Scope xnnR_scope.
Delimit Scope xnnR_scope with xnnR.
Bind Scope xnnR_scope with xnnR.

Definition add_xnnR (re1 re2 : xnnR) : xnnR :=
  match re1, re2 with
  | Fin r1, Fin r2 => Fin (r1 + r2)%nnR
  | _, _ => Inf
  end.
Notation "x + y" := (add_xnnR x%xnnR y%xnnR) : xnnR_scope.

Definition seq_xnnR := nat -> xnnR.
Identity Coercion seq_xnnR_id : seq_xnnR >-> Funclass.
Declare Scope seq_xnnR_scope.
Delimit Scope seq_xnnR_scope with seq_xnnR.
Bind Scope seq_xnnR_scope with seq_xnnR.

Definition add_seq_xnnR (u v : seq_xnnR) : seq_xnnR :=
  fun n => (u n + v n)%xnnR.
Infix "+" := add_seq_xnnR : seq_xnnR_scope.

Definition seq_nnR := nat -> nnR.
Identity Coercion seq_nnR_id : seq_nnR >-> Funclass.

(* here we axiomatise the sequence sum and the distributivity lemma *)

Axiom (sum_xnnR : seq_xnnR -> xnnR).
Notation "'Σ' ue" := (sum_xnnR ue) (at level 35) : xnnR_scope.

Axiom sum_xnnR_add :
  forall u v : seq_xnnR, (Σ (u + v))%xnnR = (Σ u + Σ v)%xnnR.

Definition isFin (re : xnnR) : Bool :=
  match re with Fin _ => true | _ => false end.

(* summability is defined in terms of infinite sums *)
Definition isSummable (u : seq_nnR) := isFin (Σ (Fin o u))%xnnR.

(* the explicit cast functions between both types are a trivial extension and a truncation
   yielding a default value in the case of infinity *)

Definition extend (r : nnR) : xnnR := Fin r.

Definition truncate (re : xnnR) : nnR :=
  match re with
  | Inf => 0%nnR
  | Fin r => r
  end.

Record summable :=
  { to_seq :> seq_nnR; isSummableP : isSummable to_seq = true }.
Declare Scope summable_scope.
Delimit Scope summable_scope with summable.
Bind Scope summable_scope with summable.

Axiom summable_add :
  forall u v : summable, isSummable (fun n => u n + v n)%nnR = true.

Definition add_summable (u v : summable) :=
  Build_summable _ (summable_add u v).
Infix "+" := add_summable : summable_scope.

Definition sum_nnR (u : summable) : nnR :=
  truncate (sum_xnnR (Fin o u)).
Notation "'Σ' u" := (sum_nnR u) (at level 35) : nnR_scope.

(* various proofs to be used as fields of the parametricity witness *)

Definition R_nnR (r : nnR) (re : xnnR) : Type := extend r = re.

Definition truncate_extend : forall (r : nnR), truncate (extend r) = r.
Proof. reflexivity. Defined.

(* in this way, the composition is an identity only conditionally *)
(* this is why truncate_in_R_nnR is not provable and the maximum provable class is (4,2b) *)
Definition extend_truncate :
  forall (re : xnnR), isFin re = true -> extend (truncate re) = re.
Proof. by case => //=; discriminate. Defined.

Definition extend_in_R_nnR (r : nnR) (re : xnnR) (e : extend r = re) : R_nnR r re := e.
Definition R_in_extend_nnR (r : nnR) (re : xnnR) (w : R_nnR r re) : extend r = re := w.
Definition R_in_extendK_nnR (r : nnR) (re : xnnR) (w : R_nnR r re) :
  extend_in_R_nnR r re (R_in_extend_nnR r re w) = w.
Proof. reflexivity. Defined.
Definition truncate_in_R_nnR (r : nnR) (re : xnnR) (e : truncate re = r) : R_nnR r re.
Proof. rewrite <- e; unfold R_nnR. apply extend_truncate. Abort.
Definition R_in_truncate_nnR (re : xnnR) (r : nnR) (w : R_nnR r re) : truncate re = r.
Proof. rewrite <- w. apply truncate_extend. Defined.

(* maximum witness between non negative reals and their extended version *)
Definition Param42b_nnR : Param42b.Rel nnR xnnR.
Proof.
  unshelve econstructor.
  - exact R_nnR.
  - unshelve econstructor.
    + exact extend.
    + exact extend_in_R_nnR.
    + exact R_in_extend_nnR.
    + exact R_in_extendK_nnR.
  - unshelve econstructor.
    + exact truncate.
    + exact R_in_truncate_nnR.
Defined.

(* the only level we will need to pre-process the distributivity goal is (0,2b) *)
Definition Param02b_nnR : Param02b.Rel nnR xnnR := Param42b_nnR.

(* as sequences are encoded with constants, we need to relate them *)

Definition seq_extend (u : summable) : seq_xnnR :=
  fun n => extend (u n).
Definition Rrseq (u : summable) (v : seq_xnnR) : Type :=
  seq_extend u = v.
Definition extend_in_Rrseq
  (r : summable) (re : seq_xnnR) (e : seq_extend r = re) : Rrseq r re := e.
Definition R_in_extend_rseq
  (r : summable) (re : seq_xnnR) (w : Rrseq r re) : seq_extend r = re := w.
Definition R_in_extendK_rseq (r : summable) (re : seq_xnnR) (w : Rrseq r re) :
  extend_in_Rrseq r re (R_in_extend_rseq r re w) = w.
Proof. reflexivity. Defined.

(* we could go up to Param42b, but no further *)
Definition Param40_rseq : Param40.Rel summable seq_xnnR.
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

Definition R_add_xnnR :
  forall (r1 : nnR) (re1 : xnnR), R_nnR r1 re1 ->
  forall (r2 : nnR) (re2 : xnnR), R_nnR r2 re2 ->
    R_nnR (r1 + r2) (re1 + re2).
Proof.
rewrite /R_nnR /extend.
move=> r1 [_ []|]; last by discriminate.
by move=> r2 [_ []|]; last by discriminate.
Qed.

Definition seq_nnR_add :
  forall (r1 : summable) (re1 : seq_xnnR), Rrseq r1 re1 ->
  forall (r2 : summable) (re2 : seq_xnnR), Rrseq r2 re2 ->
  Rrseq (r1 + r2) (re1 + re2).
Proof.
move=> [r1 r1cv] re1 <-.
by move=> [r2 r2cv] re2 <-.
Qed.

Definition R_sum_xnnR :
  forall (u : summable) (ue : seq_xnnR),
     Rrseq u ue -> R_nnR (Σ u) (Σ ue).
Proof.
rewrite /Rrseq /seq_extend /R_nnR /sum_nnR.
move=> u _ <-; rewrite extend_truncate//.
by apply isSummableP.
Qed.

Trocq Use Param01_paths.
Trocq Use Param02b_nnR.
Trocq Use Param2a0_rseq.
Trocq Use R_sum_xnnR.
Trocq Use R_add_xnnR.
Trocq Use seq_nnR_add.

(* we get a proof over non negative reals for free,
   from the analogous proof over the extended ones *)
Lemma sum_nnR_add : forall (u v : summable), (Σ (u + v) = Σ u + Σ v)%nnR.
Proof. trocq; exact: sum_xnnR_add. Qed.

Print Assumptions sum_nnR_add.
