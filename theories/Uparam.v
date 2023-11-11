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
From HoTT Require Import HoTT.

Require Import HoTT_additions.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
  
(*****************)
(* Specific Code *)
(*****************)

Record map_graph (A B : Type@{i}) (R : A -> B -> Type@{i}) := MapGraph{
  _map : A -> B;
  _map_in_R : forall (a : A) (b : B), _map a = b -> R a b;
  _R_in_map : forall (a : A) (b : B), R a b -> _map a = b;
  _R_in_mapK : forall (a : A) (b : B),
                 _map_in_R a b o _R_in_map a b == idmap}.

Arguments map_graph {A B} _.
Arguments MapGraph {A B} _.
Arguments _map {A B R} _.
Arguments _map_in_R {A B R} _.
Arguments _R_in_map {A B R} _.
Arguments _R_in_mapK {A B R} _.

Structure uparam@{i} (A B : Type@{i}) := Uparam {
  _R :> A -> B -> Type@{i};
  _covariant : map_graph _R;
  _contravariant : map_graph (sym_rel _R);
}.

Arguments Uparam {_ _}.
Arguments _R {_ _} _.
Arguments _covariant {_ _} _.
Arguments _contravariant {_ _} _.

Section Uparam.
Context {A B : Type} (r : uparam A B).

Definition map := _map (_covariant r).
Definition map_in_R := _map_in_R (_covariant r).
Definition R_in_map := _R_in_map (_covariant r).
Definition R_in_mapK := _R_in_mapK (_covariant r).

Definition comap := _map (_contravariant r).
Definition comap_in_R := _map_in_R (_contravariant r).
Definition R_in_comap := _R_in_map (_contravariant r).
Definition R_in_comapK := _R_in_mapK (_contravariant r).

End Uparam.

Lemma map_graph_equiv_sigma  (A B : Type@{i}) (R : A -> B -> Type@{i}) :
  map_graph R <~> { map : A -> B |
                  { mR : forall (a : A) (b : B), map a = b -> R a b |
                  { Rm : forall (a : A) (b : B), R a b -> map a = b |
                    forall (a : A) (b : B), mR a b o Rm a b == idmap}}}.
Proof. by symmetry; issig. Defined.

Lemma map_graph_equiv_isfun `{Funext} {A B : Type@{i}}
  (R : A -> B -> Type@{i}) : map_graph R <~> IsFun R.
Proof.
apply (equiv_composeR' (map_graph_equiv_sigma _ _ R)).
transitivity (forall x : A, {y : B & {r : R x y &
                forall yr', (y; r) = yr'}}); last first. {
  apply equiv_functor_forall_id => a.
  apply (equiv_compose' (issig_contr _)).
  apply equiv_sigma_assoc'. }
apply (equiv_compose' (equiv_sig_coind _ _)).
apply equiv_functor_sigma_id => map.
apply (equiv_compose' (equiv_sig_coind _ _)).
apply (equiv_composeR' (equiv_sigma_symm _)).
transitivity {f : forall x, R x (map x) &
    forall (x : A) (y : B) (r :  R x y), (map x; f x) = (y; r)}; last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: (equiv_composeR' equiv_forall_sigma). }
transitivity {f : forall x, R x (map x) & forall (x : A) (y : B) (r :  R x y),
    {e : map x = y & e # f x = r}}; last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  apply (equiv_compose' equiv_path_sigma_dp).
  apply equiv_functor_sigma_id => e.
  exact: equiv_dp_path_transport. }
transitivity {f : forall x, R x (map x) &
    forall x y, {g : forall (r :  R x y), map x = y &
    forall (r :  R x y), g r # f x = r }}; last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  exact: equiv_sig_coind. }
transitivity{f : forall x, R x (map x) &
    forall x, {g : forall (y : B) (r :  R x y), map x = y &
    forall (y : B) (r :  R x y), g y r # f x = r }}; last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: equiv_sig_coind. }
transitivity {f : forall x, R x (map x) &
    {g : forall (x : A) (y : B) (r :  R x y), map x = y &
         forall x y r, g x y r # f x = r }}; last first. {
  apply equiv_functor_sigma_id => comap; exact: equiv_sig_coind. }
apply (equiv_compose' (equiv_sigma_symm _)).
apply equiv_functor_sigma_id => Rm.
transitivity {g : forall (x : A) (y : B) (e : map x = y), R x y &
    forall (x : A) (y : B) (r : R x y),
    Rm x y r # g x (map x) idpath = r }. {
  apply equiv_functor_sigma_id => mR.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  unshelve econstructor. {apply: concat. elim (Rm a b r). reflexivity. }
  unshelve econstructor. {apply: concat. elim (Rm a b r). reflexivity. }
  all: move=> r'; elim r'; elim (Rm a b r); reflexivity. }
symmetry.
unshelve eapply equiv_functor_sigma.
- move=> mR a b e; exact (e # mR a).
- move=> mR mRK x y r; apply: mRK.
- apply: isequiv_biinv.
  split; (unshelve eexists; first by move=> + a; apply) => //.
  move=> r; apply path_forall => a; apply path_forall => b.
  by apply path_arrow; elim.
- by move=> mR; unshelve econstructor.
Defined.

Lemma map_graph_isprop `{Funext} {A B : Type@{i}} (R : A -> B -> Type@{i}) :
  IsHProp (map_graph R).
Proof.
apply (istrunc_equiv_istrunc (IsFun R)); last exact: isfun_isprop.
apply symmetric_equiv; apply map_graph_equiv_isfun.
Qed.

Lemma uparam_equiv `{Univalence} {A B : Type} : uparam A B <~> (A <~> B).
Proof.
apply (equiv_compose' equiv_sig_relequiv^-1).
unshelve eapply equiv_adjointify.
- move=> [R mR msR]; exists R; exact: map_graph_equiv_isfun.
- move=> [R mR msR]; exists R; exact: (map_graph_equiv_isfun _)^-1%equiv.
- by move=> [R mR msR]; rewrite !equiv_invK.
- by move=> [R mR msR]; rewrite !equiv_funK.
Defined.

Definition id_map_graph {A : Type} : @map_graph A A (@paths A) :=
  MapGraph _ idmap (fun a b r => r) (fun a b r => r) (fun a b r => 1%path).

Definition id_sym_map_graph {A : Type} : @map_graph A A (sym_rel (@paths A)) :=
  MapGraph _ idmap (fun a b r => r^) (fun a b r => r^) (fun a b r => inv_V r).

Definition id_uparam {A : Type} : uparam A A :=
  Uparam (@paths A) id_map_graph id_sym_map_graph.

Lemma uparam_induction `{Univalence} A (P : forall B, uparam A B -> Type) :
  P A id_uparam -> forall B f, P B f.
Proof.
move=> PA1 B f; rewrite -[f]/(B; f).2 -[B]/(B; f).1.
suff : (A; id_uparam) = (B; f). { elim. done. }
apply: path_ishprop; apply: hprop_inhabited_contr => _.
apply: (contr_equiv' {x : _ & A = x}).
apply: equiv_functor_sigma_id => {f}B.
symmetry; apply: equiv_compose' uparam_equiv.
exact: equiv_path_universe.
Defined.

Lemma uparam_equiv_id `{Univalence} A : uparam_equiv (@id_uparam A) = equiv_idmap.
Proof. exact: path_equiv. Qed.

Definition map_graph_Type `{Univalence} : @map_graph Type@{i} Type@{i} uparam.
Proof.
unshelve refine (MapGraph _ idmap (fun a b e => e # id_uparam) _ _).
  { move=> A B /uparam_equiv; apply: path_universe_uncurried. }
move=> A B; elim/uparam_induction.
by rewrite uparam_equiv_id/= [path_universe_uncurried _]path_universe_1.
Defined.

Definition sym_map_graph_Type `{Univalence} : @map_graph Type@{i} Type@{i} (sym_rel uparam).
Proof.
unshelve refine (MapGraph _ idmap (fun a b e => e # id_uparam) _ _).
  { move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact. }
move=> A B; elim/uparam_induction.
by rewrite uparam_equiv_id/= [path_universe_uncurried _]path_universe_1.
Defined.

Definition uparam_Type `{Univalence} : uparam Type@{i} Type@{i} :=
  Uparam _ map_graph_Type sym_map_graph_Type.

Lemma R_uparam_Type `{Univalence} : (uparam_Type : _ -> _ -> _) = uparam.
Proof. reflexivity. Defined.

Lemma map_uparam_Type `{Univalence} : map uparam_Type = id.
Proof. reflexivity. Defined.

Lemma comap_uparam_Type `{Univalence} : comap uparam_Type = id.
Proof. reflexivity. Defined.
