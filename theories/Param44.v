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

From elpi Require Import elpi.
From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(*********************)
(* Proofs for UParam *)
(*********************)

Lemma umap_equiv_sigma (A B : Type@{i}) (R : A -> B -> Type@{i}) :
  IsUMap R <~>
    { map : A -> B |
    { mR : forall (a : A) (b : B), map a = b -> R a b |
    { Rm : forall (a : A) (b : B), R a b -> map a = b |
      forall (a : A) (b : B), mR a b o Rm a b == idmap } } }.
Proof. by symmetry; issig. Defined.

Lemma umap_equiv_isfun `{Funext} {A B : Type@{i}}
  (R : A -> B -> Type@{i}) : IsUMap R <~> IsFun R.
Proof.
apply (equiv_composeR' (umap_equiv_sigma _ _ R)).
transitivity (forall x : A, {y : B & {r : R x y & forall yr', (y; r) = yr'}});
last first. {
  apply equiv_functor_forall_id => a.
  apply (equiv_compose' (issig_contr _)).
  apply equiv_sigma_assoc'.
}
apply (equiv_compose' (equiv_sig_coind _ _)).
apply equiv_functor_sigma_id => map.
apply (equiv_compose' (equiv_sig_coind _ _)).
apply (equiv_composeR' (equiv_sigma_symm _)).
transitivity {f : forall x, R x (map x) &
  forall (x : A) (y : B) (r :  R x y), (map x; f x) = (y; r)};
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: (equiv_composeR' equiv_forall_sigma).
}
transitivity
  { f : forall x, R x (map x) &
    forall (x : A) (y : B) (r :  R x y), {e : map x = y & e # f x = r} };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  apply (equiv_compose' equiv_path_sigma_dp).
  apply equiv_functor_sigma_id => e.
  exact: equiv_dp_path_transport.
}
transitivity
  { f : forall x, R x (map x) &
    forall x y, {g : forall (r :  R x y), map x = y &
    forall (r :  R x y), g r # f x = r } };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  exact: equiv_sig_coind.
}
transitivity  { f : forall x, R x (map x) &
    forall x, { g : forall (y : B) (r :  R x y), map x = y &
                forall (y : B) (r :  R x y), g y r # f x = r } };
last first. {
  apply equiv_functor_sigma_id => comap.
  apply equiv_functor_forall_id => a.
  exact: equiv_sig_coind.
}
transitivity
  { f : forall x, R x (map x) &
    {g : forall (x : A) (y : B) (r :  R x y), map x = y &
         forall x y r, g x y r # f x = r } };
last first.
{ apply equiv_functor_sigma_id => comap; exact: equiv_sig_coind. }
apply (equiv_compose' (equiv_sigma_symm _)).
apply equiv_functor_sigma_id => Rm.
transitivity
  { g : forall (x : A) (y : B) (e : map x = y), R x y &
    forall (x : A) (y : B) (r : R x y), Rm x y r # g x (map x) idpath = r }. {
  apply equiv_functor_sigma_id => mR.
  apply equiv_functor_forall_id => a.
  apply equiv_functor_forall_id => b.
  apply equiv_functor_forall_id => r.
  unshelve econstructor. { apply: concat. elim (Rm a b r). reflexivity. }
  unshelve econstructor. { apply: concat. elim (Rm a b r). reflexivity. }
  all: move=> r'; elim r'; elim (Rm a b r); reflexivity.
}
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

Lemma umap_isprop `{Funext} {A B : Type@{i}} (R : A -> B -> Type@{i}) :
  IsHProp (IsUMap R).
Proof.
apply (istrunc_equiv_istrunc (IsFun R)); last exact: isfun_isprop.
apply symmetric_equiv; apply umap_equiv_isfun.
Qed.

Lemma uparam_equiv `{Univalence} {A B : Type} : (A <=> B) <~> (A <~> B).
Proof.
apply (equiv_compose' equiv_sig_relequiv^-1).
unshelve eapply equiv_adjointify.
- move=> [R mR msR]; exists R; exact: umap_equiv_isfun.
- move=> [R mR msR]; exists R; exact: (umap_equiv_isfun _)^-1%equiv.
- by move=> [R mR msR]; rewrite !equiv_invK.
- by move=> [R mR msR]; rewrite !equiv_funK.
Defined.

Definition id_umap {A : Type} : IsUMap (@paths A) :=
  MkUMap idmap (fun a b r => r) (fun a b r => r) (fun a b r => 1%path).

Definition id_sym_umap {A : Type} : IsUMap (sym_rel (@paths A)) :=
  MkUMap idmap (fun a b r => r^) (fun a b r => r^) (fun a b r => inv_V r).

Definition id_uparam {A : Type} : A <=> A :=
  MkUParam id_umap id_sym_umap.

Lemma uparam_induction `{Univalence} A (P : forall B, A <=> B -> Type) :
  P A id_uparam -> forall B f, P B f.
Proof.
move=> PA1 B f; rewrite -[f]/(B; f).2 -[B]/(B; f).1.
suff : (A; id_uparam) = (B; f). { elim. done. }
apply: path_ishprop; apply: hprop_inhabited_contr => _.
apply: (contr_equiv' {x : _ & A = x}).
apply: equiv_functor_sigma_id => {f} B.
symmetry; apply: equiv_compose' uparam_equiv.
exact: equiv_path_universe.
Defined.

Lemma uparam_equiv_id `{Univalence} A :
  uparam_equiv (@id_uparam A) = equiv_idmap.
Proof. exact: path_equiv. Defined.

(***********************)
(* Proofs for Universe *)
(***********************)

Definition umap_Type `{Univalence} : IsUMap@{i} UParam.
Proof.
  unshelve refine (MkUMap idmap (fun a b e => e # id_uparam) _ _).
  { move=> A B /uparam_equiv; apply: path_universe_uncurried. }
  move=> A B; elim/uparam_induction.
  by rewrite uparam_equiv_id /= [path_universe_uncurried _] path_universe_1.
Defined.

Definition sym_umap_Type `{Univalence} :
  @IsUMap Type@{i} Type@{i} (sym_rel UParam).
Proof.
  unshelve refine (MkUMap idmap (fun a b e => e # id_uparam) _ _).
  { move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact. }
  move=> A B; elim/uparam_induction.
  by rewrite uparam_equiv_id /= [path_universe_uncurried _] path_universe_1.
Defined.

Definition uparam_Type `{Univalence} : Type@{i} <=> Type@{i} :=
  MkUParam umap_Type sym_umap_Type.

Lemma R_uparam_Type `{Univalence} : rel uparam_Type = UParam.
Proof. reflexivity. Defined.

Lemma map_uparam_Type `{Univalence} : map uparam_Type = id.
Proof. reflexivity. Defined.

Lemma comap_uparam_Type `{Univalence} : comap uparam_Type = id.
Proof. reflexivity. Defined.

(********************************)
(* Proofs for dependent product *)
(********************************)

Definition uparam_sym {A A' : Type} : A <=> A' -> A' <=> A :=
  fun '(MkUParam R m c) => MkUParam c m.
Notation "R ^-1" := (uparam_sym R) : param_scope.

Definition uparam_sym_val {A A' : Type} (PA : A <=> A') (a : A) (a' : A') :
  PA a a' -> PA^-1 a' a.
Proof. by []. Defined.

Definition uparam_sym_val' {A A' : Type} (PA : A <=> A') (a : A) (a' : A') :
  PA^-1 a' a -> PA a a'.
Proof. by []. Defined.

Definition uparam_sym_val_equiv {A A' : Type} (PA : A <=> A')
  (a : A) (a' : A') : PA^-1 a' a = PA a a'.
Proof. by []. Defined.

Definition comap_ind {A A' : Type} {PA : Param04.Rel A A'}
    (a : A) (a' : A') (aR : PA a a')
    (P : forall (a : A), PA a a' -> Type)  :
   P a aR -> P (comap PA a') (comap_in_R PA a' (comap PA a') idpath).
Proof.
apply (transport
  (fun aR0 : PA a a' =>
    P a aR0 -> P (comap PA a')
                 (comap_in_R PA a' (comap PA a') idpath))
  (R_in_comapK PA a' a aR)
  (paths_rect A (comap PA a')
  (fun (a0 : A) (e : comap PA a' = a0) =>
   P a0 (comap_in_R PA a' a0 e) ->
   P (comap PA a')
    (comap_in_R PA a' (comap PA a') idpath)) idmap a
  (R_in_comap PA a' a aR))).
Defined.

Definition R_forall {A A' : Type} (PA : Param00.Rel A A')
    {B : A -> Type} {B' : A' -> Type}
    (PB : forall (a : A) (a' : A'), PA a a' -> Param00.Rel (B a) (B' a')) :
    (forall a : A, B a) -> (forall a' : A', B' a') -> Type :=
  fun f f' => forall a a' aR, PB a a' aR (f a) (f' a').

(* generic symmetry lemma *)
Definition eq_umap {A A' : Type} {R R' : A -> A' -> Type} :
  (forall a a', R a a' <~> R' a a') ->
  IsUMap R' -> IsUMap R.
Proof.
move=> RR' [m mR Rm RmK]; unshelve eexists m _ _.
- move=> a' b /mR /(RR' _ _)^-1%equiv; exact.
- move=> a' b /(RR' _ _)/Rm; exact.
- by move=> a' b r /=; rewrite RmK [_^-1%function _]equiv_funK.
Defined.

Definition uparam_forall_map1 {A A' : Type} (PA : Param02.Rel A A')
    {B : A -> Type} {B' : A' -> Type}
    (PB : forall (a : A) (a' : A'), PA a a' -> Param10.Rel (B a) (B' a')) :
   Map1.Has (R_forall PA PB).
Proof.
constructor.
exact (fun f a' => map (PB _ _ (comap_in_R _ _ _ 1)) (f (comap PA a'))).
Defined.

Definition uparam_forall_map2 {A A' : Type} (PA : Param04.Rel A A')
    {B : A -> Type} {B' : A' -> Type}
    (PB : forall (a : A) (a' : A'), PA a a' -> Param20.Rel (B a) (B' a')) :
   Map2.Has (R_forall PA PB).
Proof.
exists (Map1.map _ (uparam_forall_map1 PA PB)).
move=> f f' e a a' aR; apply (map_in_R (PB _ _ _)).
apply (transport (fun t => _ = t a') e) => /=.
by elim/(comap_ind a a' aR): _.
Defined.

Definition uparam_forall_map3 `{Funext} {A A' : Type} (PA : Param04.Rel A A')
    {B : A -> Type} {B' : A' -> Type}
    (PB : forall (a : A) (a' : A'), PA a a' -> Param30.Rel (B a) (B' a')) :
   Map3.Has (R_forall PA PB).
Proof.
exists (Map1.map _ (uparam_forall_map1 PA PB)).
- exact: (Map2.map_in_R _ (uparam_forall_map2 PA PB)).
- move=> f f' fR; apply path_forall => a'.
  apply (R_in_map (PB _ _ _)); exact: fR.
Defined.

Definition uparam_forall_umap `{Funext} {A A' : Type} (PA : Param04.Rel A A')
    {B : A -> Type} {B' : A' -> Type}
    (PB : forall (a : A) (a' : A'), PA a a' -> Param40.Rel (B a) (B' a')) :
   IsUMap (R_forall PA PB).
Proof.
exists (Map1.map _ (uparam_forall_map1 PA PB))
       (Map2.map_in_R _ (uparam_forall_map2 PA PB))
       (Map3.R_in_map _ (uparam_forall_map3 PA PB)).
move=> f f' fR /=.
apply path_forall => a.
apply path_forall => a'.
apply path_forall => aR.
unfold comap_ind.
elim (R_in_comapK PA a' a aR).
elim (R_in_comap PA a' a aR).
rewrite transport_apD10.
rewrite apD10_path_forall_cancel/=.
rewrite <- (R_in_mapK (PB _ _ _)).
by elim: (R_in_map _ _ _ _).
Defined.

Definition uparam_forall `{Funext} {A A' : Type} (PA : A <=> A')
     {B : A -> Type} {B' : A' -> Type}
     (PB : forall (a : A) (a' : A'), PA a a' -> B a <=> B' a') :
   (forall a : A, B a) <=> (forall a' : A', B' a').
Proof.
unshelve econstructor.
- exact: (R_forall PA PB).
- exact: (uparam_forall_umap PA PB).
- apply (eq_umap (fun _ _ => equiv_flip _)).
  exact: (uparam_forall_umap PA^-1 (fun a' a r => (PB a a' r)^-1)).
Defined.

Fact map_uparam_forall `{Funext} A A' (PA : A <=> A')
    B B' (PB : forall a a', PA a a' -> B a <=> B' a') :
  map (uparam_forall PA PB) =
  fun f a' => map (PB _ _ (comap_in_R _ _ _ 1)) (f (comap PA a')).
Proof. reflexivity. Qed.

Fact comap_uparam_forall `{Funext} A A' (PA : A <=> A')
    B B' (PB : forall a a', PA a a' -> B a <=> B' a') :
  comap (uparam_forall PA PB) =
  fun f a => comap (PB _ _ (map_in_R PA _ _ 1)) (f (map PA a)).
Proof. reflexivity. Qed.

Definition R_arrow {A A' : Type} (PA : Param00.Rel A A')
                   {B B' : Type} (PB : Param00.Rel B B') :
    (A -> B) -> (A' -> B') -> Type :=
  fun f f' => forall a a', PA a a' -> PB (f a) (f' a').

Definition uparam_arrow_map1 {A A' : Type} (PA : Param01.Rel A A')
    {B B' : Type} (PB : Param10.Rel B B') :
  Map1.Has (R_arrow PA PB).
Proof. exists; exact (fun f a' => map PB (f (comap PA a'))). Defined.

Definition uparam_arrow_map2 {A A' : Type} (PA : Param03.Rel A A')
    {B B' : Type} (PB : Param20.Rel B B') :
  Map2.Has (R_arrow PA PB).
Proof.
exists (Map1.map _ (uparam_arrow_map1 PA PB)).
move=> f f' /= e a a' aR; apply (map_in_R PB).
apply (transport (fun t => _ = t a') e) => /=.
by apply (transport (fun t => _ = map _ (f t)) (R_in_comap PA _ _ aR)^).
Defined.

Definition uparam_arrow_map3 `{Funext} {A A' : Type} (PA : Param03.Rel A A')
    {B B' : Type} (PB : Param30.Rel B B') :
   Map3.Has (R_arrow PA PB).
Proof.
exists (Map1.map _ (uparam_arrow_map1 PA PB)).
- exact: (Map2.map_in_R _ (uparam_arrow_map2 PA PB)).
- move=> f f' /= fR; apply path_arrow => a'.
  by apply (R_in_map PB); apply fR; apply (comap_in_R PA).
Defined.

Definition uparam_arrow_umap `{Funext} {A A' : Type} (PA : Param04.Rel A A')
    {B B' : Type} (PB : Param40.Rel B B') :
   IsUMap (R_arrow PA PB).
Proof.
exists (Map1.map _ (uparam_arrow_map1 PA PB))
       (Map2.map_in_R _ (uparam_arrow_map2 PA PB))
       (Map3.R_in_map _ (uparam_arrow_map3 PA PB)).
move=> f f' fR /=.
apply path_forall => a.
apply path_forall => a'.
apply path_arrow => aR /=.
rewrite -[in X in _ = X](R_in_comapK PA a' a aR).
elim (R_in_comap PA a' a aR).
rewrite transport_apD10 /=.
rewrite apD10_path_forall_cancel/=.
rewrite <- (R_in_mapK PB).
by elim: (R_in_map _ _ _ _).
Defined.

Definition uparam_arrow `{Funext} {A A' : Type} (PA : A <=> A')
     {B B' : Type} (PB : B <=> B') :
   (A -> B) <=> (A' -> B').
Proof.
unshelve econstructor.
- exact: (R_arrow PA PB).
- exact: (uparam_arrow_umap PA PB).
- apply (eq_umap (fun _ _ => equiv_flip _)).
  exact: (uparam_arrow_umap PA^-1 PB^-1).
Defined.

Fact map_uparam_arrow `{Funext} A A' (PA : A <=> A') B B' (PB : B <=> B') :
  map (uparam_arrow PA PB) = fun f a' => map PB (f (comap PA a')).
Proof. reflexivity. Qed.

Fact comap_uparam_arrow `{Funext} A A' (PA : A <=> A') B B' (PB : B <=> B') :
  comap (uparam_arrow PA PB) = fun f a => comap PB (f (map PA a)).
Proof. reflexivity. Qed.
