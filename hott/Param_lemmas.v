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

Require Import ssreflect.
Require Import Stdlib Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(* General theorems *)
Lemma ind_map@{i} {A A' : Type@{i}} (AR : Param40.Rel@{i} A A') a
  (P : forall a', AR a a' -> map AR a = a' -> Type@{i}) :
  (P (map AR a) (map_in_R AR a (map AR a) 1%path) 1%path) ->
  forall a' aR, P a' aR (R_in_map AR a a' aR).
Proof.
by move=> P1 a' aR; rewrite -[X in P _ X](R_in_mapK AR); case: _ / R_in_map.
Defined.

Lemma ind_mapP@{i +} {A A' : Type@{i}} (AR : Param40.Rel@{i} A A') (a : A)
  (P : forall a', AR a a' -> map@{i} AR a = a' -> Type@{i})
  (P1 : P (map@{i} AR a) (map_in_R@{i} AR a (map@{i} AR a) 1%path) 1%path)
  (Q : forall a' aR e, P a' aR e -> Type@{i}) :
   Q (map@{i} AR a) (map_in_R@{i} AR a (map@{i} AR a) 1%path) 1%path P1 ->
  forall a' aR,
     Q a' aR (R_in_map@{i} AR a a' aR) (@ind_map@{i} A A' AR a P P1 a' aR).
Proof.
rewrite /ind_map => Q1 a' aR.
case: {1 6}_ / R_in_mapK.
by case: _ / R_in_map.
Defined.

Lemma weak_ind_map@{i} {A A' : Type@{i}} (AR : Param40.Rel@{i} A A') a
  (P : forall a', AR a a' -> Type@{i}) :
  (P (map AR a) (map_in_R AR a (map AR a) 1%path)) ->
  forall a' aR, P a' aR.
Proof. by move=> P1 a' aR; elim/(ind_map AR): aR / _. Defined.

Lemma ind_comap@{i} {A A' : Type@{i}} (AR : Param04.Rel@{i} A A') a'
  (P : forall a, AR a a' -> comap AR a' = a -> Type@{i}) :
  (P (comap AR a') (comap_in_R AR a' (comap AR a') 1%path) 1%path) ->
  forall a aR, P a aR (R_in_comap AR a' a aR).
Proof.
by move=> P1 a aR; rewrite -[X in P _ X](R_in_comapK AR); case: _ / R_in_comap.
Defined.

Lemma ind_comapP@{i +} {A A' : Type@{i}} (AR : Param04.Rel@{i} A A') a'
  (P : forall a, AR a a' -> comap AR a' = a -> Type@{i})
  (P1 : P (comap@{i} AR a') (comap_in_R@{i} AR a' (comap@{i} AR a') 1%path) 1%path)
  (Q : forall a aR e, P a aR e -> Type@{i}) :
   Q (comap@{i} AR a') (comap_in_R@{i} AR a' (comap@{i} AR a') 1%path) 1%path P1 ->
  forall a aR,
     Q a aR (R_in_comap@{i} AR a' a aR) (@ind_comap@{i} A A' AR a' P P1 a aR).
Proof.
rewrite /ind_comap => Q1 a aR.
case: {1 6}_ / R_in_comapK.
by case: _ / R_in_comap.
Defined.

Lemma weak_ind_comap@{i} {A A' : Type@{i}} (AR : Param04.Rel@{i} A A') a'
  (P : forall a, AR a a' -> Type@{i}) :
  (P (comap AR a') (comap_in_R AR a' (comap AR a') 1%path)) ->
  forall a aR, P a aR.
Proof. by move=> P1 a aR; elim/(ind_comap AR): aR / _. Defined.

Definition map_ind@{i} {A A' : Type@{i}} {PA : Param40.Rel@{i} A A'}
    (a : A) (a' : A') (aR : PA a a')
    (P : forall (a' : A'), PA a a' -> Type@{i})  :
   P a' aR -> P (map PA a) (map_in_R PA a (map PA a) idpath).
Proof. by elim/(ind_map PA): _ aR / _. Defined.

Definition comap_ind@{i} {A A' : Type@{i}} {PA : Param04.Rel@{i} A A'}
    (a : A) (a' : A') (aR : PA a a')
    (P : forall (a : A), PA a a' -> Type@{i})  :
   P a aR -> P (comap PA a') (comap_in_R PA a' (comap PA a') idpath).
Proof. by elim/(ind_comap PA): _ aR / _. Defined.

(* symmetry lemmas for Map *)

Definition eq_Map0w@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof.
  move=> RR' []; exists.
Defined.

Definition eq_Map1w@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof.
  move=> RR' [m]; exists. exact.
Defined.

Definition eq_Map2aw@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof.
  move=> RR' [m mR]; exists m.
  move=> a' b /mR/(snd (RR' _ _)); exact.
Defined.

Definition eq_Map2bw@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof.
  move=> RR' [m Rm]; unshelve eexists m.
  - move=> a' b /(fst (RR' _ _)) /Rm; exact.
Defined.

Definition eq_Map3w@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <--> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof.
  move=> RR' [m mR Rm]; unshelve eexists m.
  - move=> a' b /mR /(snd (RR' _ _)); exact.
  - move=> a' b /(fst (RR' _ _))/Rm; exact.
Defined.

Definition flipw@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
    (forall a a', R a a' <->> R' a a') ->
    (forall a a', R a a' <--> R' a a') :=
fun Rab a a' => ((Rab a a').1, (Rab a a').2.1).

Definition eq_Map0@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map0.Has@{i} R' -> Map0.Has@{i} R.
Proof. by move=> /flipw/eq_Map0w. Defined.

Definition eq_Map1@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map1.Has@{i} R' -> Map1.Has@{i} R.
Proof. by move=> /flipw/eq_Map1w. Defined.
  
Definition eq_Map2a@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map2a.Has@{i} R' -> Map2a.Has@{i} R.
Proof. by move=> /flipw/eq_Map2aw. Defined.

Definition eq_Map2b@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map2b.Has@{i} R' -> Map2b.Has@{i} R.
Proof. by move=> /flipw/eq_Map2bw. Defined.

Definition eq_Map3@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map3.Has@{i} R' -> Map3.Has@{i} R.
Proof. by move=> /flipw/eq_Map3w. Defined.
  
Definition eq_Map4@{i} {A A' : Type@{i}} {R R' : A -> A' -> Type@{i}} :
  (forall a a', R a a' <->> R' a a') ->
  Map4.Has@{i} R' -> Map4.Has@{i} R.
Proof.
move=> RR' [m mR Rm RmK]; unshelve eexists m _ _.
- move=> a' b /mR /(RR' _ _).2.1; exact.
- move=> a' b /(RR' _ _).1/Rm; exact.
- move=> a' b r /=; rewrite RmK.
  by case: RR' => /= f [/= g ].
Defined.

Register eq_Map0 as trocq.eq_map0.
Register eq_Map1 as trocq.eq_map1.
Register eq_Map2a  as trocq.eq_map2a.
Register eq_Map2b  as trocq.eq_map2b.
Register eq_Map3 as trocq.eq_map3.
Register eq_Map4 as trocq.eq_map4.

Section rel_uniq_refl.

  Variable A : Type.

  Variable AR : A -> A -> Type.
  Hypothesis AR_refl : forall a : A, AR a a.
  Hypothesis AR_eqb : forall a1 a2 : A, AR a1 a2 -> a1 = a2.
  Hypothesis rel_refl_uniq : forall (a : A) (r1 : AR a a), r1 = (AR_refl a).

  Lemma eqb_AR (a1 a2 : A) : a1 = a2 -> AR a1 a2.
  Proof. by move=> ->; apply AR_refl. Qed.

  Lemma AR_irrel : forall (a1 a2 : A) (r1 r2 : AR a1 a2), r1 = r2.
  Proof.
    move=> a1 a2 r.
    have e : a1 = a2 by apply AR_eqb.
    move: r; rewrite {}e=> r1 r2.
    by rewrite (rel_refl_uniq _ r1) (rel_refl_uniq _ r2).
  Qed.

  Definition mapR : A -> A := idmap.

  Lemma mR : forall a1 a2 : A, mapR a1 = a2 -> AR a1 a2.
  Proof. by move=> a1 a2; by rewrite /mapR=> ->; apply AR_refl. Qed.

  Lemma Rm : forall a1 a2 : A, AR a1 a2 -> idmap a1 = a2.
  Proof. by move=> /= a1 a2 /AR_eqb ->. Qed.

  Lemma mRRmK : forall (a1 a2 : A) (r : AR a1 a2), mR a1 a2 (Rm a1 a2 r) = r.
  Proof. by move=> a1 a2 r; apply AR_irrel. Qed.

  Lemma Map4_AR : Map4.Has AR.
  Proof.
    unshelve econstructor.
    - by apply mapR.
    - by apply mR.
    - by apply Rm.
    - by apply mRRmK.
  Qed.

  Lemma AR_sym : forall a1 a2, AR a1 a2 -> AR a2 a1.
  Proof. by move=> a1 a2 /AR_eqb ->; apply AR_refl. Qed.

  Lemma AR_sym_R : forall (a1 a2 : A), sym_rel AR a1 a2 <->> AR a1 a2.
  Proof.
    move=> a1 a2; unshelve eexists _,_ .
    - by apply AR_sym.
    - by apply AR_sym.
    - by move=> r; apply AR_irrel.
  Qed.

  Lemma Param44_AR : Param44.Rel A A.
  Proof.
    unshelve econstructor.
    - exact AR.
    - exact Map4_AR.
    - apply (fun e => @eq_Map4 _ _ (sym_rel AR) AR e Map4_AR).
      apply AR_sym_R.
   Qed.

End rel_uniq_refl.

Section RmmRK.

  Variable A B : Type.
  Variable R : A -> B -> Type.
  Variable map : A -> B.
  Variable map_in_R : forall x y, map x = y -> R x y. 
  Variable R_in_map : forall x y, R x y -> map x = y.
  Variable mRRmK : forall x y (r : R x y), map_in_R _ _ (R_in_map _ _ r) = r.

  Definition F {x : A} {y : B}  (p : map x = y) := apD (R_in_map x) p.

  Definition inverses_concat_tr : forall x y,
    forall p : map x = y,
    R_in_map x (map x) (map_in_R x (map x) 1) @ p 
    = R_in_map x y (transport _ p (map_in_R x (map x) 1)).
  Proof. 
  move=> x y p.
  rewrite -transport_paths_r.
  apply Wdpath_arrow.
  exact: F.
  Defined.

  Definition path_shape {x y} :
  forall p : map x = y,
  p = (R_in_map x (map x) (map_in_R x (map x) 1))^ 
      @ R_in_map x y (transport _ p (map_in_R x (map x) 1)).
  Proof.
  move=> p.
  rewrite -[X in X = _](concat_1p p).
  rewrite -[X in X @ p](concat_Vp (R_in_map x (map x) (map_in_R x (map x) 1))).
  rewrite concat_pp_p; apply ap.
  apply inverses_concat_tr.
  Defined.

  Lemma tr_1 : forall (x : A) y (p : map x = y), 
    transport (fun y=> R x y) p (map_in_R _ _ 1) = (map_in_R x y p).
  Proof.
  move=> x y p.
  by case: _ / p .
  Defined.

  Lemma Rm_concat : forall a b b' 
    (e : map a = b)
    (e1 : b = b'),
    R_in_map a b' (map_in_R a b' (e @ e1)) =
    R_in_map a b (map_in_R a b e) @ e1.
  Proof.
  move=> a b1 b2 e e1.
  by case: _ / e1; rewrite !concat_p1.
  Defined.

  Definition RmmRK : forall a b (e : map a = b), 
   R_in_map _ _ (map_in_R _ _ e) = e.
  Proof.
  move=> a b e.
  rewrite [X in _ = X](path_shape e).
  rewrite tr_1.
  set q := R_in_map a b _.
  set p := R_in_map _ _ _.
  apply (moveL_Vp q q p).
  rewrite -Rm_concat concat_1p.
  by rewrite /q mRRmK.
  Defined.

End RmmRK.
Section Genthm722.

  Variable A B : Type.
  Variable R : A -> B -> Type.
  Variable m : A -> B.
  Variable Rrefl : forall x y, m x = y -> R x y. (* 2a *)
  Variable imp : forall x y, R x y -> m x = y. (* 2b *)
  Variable MereR : forall x y (r1 r2 : R x y), r1 = r2.

  Definition inverses_concat_tr' : forall x,
  forall p : m x = m x,
    imp x (m x) (Rrefl x _ 1) @ p = imp x (m x) (transport _ p (Rrefl x _ 1)).
  Proof. 
  move=> x p.
  rewrite -transport_paths_r.
  apply Wdpath_arrow.
  exact: F.
  Defined.

  Definition path_shape' : forall x,
  forall p : m x = m x,
  p = (imp x (m x) (Rrefl x _ 1))^ @ imp x (m x) (@transport _ _ _ _ p (Rrefl x _ 1)).
  Proof.
  move=> x p.
  rewrite -[X in X = _](concat_1p p).
  rewrite -[X in X @ p](concat_Vp (imp x (m x) (Rrefl x _ 1))).
  rewrite concat_pp_p.
  apply ap.
  apply inverses_concat_tr.
  Defined.

  Lemma tr_id : forall (x : A) (p : m x = m x), 
    transport (fun y=> R x y) p (Rrefl x _ 1) = (Rrefl x _ 1).
  Proof. move=> x p; apply MereR. Qed.

  Definition UIP_MA {x y : A} (p q : m x = m y): p = q.
  Proof.
  move: q.
  case: _ /p.
  move=> q.
  rewrite (path_shape' x 1) /=.
  rewrite (path_shape' x q).
  by rewrite !tr_id.
  Defined.

  Section surj.

    Hypothesis comap : B -> A.
    Hypothesis corefl : forall b, R (comap b) b.
    
    Lemma UIP_B : forall (x y : B) (p q : x = y), p = q.
    Proof.
    move=> x y.
    rewrite -(imp _ _ (corefl x)).
    rewrite -(imp _ _ (corefl y)).
    apply UIP_MA.
    Qed.

  End surj.

End Genthm722.

Section thm722.

    Variable A : Type.
    Variable R : A -> A -> Type.
    Variable rrefl : forall x, R x x. (* 2a *)
    Definition rrefl' : forall x y, x = y -> R x y. 
    by move=> x y p; case: _ /p; apply rrefl. 
    Defined.
    Variable imp : forall x y, R x y -> x = y.  (* 2b *)
    Variable mereR : forall x y (r1 r2 : R x y), r1 = r2.

    Lemma uip_a (x y : A) (p q : x = y) : p = q.
    Proof. 
    apply (UIP_MA A A R (idmap) (rrefl') imp). 
    by move=> e ?; apply mereR.
    Qed.

End thm722.

(************************)
(* Proofs about Param44 *)
(************************)

Lemma umap_equiv_sigma (A B : Type@{i}) (R : A -> B -> Type@{i}) :
  IsUMap R <~>
    { map : A -> B |
    { mR : forall (a : A) (b : B), map a = b -> R a b |
    { Rm : forall (a : A) (b : B), R a b -> map a = b |
      forall (a : A) (b : B), mR a b o Rm a b == idmap } } }.
Proof. by symmetry; issig. Defined.

Definition issig_contr (A : Type) `{Funext}
  : {x : A & forall y, x = y} <~> Contr A.
Proof. apply equiv_inverse, equiv_istrunc_unfold. Defined.

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
  reflexivity.
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
  (do ?unshelve eexists); do ?by [
    move=> + a; apply => //|
    move=> r; apply path_forall => a //; apply path_forall => b; apply path_arrow; elim].
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
- by move=> [R mR msR]; cbv zeta; rewrite !equiv_invK.
- by move=> [R mR msR]; cbv zeta; rewrite !equiv_funK.
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
