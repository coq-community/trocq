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
Require Import Stdlib Database.
From elpi Require Import elpi.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.

Import HoTTNotations.
From Trocq.Elpi Extra Dependency "class.elpi" as class.
From Trocq.Elpi.generation Extra Dependency "hierarchy.elpi" as hierarchy_generation.

Elpi Command genhierarchy.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File hierarchy_generation.

(* Coq representation of the hierarchy *)
Inductive map_class : Set := map0 | map1 | map2a | map2b | map3 | map4.

Register map0 as trocq.indc_map0.
Register map1 as trocq.indc_map1.
Register map2a as trocq.indc_map2a.
Register map2b as trocq.indc_map2b.
Register map3 as trocq.indc_map3.
Register map4 as trocq.indc_map4.
Elpi Query lp:{{register-map-inductives}}.

(*************************)
(* Parametricity Classes *)
(*************************)

(* first unilateral witnesses describing one side of the structure given to a relation *)

Module Map0.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {}.
End Map0.

Module Map1.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B
}.
End Map1.

Module Map2a.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b
}.
End Map2a.

Module Map2b.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map2b.

Module Map3.
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b
}.
End Map3.

Module Map4.
(* An alternative presentation of Sozeau, Tabareau, Tanter's univalent parametricity:
   symmetrical and transport-free *)
Record Has@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := BuildHas {
  map : A -> B;
  map_in_R : forall (a : A) (b : B), map a = b -> R a b;
  R_in_map : forall (a : A) (b : B), R a b -> map a = b;
  R_in_mapK : forall (a : A) (b : B) (r : R a b), (map_in_R a b (R_in_map a b r)) = r
}.
End Map4.

Register Map0.Has as trocq.map0.
Register Map1.Has as trocq.map1.
Register Map1.map as trocq.map1.map.
Register Map2a.Has as trocq.map2a.
Register Map2a.map_in_R as trocq.map2a.map_in_r.
Register Map2b.Has as trocq.map2b.
Register Map2b.R_in_map as trocq.map2b.r_in_map.
Register Map3.Has as trocq.map3.
Register Map4.Has as trocq.map4.
Register Map4.R_in_mapK as trocq.map4.r_in_mapk.
Elpi Query lp:{{register-map-classes}}.

Definition sym_rel@{i} {A B : Type@{i}} (R : A -> B -> Type@{i}) := fun b a => R a b.

Import HoTTNotations.

Register sym_rel as trocq.sym_rel.

Elpi Query lp:{{
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.sym-rel {{:gref lib:trocq.sym_rel}})),
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (pi UI\
    trocq.db.paths UI (global {{:gref lib:trocq.paths}})
  )).
}}.

Definition PType (n : map_class) (m : map_class) : Type := Type.
Definition PTriple {T T' TR : Type} (X : T) (X' : T') (XR : TR) := X.

Register PType as trocq.fake_aterm_ptype.
Register PTriple as trocq.fake_aterm_ptriple.
Elpi Query lp:{{
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.fake-aterm-ptype {{:gref lib:trocq.fake_aterm_ptype}} {{:gref lib:trocq.fake_aterm_ptriple}})).
}}.

(********************)
(* Record Hierarchy *)
(********************)

Elpi Accumulate lp:{{
  main-interp [] _ :-
    std.forall {param-class.all-of-kind all} (Class\ sigma ModuleName\
      param-class.add-suffix Class "Param" ModuleName,
      coq.env.begin-module ModuleName none,
      generate-module Class,
      coq.env.end-module _
    ).
}}.

#[synterp] Elpi Accumulate File class.
#[synterp] Elpi Accumulate lp:{{
  main-synterp [] _ :-
    std.forall {param-class.all-of-kind all} (Class\ sigma ModuleName\
      param-class.add-suffix Class "Param" ModuleName,
      coq.env.begin-module ModuleName none,

      coq.env.end-module _
    ).
}}.

Elpi genhierarchy.

(********************)
(* Record Weakening *)
(********************)

Elpi Query lp:{{
  std.forall {map-class.all-of-kind all} m\ sigma SubClasses\
    map-class.weakenings-from m SubClasses,
    std.forall SubClasses m'\ sigma Name GR GR'\
     trocq.db.map->class m GR, trocq.db.map->class m' GR',
     map-class.add-2-suffix "" m m' "forgetMap" Name,
     util.add-named-coe Name GR GR' _.
}}.

Elpi Query lp:{{
  std.forall {param-class.all-of-kind all} generate-forget.
}}.

(* General projections *)

Definition rel {A B} (R : Param00.Rel A B) := Param00.R A B R.
Coercion rel : Param00.Rel >-> Funclass.

Register rel as trocq.rel0.
Elpi Query lp:{{
  coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.rel0 {{:gref lib:trocq.rel0}})).
}}.

Definition map {A B} (R : Param10.Rel A B) : A -> B :=
  Map1.map _ (Param10.covariant A B R).
Definition map_in_R {A B} (R : Param2a0.Rel A B) :
  forall (a : A) (b : B), map R a = b -> R a b :=
  Map2a.map_in_R _ (Param2a0.covariant A B R).
Definition R_in_map {A B} (R : Param2b0.Rel A B) :
  forall (a : A) (b : B), R a b -> map R a = b :=
  Map2b.R_in_map _ (Param2b0.covariant A B R).
Definition R_in_mapK {A B} (R : Param40.Rel A B) :
  forall (a : A) (b : B), map_in_R R a b o R_in_map R a b == idmap :=
  Map4.R_in_mapK _ (Param40.covariant A B R).

Arguments map : simpl never.
Arguments map_in_R : simpl never.
Arguments R_in_map : simpl never.
Arguments R_in_mapK : simpl never.

Definition comap {A B} (R : Param01.Rel A B) : B -> A :=
  Map1.map _ (Param01.contravariant A B R).
Definition comap_in_R {A B} (R : Param02a.Rel A B) :
  forall (b : B) (a : A), comap R b = a -> R a b :=
  Map2a.map_in_R _ (Param02a.contravariant A B R).
Definition R_in_comap {A B} (R : Param02b.Rel A B) :
  forall (b : B) (a : A), R a b -> comap R b = a :=
  Map2b.R_in_map _ (Param02b.contravariant A B R).
Definition R_in_comapK {A B} (R : Param04.Rel A B) :
  forall (b : B) (a : A), comap_in_R R b a o R_in_comap R b a == idmap :=
  Map4.R_in_mapK _ (Param04.contravariant A B R).

Arguments comap : simpl never.
Arguments comap_in_R : simpl never.
Arguments R_in_comap : simpl never.
Arguments R_in_comapK : simpl never.

(* Aliasing *)

Declare Scope param_scope.
Local Open Scope param_scope.
Delimit Scope param_scope with P.

Notation UParam := Param44.Rel.
Notation MkUParam := Param44.BuildRel.
Notation "A <=> B" := (Param44.Rel A B) : param_scope.
Notation IsUMap := Map4.Has.
Notation MkUMap := Map4.BuildHas.
Arguments Map4.BuildHas {A B R}.
Arguments Param44.BuildRel {A B R}.

Definition id_umap@{i} {A : Type@{i}} : IsUMap (@paths A) :=
  MkUMap idmap (fun a b r => r) (fun a b r => r) (fun a b r => 1%path).

Definition id_sym_umap@{i} {A : Type@{i}} : IsUMap (sym_rel (@paths A)) :=
  MkUMap idmap (fun a b r => r^) (fun a b r => r^) (fun a b r => inv_V r).

Definition id_uparam@{i} {A : Type@{i}} : A <=> A :=
  MkUParam id_umap id_sym_umap.

(* instances of MapN for A = A *)
(* allows to build id_ParamMN : forall A, ParamMN.Rel A A *)

Definition id_Map0 {A : Type} : Map0.Has (@paths A).
Proof. constructor. Defined.

Definition id_Map0_sym {A : Type} : Map0.Has (sym_rel (@paths A)).
Proof. constructor. Defined.

Definition id_Map1 {A : Type} : Map1.Has (@paths A).
Proof. constructor. exact idmap. Defined.

Definition id_Map1_sym {A : Type} : Map1.Has (sym_rel (@paths A)).
Proof. constructor. exact idmap. Defined.

Definition id_Map2a {A : Type} : Map2a.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined.

Definition id_Map2a_sym {A : Type} : Map2a.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined.

Definition id_Map2b {A : Type} : Map2b.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined.

Definition id_Map2b_sym {A : Type} : Map2b.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined.

Definition id_Map3 {A : Type} : Map3.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
Defined.

Definition id_Map3_sym {A : Type} : Map3.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
Defined.

Definition id_Map4 {A : Type} : Map4.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
  - exact (fun a b e => 1%path).
Defined.

Definition id_Map4_sym {A : Type} : Map4.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
  - exact (fun A B e => inv_V e).
Defined.

Register id_Map0 as trocq.id_map0.
Register id_Map0_sym as trocq.id_map0_sym.
Register id_Map1 as trocq.id_map1.
Register id_Map1_sym as trocq.id_map1_sym.
Register id_Map2a as trocq.id_map2a.
Register id_Map2a_sym as trocq.id_map2a_sym.
Register id_Map2b as trocq.id_map2b.
Register id_Map2b_sym as trocq.id_map2b_sym.
Register id_Map3 as trocq.id_map3.
Register id_Map3_sym as trocq.id_map3_sym.
Register id_Map4 as trocq.id_map4.
Register id_Map4_sym as trocq.id_map4_sym.

Elpi Query lp:{{register-id-maps}}.

(* generate id_ParamMN : forall A, ParamMN.Rel A A for all M N *)

Elpi Query lp:{{
  std.forall {param-class.all-of-kind all} generate-id-param.
}}.

(* symmetry property for Param *)

Elpi Query lp:{{
  std.forall {param-class.all-of-kind all} generate-param-sym.
}}.



Definition Prop_id_Map0 {A : Prop} : Map0.Has (@paths A).
Proof. constructor. Defined.

Definition Prop_id_Map0_sym {A : Prop} : Map0.Has (sym_rel (@paths A)).
Proof. constructor. Defined.

Definition Prop_id_Map1 {A : Prop} : Map1.Has (@paths A).
Proof. constructor. exact idmap. Defined.

Definition Prop_id_Map1_sym {A : Prop} : Map1.Has (sym_rel (@paths A)).
Proof. constructor. exact idmap. Defined.

Definition Prop_id_Map2a {A : Prop} : Map2a.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined.

Definition Prop_id_Map2a_sym {A : Prop} : Map2a.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined.

Definition Prop_id_Map2b {A : Prop} : Map2b.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
Defined.

Definition Prop_id_Map2b_sym {A : Prop} : Map2b.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
Defined.

Definition Prop_id_Map3 {A : Prop} : Map3.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
Defined.

Definition Prop_id_Map3_sym {A : Prop} : Map3.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
Defined.

Definition Prop_id_Map4 {A : Prop} : Map4.Has (@paths A).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun a b e => e).
  - exact (fun a b e => e).
  - exact (fun a b e => 1%path).
Defined.

Definition Prop_id_Map4_sym {A : Prop} : Map4.Has (sym_rel (@paths A)).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e^).
  - exact (fun A B e => e^).
  - exact (fun A B e => inv_V e).
Defined.

(* generate Prop_id_ParamMN : forall A, ParamMN.Rel A A for all M N *)

Elpi Query lp:{{
  std.forall {param-class.all-of-kind all} generate-prop-id-param.
}}.

(* symmetry property for Prop Param *)

Elpi Query lp:{{
  std.forall {param-class.all-of-kind all} generate-prop-param-sym.
}}.
