From Coq Require Import ssreflect.
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Notation Empty := False.

Inductive EmptyR : Empty -> Empty -> Type := .

Definition map_Empty (e : Empty) : Empty := e.

Definition map_in_R_Empty : forall (e e' : Empty), map_Empty e = e' -> EmptyR e e' :=
  fun e => match e with end.

Definition R_in_map_Empty : forall (e e' : Empty), EmptyR e e' -> map_Empty e = e' :=
  fun e => match e with end.

Definition R_in_mapK_Empty : forall (e e' : Empty) (eR : EmptyR e e'),
  map_in_R_Empty e e' (R_in_map_Empty e e' eR) = eR :=
    fun e => match e with end.

Definition Map0_Empty : Map0.Has EmptyR.
Proof. constructor. Defined.

Definition Map1_Empty : Map1.Has EmptyR.
Proof. constructor. exact map_Empty. Defined.

Definition Map2a_Empty : Map2a.Has EmptyR.
Proof.
  unshelve econstructor.
  - exact map_Empty.
  - exact map_in_R_Empty.
Defined.

Definition Map2b_Empty : Map2b.Has EmptyR.
Proof.
  unshelve econstructor.
  - exact map_Empty.
  - exact R_in_map_Empty.
Defined.

Definition Map3_Empty : Map3.Has EmptyR.
Proof.
  unshelve econstructor.
  - exact map_Empty.
  - exact map_in_R_Empty.
  - exact R_in_map_Empty.
Defined.

Definition Map4_Empty : Map4.Has EmptyR.
Proof.
  unshelve econstructor.
  - exact map_Empty.
  - exact map_in_R_Empty.
  - exact R_in_map_Empty.
  - exact R_in_mapK_Empty.
Defined.

Definition Param01_Empty : Param01.Rel Empty Empty.
Proof.
unshelve econstructor; first exact: EmptyR.
- done.
- constructor; exact map_Empty.
Defined.


Definition Param10_Empty : Param10.Rel Empty Empty.
Proof.
unshelve econstructor; first exact: EmptyR.
- constructor; exact map_Empty.
- done.
Defined.

