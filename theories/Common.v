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

Require Import ssreflect.
From elpi Require Export elpi.
From Trocq Require Export
  HoTT_additions Hierarchy Param_Type Param_forall Param_arrow Database Param
  Param_paths Vernac.

Set Universe Polymorphism.

Local Open Scope param_scope.

Definition graph@{i} {A B : Type@{i}} (f : A -> B) := paths o f.

Module Fun.
Section Fun.
Universe i.
Context {A B : Type@{i}} (f : A -> B) (g : B -> A).
Definition toParam : Param40.Rel@{i} A B :=
  @Param40.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _
       (fun _ _ => id) (fun _ _ => id) (fun _ _ _ => 1%path))
     (@Map0.BuildHas@{i} _ _ _).

Definition toParamSym : Param04.Rel@{i} A B :=
  @Param04.BuildRel A B (sym_rel (graph g))
     (@Map0.BuildHas@{i} _ _ _)
     (@Map4.BuildHas@{i} _ _ _ g (fun _ _ => id) (fun _ _ => id)
        (fun _ _ _ => 1%path)).
End Fun.
End Fun.

Module SplitInj.
Section SplitInj.
Universe i.
Context {A B : Type@{i}}.
Record type@{} := {
  section :> A -> B;
  retract : B -> A;
  sectionK : forall x, retract (section x) = x
}.

Definition fromParam@{} (R : Param2a2b.Rel@{i} A B) := {|
  section := map R;
  retract := comap R;
  sectionK x := R_in_comap R _ _ (map_in_R R _ _ 1%path)
|}.

Section to.
Variable (f : type).

Let section_in_retract b a (e : f a = b) : retract f b = a :=
  transport (fun x => retract f x = a) e (sectionK f a).

Definition toParam@{} : Param42b.Rel@{i} A B :=
  @Param42b.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => id) (fun _ _ => id)
        (fun _ _ _ => 1%path))
     (@Map2b.BuildHas@{i} _ _ _ _ section_in_retract).

Definition toParamSym@{} : Param2b4.Rel@{i} B A :=
  @Param2b4.BuildRel B A (sym_rel (graph f))
     (@Map2b.BuildHas@{i} _ _ _ _ section_in_retract)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => id) (fun _ _ => id)
        (fun _ _ _ => 1%path)).

End to.

End SplitInj.
End SplitInj.

Module SplitSurj.
Section SplitSurj.
Universe i.
Context {A B : Type@{i}}.
Record type := {
  retract :> A -> B;
  section : B -> A;
  sectionK : forall x, retract (section x) = x
}.

Definition fromParam@{} (R : Param2b2a.Rel@{i} A B) := {|
  retract := map R;
  section := comap R;
  sectionK x := R_in_map R (comap R x) x (comap_in_R R x (comap R x) 1%path)
|}.

Section to.
Context (f : type).

Let section_in_retract b a (e : section f b = a) : f a = b :=
  transport (fun x => f x = b) e (sectionK f b).

Definition toParam@{} : Param42a.Rel@{i} A B :=
  @Param42a.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path))
     (@Map2a.BuildHas@{i} _ _ _ _ section_in_retract).

Definition toParamSym@{} : Param2a4.Rel@{i} B A :=
  @Param2a4.BuildRel B A (sym_rel (graph f))
     (@Map2a.BuildHas@{i} _ _ _ _ (section_in_retract))
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path)).

End to.

End SplitSurj.
End SplitSurj.

Module Iso.
Section Iso.
Universe i.
Context {A B : Type@{i}}.
Record type@{} := {
  map :> A -> B;
  comap : B -> A;
  mapK : forall x, comap (map x) = x;
  comapK : forall x, map (comap x) = x
}.

Section to.
Variable (f : type).

Let mapK' x : comap f (f x) = x :=
  ap (comap f) (ap f (mapK f x)^) @ ap (comap f) (comapK f _) @ mapK f x.

Let comap_in_map b a (e : comap f b = a) : f a = b :=
  ap f e^ @ comapK f b.

Let map_in_comap b a (e : f a = b) : comap f b = a :=
  ap (comap f) e^ @ mapK' a.

Let map_in_comapK b a (e : f a = b) :
  comap_in_map b a (map_in_comap b a e) = e.
Proof. Admitted.

Definition toParam@{} : Param44.Rel@{i} A B :=
  @Param44.BuildRel A B (graph f)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path))
     (@Map4.BuildHas@{i} _ _ _ _ comap_in_map map_in_comap map_in_comapK).

Definition toParamSym@{} : Param44.Rel@{i} B A :=
  @Param44.BuildRel B A (sym_rel (graph f))
     (@Map4.BuildHas@{i} _ _ _ _ comap_in_map map_in_comap map_in_comapK)
     (@Map4.BuildHas@{i} _ _ _ _ (fun _ _ => idmap) (fun _ _ => idmap)
        (fun _ _ _ => 1%path)).

End to.

End Iso.
End Iso.
