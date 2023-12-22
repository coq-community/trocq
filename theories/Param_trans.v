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
Require Import HoTT_additions Hierarchy Common.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition R_trans {A B C : Type} (R1 : A -> B -> Type) (R2 : B -> C -> Type) : A -> C -> Type :=
  fun a c => {b : B & (R1 a b * R2 b c)%type}.

Definition map_trans {A B C : Type} (R1 : Param10.Rel A B) (R2 : Param10.Rel B C) : A -> C :=
  map R2 o map R1.

Definition map_in_R_trans {A B C : Type} (R1 : Param2a0.Rel A B) (R2 : Param2a0.Rel B C) :
  forall (a : A) (c : C), map_trans R1 R2 a = c -> R_trans R1 R2 a c.
Proof.
  intros a c e; exists (map R1 a); split.
  - apply (map_in_R R1); reflexivity.
  - apply (map_in_R R2); exact: e.
Defined.

Definition R_in_map_trans {A B C : Type} (R1 : Param2b0.Rel A B) (R2 : Param2b0.Rel B C) :
  forall (a : A) (c : C), R_trans R1 R2 a c -> map_trans R1 R2 a = c.
Proof.
  intros a c [b [r1 r2]]; apply R_in_map.
  exact: (transport (fun x => R2 x c) (R_in_map R1 a b r1)^).
Defined.

Definition R_in_mapK_trans {A B C : Type} (R1 : Param44.Rel A B) (R2 : Param44.Rel B C) :
  forall (a : A) (c : C) (r : R_trans R1 R2 a c),
    map_in_R_trans R1 R2 a c (R_in_map_trans R1 R2 a c r) = r.
Proof. Admitted.

Definition Map4_trans {A B C : Type} (R1 : Param44.Rel A B) (R2 : Param44.Rel B C) :
  Map4.Has (R_trans R1 R2).
Proof.
  unshelve econstructor.
  - exact (map_trans R1 R2).
  - exact (map_in_R_trans R1 R2).
  - exact (R_in_map_trans R1 R2).
  - exact (R_in_mapK_trans R1 R2).
Defined.

Definition R_trans_sym {A B C : Type} (R1 : Param44.Rel A B) (R2 : Param44.Rel B C) :
  forall (c : C) (a : A),
    sym_rel (R_trans R1 R2) c a <->> R_trans (sym_rel R2) (sym_rel R1) c a.
Proof.
  intros c a.
  unfold sym_rel, R_trans.
  unshelve eexists _, _.
  - intros [b [r1 r2]]. exact (b; (r2, r1)).
  - intros [b [r2 r1]]. exact (b; (r1, r2)).
  - intros [b [r2 r1]]; reflexivity.
Defined.

Definition Param44_trans {A B C : Type} : Param44.Rel A B -> Param44.Rel B C -> Param44.Rel A C.
Proof.
  intros R1 R2.
  unshelve econstructor.
  - exact (R_trans R1 R2).
  - exact (Map4_trans R1 R2).
  - unshelve eapply (@eq_Map4 _ _ (sym_rel (R_trans R1 R2)) (R_trans (sym_rel R2) (sym_rel R1))).
    + exact (R_trans_sym R1 R2).
    + exact (Map4_trans (Param44_sym B C R2) (Param44_sym A B R1)).
Defined.
