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
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive sigR
  A A' (AR : A -> A' -> Type)
  P P' (PR : forall a a', AR a a' -> P a -> P' a' -> Type) :
    {x : A & P x} -> {x' : A' & P' x'} -> Type :=
      | existR a a' (aR : AR a a') p p' (pR : PR a a' aR p p') :
        sigR A A' AR P P' PR (a; p) (a'; p').

Definition sig_map
  (A A' : Type) (AR : Param2a0.Rel A A')
  (P : A -> Type) (P' : A' -> Type) (PR : forall a a', AR a a' -> Param10.Rel (P a) (P' a')) :
    {x : A & P x} -> {x' : A' & P' x'} :=
      fun s => (map AR s.1; map (PR s.1 (map AR s.1) (map_in_R AR s.1 (map AR s.1) idpath)) s.2).

Definition sig_map_in_R
  (A A' : Type) (AR : Param2a0.Rel A A')
  (P : A -> Type) (P' : A' -> Type) (PR : forall a a', AR a a' -> Param2a0.Rel (P a) (P' a')) :
    forall (s : {x : A & P x}) (s' : {x' : A' & P' x'}),
      sig_map A A' AR P P' PR s = s' -> sigR A A' AR P P' PR s s'.
Proof.
move=> [x Px] [y Py]; case: _ /.
exists (@map_in_R A A' AR x _ 1); exact: map_in_R.
Defined.

Arguments rel : simpl never.

Definition sig_R_in_map
  (A A' : Type) (AR : Param40.Rel A A')
  (P : A -> Type) (P' : A' -> Type) (PR : forall a a', AR a a' -> Param2b0.Rel (P a) (P' a')) :
    forall (s : {x : A & P x}) (s' : {x' : A' & P' x'}),
      sigR A A' AR P P' PR s s' -> sig_map A A' AR P P' PR s = s'.
Proof.
  move=> [x Px] [u Py]; elim=> a a' aR p p' pR.
  elim (R_in_map _ _ _ pR).
  elim (R_in_mapK _ _ _ aR).
  by case: _ / (R_in_map AR _ _ aR).
Defined.

Definition sig_R_in_mapK
  (A A' : Type) (AR : Param40.Rel A A')
  (P : A -> Type) (P' : A' -> Type) (PR : forall a a', AR a a' -> Param40.Rel (P a) (P' a')) :
    forall (s : {x : A & P x}) (s' : {x' : A' & P' x'}),
      (sig_map_in_R A A' AR P P' PR s s') o (sig_R_in_map A A' AR P P' PR s s') == idmap.
Proof.

Admitted.