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
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Notation bool := Datatypes.bool.
Notation false := Datatypes.false.
Notation true := Datatypes.true.

Inductive boolR : bool -> bool -> Type :=
  | falseR : boolR false false
  | trueR : boolR true true.

Definition map_bool : bool -> bool := id.

Definition map_in_R_bool {b b' : bool} (e : map_bool b = b') : boolR b b' :=
  match e with
  | idpath =>
    match b with
    | false => falseR
    | true => trueR
    end
  end.

Definition R_in_map_bool {b b' : bool} (bR : boolR b b') : map_bool b = b' :=
  match bR with
  | falseR => idpath
  | trueR => idpath
  end.

Definition R_in_mapK_bool {b b' : bool} (bR : boolR b b') :
  map_in_R_bool (R_in_map_bool bR) = bR :=
    match bR with
    | falseR => idpath
    | trueR => idpath
    end.

Definition Param_bool_sym {b b' : bool} (bR : boolR b b') : boolR b' b :=
  match bR with
  | falseR => falseR
  | trueR => trueR
  end.

Definition Param_bool_sym_inv {b b' : bool} (bR : boolR b b') :
  Param_bool_sym (Param_bool_sym bR) = bR :=
    match bR with
    | falseR => idpath
    | trueR => idpath
    end.

Definition boolR_sym : forall (b b' : bool), sym_rel boolR b b' <~> boolR b b'.
Proof.
  intros b b'.
  unshelve eapply equiv_adjointify.
  - apply Param_bool_sym.
  - apply Param_bool_sym.
  - intro bR. apply Param_bool_sym_inv.
  - intro bR. apply Param_bool_sym_inv.
Defined.

Definition Map4_bool : Map4.Has boolR.
Proof.
  unshelve econstructor.
  - exact map_bool.
  - exact @map_in_R_bool.
  - exact @R_in_map_bool.
  - exact @R_in_mapK_bool.
Defined.

Definition Param44_bool : Param44.Rel bool bool.
Proof.
  unshelve econstructor.
  - exact boolR.
  - exact Map4_bool.
  - apply (fun e => @eq_Map4 _ _ (sym_rel boolR) boolR e Map4_bool).
    apply boolR_sym.
Defined.
