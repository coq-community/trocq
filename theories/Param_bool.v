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

Notation Bool := bool.

Inductive BoolR : Bool -> Bool -> Type :=
  | falseR : BoolR false false
  | trueR : BoolR true true.

Definition map_Bool : Bool -> Bool := id.

Definition map_in_R_Bool {b b' : Bool} (e : map_Bool b = b') : BoolR b b' :=
  match e with
  | idpath =>
    match b with
    | false => falseR
    | true => trueR
    end
  end.

Definition R_in_map_Bool {b b' : Bool} (bR : BoolR b b') : map_Bool b = b' :=
  match bR with
  | falseR => idpath
  | trueR => idpath
  end.

Definition R_in_mapK_Bool {b b' : Bool} (bR : BoolR b b') :
  map_in_R_Bool (R_in_map_Bool bR) = bR :=
    match bR with
    | falseR => idpath
    | trueR => idpath
    end.

Definition Param_Bool_sym {b b' : Bool} (bR : BoolR b b') : BoolR b' b :=
  match bR with
  | falseR => falseR
  | trueR => trueR
  end.

Definition Param_Bool_sym_inv {b b' : Bool} (bR : BoolR b b') :
  Param_Bool_sym (Param_Bool_sym bR) = bR :=
    match bR with
    | falseR => idpath
    | trueR => idpath
    end.

Definition BoolR_sym : forall (b b' : Bool), sym_rel BoolR b b' <->> BoolR b b'.
Proof.
  intros b b'; unshelve eexists _,_ .
  - apply Param_Bool_sym.
  - apply Param_Bool_sym.
  - intro bR. apply Param_Bool_sym_inv.
Defined.

Definition Map4_Bool : Map4.Has BoolR.
Proof.
  unshelve econstructor.
  - exact map_Bool.
  - exact @map_in_R_Bool.
  - exact @R_in_map_Bool.
  - exact @R_in_mapK_Bool.
Defined.

Definition Param44_Bool : Param44.Rel Bool Bool.
Proof.
  unshelve econstructor.
  - exact BoolR.
  - exact Map4_Bool.
  - apply (fun e => @eq_Map4 _ _ (sym_rel BoolR) BoolR e Map4_Bool).
    apply BoolR_sym.
Defined.
