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

From Coq Require Import ssreflect.
From Trocq Require Import Trocq Param_list.
From Trocq_examples Require Import int_to_Zp.

Set Universe Polymorphism.

Local Open Scope int_scope.
Local Open Scope Zmodp_scope.

Definition Rp := SplitSurj.toParamSym (SplitSurj.Build reprpK).

Axiom Rzero : Rp zerop zero.
Variable Radd : binop_param Rp Rp Rp addp add.
Variable paths_to_eqmodp : binop_param Rp Rp iff paths eqmodp.

Trocq Use Rp Param01_paths Param10_paths Radd Rzero Param_cons Param_nil.

Module Stuck.

Trocq Use Param44_list.
Goal forall (l : list Zmodp), l = l.
Fail trocq.
Abort.

End Stuck.

Module Works.

Trocq Use Param2a4_list.
Goal forall (l : list Zmodp), l = l.
trocq.
reflexivity.
Qed.

End Works.

