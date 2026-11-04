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

From elpi Require Export elpi.
From Trocq Require Export
  Database Hierarchy Vernac Param Common
  Param_arrow Param_Type Param_forall Param_prod Param_sigma
  Param_Empty Param_option Param_sum Param_trans Param_paths Param_vector
  Param_nat Param_list Param_bool Param_lemmas.

(* TODO: should we also export some variant-specific files, such as Param_Prop.v? *)
Trocq Register Param01_paths.
Trocq Register Param10_paths.