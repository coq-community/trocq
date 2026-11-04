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

From Trocq Require Import Stdlib Trocq.

Set Universe Polymorphism.

Section LambdaType.
    Variable (U : Type) (U' : Type).

    Variable (fU : U' -> U).
    Definition RU := mkParam01 fU.
    Trocq Register RU.

    Goal (fun A : Type => U) (forall X : Type, U).
        trocq.
        enough (x : (fun A : Type => U') (forall X : Type, U')) by exact x.
    Abort.

    Goal (fun A : Type => U) (forall X : Type, X).
        trocq.
        enough (x : (fun A : Type => U') (forall X : Type, X)) by exact x.
    Abort.
End LambdaType.


