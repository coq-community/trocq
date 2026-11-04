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

Section TrocqLogging.

    Variable (A B: Type).
    Variable (f : B -> A).

    Definition R1 : Param01.Rel A B := mkParam01 f.
    Trocq Register R1.

    Goal A.
        trocq.
        enough (x : B) by exact x.
    Abort.

    Trocq Logging trace.
    Goal A.
        trocq.
        enough (x : B) by exact x.
    Abort.

    Trocq Logging info.
    Goal A.
        trocq.
        enough (x : B) by exact x.
    Abort.
End TrocqLogging.
