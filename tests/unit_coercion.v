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

Section TrocqCoercion.

    Variable (A B C : Type).
    Variable (f1 : B -> A) (f2 : C -> A).

    Definition R1 : Param10.Rel B A := mkParam10 f1.
    Definition R2 : Param10.Rel C A := mkParam10 f2.

    Trocq Register R1.
    Trocq Register R2.

    Trocq Coercion On.

    Goal A.
        enough (x : B) by exact x.
    Abort.

    Goal A.
        enough (x : C) by exact x.
    Abort.
End TrocqCoercion.
