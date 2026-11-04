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

Section TypeArrow.

    Variable (L L' : Type -> Type).
    Variable (f : forall (A : Type) (A' : Type), (A -> A') -> L' A' -> L A).

    Definition RL (A : Type) (A' : Type) (AR : Param10.Rel A A')
        : Param01.Rel (L A) (L' A') := mkParam01 (f A A' (map AR)).

    Trocq Register RL.

    Goal (forall A : Type, L A).
        trocq.
        enough (x : forall A' : Type, L' A') by exact x.
    Abort.

End TypeArrow.
