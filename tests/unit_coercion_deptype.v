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

Section TrocqDepType.

    Variable (A A' : Type).
    Variable (f : A -> A').
    Definition RA := mkParam10 f.

    Variable (L L' : Type -> Type).
    Variable (m : forall (X : Type) (X' : Type) (f : X -> X'), (L X) -> (L' X')).
    
    Definition RL (X : Type) (X' : Type) (XR : Param10.Rel X X') : Param10.Rel (L X) (L' X') := mkParam10 (m X X' (map XR)).

    Trocq Register RA.
    Trocq Register RL.

    Trocq Coercion On.
    Goal L' A'.
        enough (x : L A) by exact x.
    Abort.

End TrocqDepType.
