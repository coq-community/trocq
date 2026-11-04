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

Section TrocqCoercionPi.

    Variable (A A' : Type).
    Variable (f : A -> A').

    Definition Rf := mkParam03 f.
    Trocq Register Rf.

    Variable (B : A -> Type) (B' : A' -> Type).
    Variable (BR : forall (a' : A') (a : A), Rf a' a -> Param10.Rel (B' a') (B a)).
    Trocq Register BR.
    
    Trocq Coercion On.
    Goal forall (a : A), B a.
        enough (x : forall a' : A', B' a') by exact x.
    Abort.

End TrocqCoercionPi.
