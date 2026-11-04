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

Section SimplePi.

    Variable (A A' : Type).
    Variable (f : A -> A').
    Definition RA := mkParam2a0 f.

    Variable (B : A -> Type) (B' : A' -> Type).
    Variable (m : forall (X : A) (X' : A') (RX : RA X X'), (B' X') -> (B X)).
    Definition RL (X : A) (X' : A') (XR : RA X X') := mkParam01 (m X X' XR). 

    Trocq Register RA.
    Trocq Register RL.

    Goal forall X : A, B X.
        trocq.
        enough (x : forall X' : A', B' X') by exact x.
    Abort.

End SimplePi.
