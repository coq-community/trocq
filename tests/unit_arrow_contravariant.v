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

Section ArrowContravariant.
    Variable (A A' A'' B B' : Type).
    Variable (f1 : A -> A') (f2 : A'' -> A) (g1 : B -> B') (g2 : B' -> B).

    Definition RA1 : Param10.Rel A A' := mkParam10 f1.
    Definition RA2 : Param01.Rel A A'':= mkParam01 f2.
    Definition RB  : Param11.Rel B B' := mkParam11 g1 g2.

    Trocq Register RA1.
    Trocq Register RA2.
    Trocq Register RB.

    Goal A.
        trocq to A''.
        enough (x : A'') by exact x.
    Abort.

    Goal A -> B.
        trocq to (A' -> B').
        enough (x : A' -> B') by exact x.
    Abort.

    Goal B -> A.
        trocq to (B' -> A'').
        enough (x : B' -> A'') by exact x.
    Abort.

End ArrowContravariant.
