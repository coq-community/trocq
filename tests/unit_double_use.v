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

Section DoubleUse.
    Variable (A A' : Type).
    Variable (f1 : A -> A') (f2 : A' -> A).

    Variable (F F' : Type -> Type).
    Definition RA : Param11.Rel A A' := mkParam11 f1 f2.

    Variable (RF1 : forall (X X' : Type) (RX : Param01.Rel X X'), Param01.Rel (F X) (F' X')).
    Variable (RF2 : forall (X X' : Type) (RX : Param10.Rel X X'), Param10.Rel (F X) (F' X')).
    

    Trocq Register RA.
    Trocq Register RF1.
    Trocq Register RF2.
    
    Trocq Logging trace.
    Goal F A -> F A.
        trocq.
        enough (x : F' A' -> F' A') by exact x.
    Abort.

End DoubleUse.
