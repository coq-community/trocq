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

Section Transfer.

    Variable (I I' : Type).
    Variable (f : I -> I').

    Definition Rf := mkParam2a0 f.
    Trocq Register Rf.

    Variable (pe : I -> Prop) (pe' : I' -> Prop).
    Variable peR1 : forall (m : I) (m' : I') (rm : (Rf) m m'),
        pe m -> pe' m'.
    Variable peR2 : forall (m : I) (m' : I') (rm : (Rf) m m'),
        pe' m' -> pe m.
    Definition Rpe (n : I) (n' : I') (rn : (Rf) n n')
        : Param11.Rel (pe n) (pe' n') :=
        mkParam11 (peR1 n n' rn) (peR2 n n' rn).
    Trocq Register Rpe.

    Goal forall m : I, pe m.
        trocq.
        enough (x : forall m' : I', pe' m') by exact x.
    Abort.

End Transfer.
