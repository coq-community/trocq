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

    Variable (I I' : Type) (f : I -> I').

    Definition Rf := mkParam2a0 f.
    Trocq Register Rf.

    Variable (pe : I -> I -> Prop) (pe' : I' -> I' -> Prop).
    Variable (peR : forall (n m : I) (n' m' : I'), Rf n n' -> Rf m m' -> pe' n' m' -> pe n m).

    Definition Rpe (n : I) (n' : I') (rn : Rf n n')
        (m : I) (m' : I') (rm : Rf m m') :=
        mkParam01 (peR n m n' m' rn rm).
    Trocq Register Rpe.

    Goal forall (n : I), forall (m : I), pe n m.
    Proof.
        trocq.
        enough (x : forall n' : I', forall m' : I', pe' n' m') by exact x.
    Abort.

End Transfer.
