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

    Definition Rf := mkParam30 f.
    Trocq Register Rf.


    Variable (pe : I -> Prop) (pe' : I'  -> Prop).
    Variable (peR : forall (n : I) (n' : I'), Rf n n' -> pe' n' -> pe n).

    Definition Rpe
        (n : I) (n' : I') (rn : Rf n n')
         := mkParam01 (peR n n' rn).
    Trocq Register Rpe.

    Variable (qe : I -> I -> Prop) (qe' : I' -> I' -> Prop).
    Variable (qeR : forall (n m : I) (n' m' : I'), Rf n n' -> Rf m m' -> qe n m -> qe' n' m').
    Definition Rqe
        (n : I) (n' : I') (rn : Rf n n')
        (m : I) (m' : I') (rm : Rf m m')
        := mkParam10 (qeR n m n' m' rn rm).
    Trocq Register Rqe.

    Goal forall (m : I), qe m m -> pe m.
        assert (H : True -> True) by exact (fun x => x).
        trocq.
        enough (x : forall m : I', qe' m m -> pe' m) by exact x.
    Abort.

End Transfer.
