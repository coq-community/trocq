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

    Variable (pe : I -> I -> Prop) (pe' : I' -> I' -> Prop).
    Variable peR1 : forall (m : I) (m' : I') (rm : (Rf) m m')
        (n : I) (n' : I') (rn : (Rf) n n'),
        pe n m -> pe' n' m'.
    Variable peR2 : forall (m : I) (m' : I') (rm : (Rf) m m')
        (n : I) (n' : I') (rn : (Rf) n n'),
        pe' n' m' -> pe n m.
    Definition Rpe (n : I) (n' : I') (rn : (Rf) n n')
        (m : I) (m' : I') (rm : (Rf) m m')
        : Param11.Rel (pe n m) (pe' n' m') :=
        mkParam11 (peR1 m m' rm n n' rn) (peR2 m m' rm n n' rn).
    Trocq Register Rpe.

    Variable (p : I -> I -> I) (p' : I' -> I' -> I').
    Variable pR : forall (n m : I) (n' m' : I'), f (p n m) = p' n' m'.
    Definition Rp (m : I) (m' : I') (rm : (Rf) m m')
        (n : I) (n' : I') (rn : (Rf) n n')
        : (Rf) (p m n) (p' m' n') := pR m n m' n'.
    Trocq Register Rp.

    Goal forall m : I, forall n : I, pe m (p n n) -> pe m n.
        trocq.
        enough (x : forall m' : I', forall n' : I', pe' m' (p' n' n') -> pe' m' n') by exact x.
    Abort.

End Transfer.
