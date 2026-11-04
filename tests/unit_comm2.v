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

Section N.

    Inductive N : Set :=
    | Z : N
    | S : N -> N.
    Fixpoint ad (n m : N) : N :=
        match n with
        | Z => m
        | S p => S (ad p m)
        end.

    Definition NR : Param44.Rel N N. admit. Admitted.
    Trocq Register NR.
    Definition NS {n n': N} (Rr : NR n n'): NR (S n) (S n'). admit. Admitted.
    Trocq Register NS.
    Definition Nad {n n' : N} (Rr : NR n n') {m m' : N} (Rr' : NR m m'): NR (ad n m) (ad n' m'). admit. Admitted.
    Trocq Register Nad.

    Variable A : Type.

    Variable (T : N -> Type) (T' : N -> Type).
    Variable (append : forall {n m : N}, T n -> T m -> T (ad n m)).
    Variable (append' : forall {n m : N}, T' n -> T' m -> T' (ad n m)).

    Definition NT
        {n n' : N} (nR : NR n n'): Param2a2b.Rel (T n) (T' n'). admit. Admitted.
    Trocq Register NT.


    Definition Nappend {n n' : N} (nR : NR n n')
        {m m' : N} (mR : NR m m')
        {t : T n} {t' : T' n'} (tR : NT nR t t')
        {u : T m} {u' : T' m'} (uR : NT mR u u') :
        NT (Nad nR mR) (append t u) (append' t' u'). admit. Admitted. 
    Trocq Register Nappend.

    Variable (P : forall {n : N}, T n -> Type).
    Variable (P' : forall {n : N}, T' n -> Type).
    Definition RP {n n' : N} (nR : NR n n')
        {t : T n} {t' : T' n'} {tR : NT nR t t'}
        : Param44.Rel (P t) (P' t').
        admit. Admitted.
    Trocq Register RP.

    Goal forall {n1 n2 : N}
        (v1 : T n1) (v2 : T n2),
        P (append v1 v2).
        trocq.
        enough (x : forall {n1 n2 : N}
            (v1 : T' n1) (v2 : T' n2),
            P' (append' v1 v2)) by exact x.
    Abort.

End N.
