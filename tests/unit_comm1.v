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

    Variable (T : Type -> N -> Type) (T' : Type -> N -> Type).
    Variable (append : forall {A : Type} {n m : N}, T A n -> T A m -> T A (ad n m)).
    Variable (append' : forall {A : Type} {n m : N}, T' A n -> T' A m -> T' A (ad n m)).
    Variable (cons : forall {A : Type} {n : N}, A -> T A n -> T A (S n)).
    Variable (cons' : forall {A : Type} {n : N}, A -> T' A n -> T' A (S n)).

    Definition NT {A A' : Type} (AR : Param00.Rel A A')
        {n n' : N} (nR : NR n n'): Param2a2b.Rel (T A n) (T' A' n'). admit. Admitted.
    Trocq Register NT.


    Definition Ncons {A A' : Type} (AR : Param00.Rel A A')
        {n n' : N} (nR : NR n n')
        {a : A} {a' : A'} (aR : AR a a')
        {t : T A n} {t' : T' A' n'} (tR : NT AR nR t t') :
        NT AR (NS nR) (cons a t) (cons' a' t'). admit. Admitted.
    Trocq Register Ncons.

    Definition Nappend {A A' : Type} (AR : Param00.Rel A A')
        {n n' : N} (nR : NR n n')
        {m m' : N} (mR : NR m m')
        {t : T A n} {t' : T' A' n'} (tR : NT AR nR t t')
        {u : T A m} {u' : T' A' m'} (uR : NT AR mR u u') :
        NT AR (Nad nR mR) (append t u) (append' t' u'). admit. Admitted. 
    Trocq Register Nappend.

    Variable (P : forall {A : Type} {n : N}, T A n -> Type).
    Variable (P' : forall {A : Type} {n : N}, T' A n -> Type).
    Definition RP {A A' : Type} (AR : Param44.Rel A A')
        {n n' : N} (nR : NR n n')
        {t : T A n} {t' : T' A' n'} {tR : NT AR nR t t'}
        : Param44.Rel (P t) (P' t').
        admit. Admitted.
    Trocq Register RP.

    Goal forall {A : Type} {n1 n2 : N}
        (v1 : T A n1) (v2 : T A n2) (a : A),
        P (cons a (append v1 v2)).
        trocq.
        enough (x : forall {A' : Type} {n1' n2' : N}
            (v1' : T' A' n1') (v2' : T' A' n2') (a' : A'),
            P' (cons' a' (append' v1' v2'))) by exact x.
    Abort.

End N.
