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

From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
From Trocq Require Import Trocq.
From Trocq_examples Require Import N.

Set Universe Polymorphism.

(* the best we can do to link these types is (4,4), but
we only need (2a,3) si ut suffices that N.to_nat is a retraction *)
Definition RN : Param2a3.Rel N nat :=
 SplitSurj.toParamSym (SplitSurj.Build N.to_natK).

(* as 0 and Nsucc appear in the goal, we need to link them with nat constructors *)
(* NB: as these are not type formers, only class (0,0) is required, so these proofs amount to what
   would be done in the context of raw parametricity *)

Definition RN0 : RN 0%N 0%nat. Proof. done. Qed.
Definition RNS m n : RN m n -> RN m.+1%N n.+1%nat. Proof. by case. Qed.

Trocq Use RN RN0 RNS.

Lemma N_Srec : forall (P : N -> Type), P N0 ->
 (forall n, P n -> P n.+1%N) -> forall n, P n.
Proof.
  trocq.
  (* the output sort of P' is (1,1) because of the covariant and contravariant occurrences of P in
     the input goal; this annotation was made to be definitionally equal to Type: from there,
     the induction principle of nat can be applied directly *)
  exact nat_rect.
Defined.

Print N_Srec.
Print Assumptions N_Srec.
