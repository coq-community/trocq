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
From Trocq Require Import Trocq.
From Trocq_examples Require Import N.

Set Universe Polymorphism.

(** In this example, we transport the induction principle on natural numbers
  from two equivalent representations of `N`: the unary one `nat` and the binary
  one `N`. We introduce the `Trocq Use` command to register such translations.
  *)
Definition RN : (N <=> nat)%P := Iso.toParamSym N.of_nat_iso.
Trocq Use RN. (* registering related types *)

(** This equivalence proof coerces to a relation of type `N -> nat -> Type`,
  which we show relates the respective zero and successor constants of these
  types: *)
Definition RN0 : RN 0%N 0%nat. Proof. done. Defined.
Definition RNS m n : RN m n -> RN (N.succ m) (S n). Proof. by case: _ /. Defined.
Trocq Use RN0 RNS. (* registering related constants *)

(** We can now make use of the tactic to prove an induction principle on `N` *)
Lemma N_Srec : forall (P : N -> Type), P 0%N ->
    (forall n, P n -> P (N.succ n)) -> forall n, P n.
Proof. trocq. (* replaces N by nat in the goal *) exact nat_rect. Defined.

(** Inspecting the proof term actually reveals that univalence was not needed in
    the proof of `N_Srec`. The `example` directory of the artifact provides more
    examples, for weaker relations than equivalences, and beyond representation
    independence. *)
Set Printing Depth 20.
Print Assumptions N_Srec.

