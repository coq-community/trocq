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

(* Let us first prove that type nat , of unary natural numbers, and type N , of
binary ones, are equivalent *)
Definition RN44 : (N <=> nat)%P := Iso.toParamSym Niso.

(* This equivalence proof coerces to a relation of type N -> nat -> Type , which
relates the respective zero and successor constants of these types: *)
Definition RN0 : RN44 0%N 0%nat. Proof. done. Defined.
Definition RNS m n : RN44 m n -> RN44 (Nsucc m) (S n).
Proof. by move: m n => _ + <-; case=> //=. Defined.

(* We now register all these informations in a database known to the tactic: *)
Trocq Use RN0. Trocq Use RNS.
Trocq Use RN44.

(* We can now make use of the tactic to prove an induction principle on N *)
Lemma N_Srec : forall (P : N -> Type), P N0 ->
 (forall n, P n -> P (Nsucc n)) -> forall n, P n.
Proof. trocq. (* N replaces nat in the goal *) exact nat_rect. Defined.

(* Inspecting the proof term atually reveals that univalence was not needed
in the proof of N_Srec.  *)
Print N_Srec.
Print Assumptions N_Srec.

(* Indeed this computes *)
Eval compute in N_Srec (fun n => N) (0%N) Nadd (Npos 1~0~1~1~1~0).
