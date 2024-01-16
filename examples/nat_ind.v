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

Set Universe Polymorphism.

Section IndType.
Variables (I : Type) (I0 : I) (IS : I -> I).
Variables (to_nat : I -> nat) (of_nat : nat -> I).

Hypothesis to_natK : forall x, of_nat (to_nat x) = x.
Hypothesis of_nat0 : of_nat O = I0.
Hypothesis of_natS : forall n, of_nat (S n) = IS (of_nat n).

(* We only need (2a,3), so it suffices that to_nat is a retraction *)
Definition RI : Param2a3.Rel I nat :=
 SplitSurj.toParamSym (SplitSurj.Build to_natK).

Definition RI0 : RI I0 O. Proof. exact of_nat0. Qed.
Definition RIS m n : RI m n -> RI (IS m) (S n).
Proof. by move=> <-; apply: of_natS. Qed.

Trocq Use RI RI0 RIS.

Lemma I_Srec : forall (P : I -> Type), P I0 ->
 (forall n, P n -> P (IS n)) -> forall n, P n.
Proof.
  trocq.
  (* the output sort of P' is (1,1) because of the covariant and contravariant occurrences of P in
     the input goal; this annotation was made to be definitionally equal to Type: from there,
     the induction principle of nat can be applied directly *)
  exact nat_rect.
Defined.

End IndType.

Check I_Srec.
Print I_Srec.
Print Assumptions I_Srec.
