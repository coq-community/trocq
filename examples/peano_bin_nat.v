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
we only need (2a,3) which is morally that Nmap is a split injection *)
Definition RN := SplitSurj.toParamSym@{Set} {|
   SplitSurj.retract := Ncomap;
   SplitSurj.section := Nmap;
   SplitSurj.sectionK := NmapK |}.

(* for brevity, we create witnesses at lower classes by forgetting fields in RN2a3 *)
(* this behaviour can be automated so as to only declare Rn2a3 and get for free all the instances
   reachable by forgetting fields *)
(* in the general case, if a field requires an axiom, it is better to manually recreate instances
   that do not need this field, so that it is not imported before forgetting, and the lower
   instances can be declared without the axiom *)

(* as 0 and Nsucc appear in the goal, we need to link them with nat constructors *)
(* NB: as these are not type formers, only class (0,0) is required, so these proofs amount to what
   would be done in the context of raw parametricity *)

Definition RN0 : RN N0 0%nat. Proof. done. Qed.
Definition RNS : forall m n, RN m n -> RN (Nsucc m) (S n).
Proof. by move=> _ + <-; case=> //=. Qed.

Trocq Use RN.
Trocq Use RN0.
Trocq Use RNS.

Lemma N_Srec : forall (P : N -> Type), P N0 ->
 (forall n, P n -> P (Nsucc n)) -> forall n, P n.
Proof.
  trocq.
  (* the output sort of P' is (1,1) because of the covariant and contravariant occurrences of P in
     the input goal; this annotation was made to be definitionally equal to Type: from there,
     the induction principle of nat can be applied directly *)
  exact nat_rect.
Defined.

Print N_Srec.
Print Assumptions N_Srec.
