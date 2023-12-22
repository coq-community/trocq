(*****************************************************************************)
(*                            *                    Trocq                     *)
(*  _______                   *           Copyright (C) 2023 MERCE           *)
(* |__   __|                  *    (Mitsubishi Electric R&D Centre Europe)   *)
(*    | |_ __ ___   ___ __ _  *       Cyril Cohen <cyril.cohen@inria.fr>     *)
(*    | | '__/ _ \ / __/ _` | *       Enzo Crance <enzo.crance@inria.fr>     *)
(*    | | | | (_) | (_| (_| | *   Assia Mahboubi <assia.mahboubi@inria.fr>   *)
(*    |_|_|  \___/ \___\__, | ************************************************)
(*                        | | * This file is distributed under the terms of  *)
(*                        |_| * GNU Lesser General Public License Version 3  *)
(*                            * see LICENSE file for the text of the license *)
(*****************************************************************************)

From elpi Require Import elpi.
From Coq Require Import ssreflect.
From Trocq Require Import Trocq.

Set Universe Polymorphism.

(* Example file on CCω *)
(* Feel free to comment commands adding the axioms to the Trocq database,
   in order to see which goals can be pre-processed without them, and which ones cannot *)

Section test.
Universe i.

Goal
  (* Type@{i}. *)
  (* Type@{i} -> Type@{i}. *)
  (* forall (A : Type@{i}), A. *)
  forall (A : Type@{i}), A -> A.
  (* forall (A B : Type@{i}), A -> B. *)
  (* forall (F : Type@{i} -> Type@{i}) (A : Type@{i}), F A. *)
  (* forall (F : Type@{i} -> Type@{i}) (A B : Type@{i}), F A -> F B. *)
  (* forall (F : Type@{i} -> Type@{i} -> Type@{i}) (A B : Type@{i}), F A B. *)
  (* forall (F : Type@{i} -> Type@{i} -> Type@{i}) (A B : Type@{i}), F A B -> F B A. *)
  (* forall (F : Type@{i} -> Type@{i}) (A : Type@{i}), F A -> forall (B : Type@{i}), F B. *)
  (* forall (F : Type@{i} -> Type@{i}) (A : Type@{i}), F A -> forall (B : Type@{i}), F B -> F A. *)
  (* forall (A : Type@{i}) (F : A -> Type@{i}) (a : A), F a. *)
  (* forall (A : Type@{i}) (F : A -> Type@{i}) (a : A), F a -> F a. *)
  (* forall (F : Type@{i} -> Type@{i}) (A : Type@{i}) (H : F A -> Type@{i}) (J : F A), H J. *)
  (* forall (F : Type@{i} -> Type@{i}) (A B : Type@{i}) (H : F A -> F B) (J : F A) (K : F B -> Type), K (H J). *)
  (* forall
    (F : Type@{i} -> Type@{i}) (A : Type@{i}) (H : F A),
    F A -> forall (B : Type@{i}) (J : F A -> F B), (forall (K : F B -> Type@{i}), K (J H)) ->
      F B -> F A. *)
  (* forall (X : forall (A : Type@{i}), A -> Type@{i}) (A : Type@{i}) (a : A), A -> X A a -> A. *)
  (* forall (T : (Type@{i} -> Type@{j})) (F : ((Type@{i} -> Type@{j}) -> Type@{k})), F T. *)
Proof.
  param.
Abort.
End test.