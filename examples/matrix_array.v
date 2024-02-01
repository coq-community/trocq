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

From Trocq Require Import Trocq.
From Trocq Require Import Param_sigma.

Axiom IMatrix : nat -> nat -> {A : Type & A} -> Type.
Axiom array : {A : Type & A} -> Type.
Definition sarray : nat -> nat -> {A : Type & A} -> Type := fun _ _ T => array T.

Axiom matrix_sarray_R_d : forall (m n : nat) (T : {A : Type & A}),
  Param42b.Rel (IMatrix m n T) (sarray m n T).

(* Definition matrix_sarray_R
  (m m' : nat) (mR : natR m m')
  (n n' : nat) (nR : natR n n')
  (T : {A : Type & A}) (T' : {A : Type & A}) (TR : sigR Type Type )
  Param42b.Rel (IMatrix m n T) (sarray m n T). *)
