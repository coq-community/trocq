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

From Coq Require Import Prelude.
From Coq Require Import Setoid Morphisms.

(* what it can do *)
Section Test.
Declare Scope int_scope.
Delimit Scope int_scope with int.
Context (int : Set) (zero : int) (add : int -> int -> int).
Context (eqmodp : int -> int -> Prop).
Hypothesis eqmodp_equiv : Equivalence eqmodp.
Existing Instance eqmodp_equiv.

Hypothesis add_proper : Proper (eqmodp ==> eqmodp ==> eqmodp) add.
Existing Instance add_proper.

Notation "x == y" := (eqmodp x y) (format "x  ==  y", at level 70) : int_scope.
Notation "x + y" := (add x%int y%int) : int_scope.

Goal (forall x y : int, x + y == y + x)%int ->
     forall x y z, (x + y + z == y + x + z)%int.
Proof.
intros addC x y z.
rewrite (addC x y).
reflexivity.
Qed.

End Test.

(* what it cannot do : handle heterogenous relations *)
