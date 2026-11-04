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

Require Import ssreflect.
From Trocq Require Import Trocq Param_list.

Set Universe Polymorphism.

Declare Scope int_scope.
Delimit Scope int_scope with int.
Delimit Scope int_scope with ℤ.
Local Open Scope int_scope.
Declare Scope Zmodp_scope.
Delimit Scope Zmodp_scope with Zmodp.
Local Open Scope Zmodp_scope.

Definition binop_param {X X'} RX {Y Y'} RY {Z Z'} RZ
   (f : X -> Y -> Z) (g : X' -> Y' -> Z') :=
  forall x x', RX x x' -> forall y y', RY y y' -> RZ (f x y) (g x' y').

(***
We setup an axiomatic context in order not to develop
arithmetic modulo in Coq/HoTT.
**)
Axiom (int@{i} : Type@{i}) (zero : int) (add : int -> int -> int)
      (mul : int -> int -> int) (one : int).
Axiom (addC : forall m n, add m n = add n m).
Axiom (Zmodp : Type) (zerop : Zmodp) (addp : Zmodp -> Zmodp -> Zmodp)
      (mulp : Zmodp -> Zmodp -> Zmodp) (onep : Zmodp).
Axiom (modp : int -> Zmodp) (reprp : Zmodp -> int)
      (reprpK : forall x, modp (reprp x) = x).

Definition eqmodp (x y : int) := modp x = modp y.

Definition Rp := SplitSurj.toParamSym (SplitSurj.Build reprpK).

Axiom Rzero : Rp zerop zero.
Axiom Radd : binop_param Rp Rp Rp addp add.
Axiom paths_to_eqmodp : binop_param Rp Rp iff eq eqmodp.

Trocq Register Rp.
Trocq Register Radd.
Trocq Register Rzero.
Print Param_cons.
Trocq Register Param_cons.
Trocq Register Param_nil.

Module Stuck.

Trocq Register Param44_list.
Goal forall (l : list Zmodp), l = l.
Fail trocq.
Abort.

End Stuck.

Module Works.

Trocq Register Param2a4_list.
Goal forall (l : list Zmodp), l = l.
trocq.
reflexivity.
Qed.

End Works.
