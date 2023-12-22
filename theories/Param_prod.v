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

From Coq Require Import ssreflect.
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive prodR
  {A A'} (AR : A -> A' -> Type) {B B'} (BR : B -> B' -> Type) : A * B -> A' * B' -> Type :=
    | pairR a a' (aR : AR a a') b b' (bR : BR b b') : prodR AR BR (a, b) (a', b').

Arguments pairR {A A' AR B B' BR} a a' aR b b' bR.
(*  *)

Definition prod_map
  (A A' : Type) (AR : Param10.Rel A A') (B B' : Type) (BR : Param10.Rel B B') :
    A * B -> A' * B' :=
      fun p =>
        match p with
        | (a, b) => (map AR a, map BR b)
        end.

(*  *)

Definition pair_inj1 A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> a1 = a2 :=
    fun e => 
      match e in _ = (a, b) return _ = a with
      | eq_refl _ => @idpath _ a1
      end.

Definition pair_inj2 A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> b1 = b2 :=
    fun e => 
      match e in @paths _ _ (a, b) return _ = b with
      | @idpath _ _ => @idpath _ b1
      end.

Definition prod_map_in_R
  (A A' : Type) (AR : Param2a0.Rel A A') (B B' : Type) (BR : Param2a0.Rel B B') :
    forall p p', prod_map A A' AR B B' BR p = p' -> prodR AR BR p p' :=
  fun p p' =>
    match p with
    | (a, b) =>
      match p' with
      | (a', b') =>
        fun e =>
          pairR
            a a' (map_in_R AR a a' (pair_inj1 A' B' (map AR a) a' (map BR b) b' e))
            b b' (map_in_R BR b b' (pair_inj2 A' B' (map AR a) a' (map BR b) b' e))
      end
    end.

(*  *)

Definition prod_R_in_map
  (A A' : Type) (AR : Param2b0.Rel A A') (B B' : Type) (BR : Param2b0.Rel B B') :
    forall p p', prodR AR BR p p' -> prod_map A A' AR B B' BR p = p' :=
  fun p p' r =>
    match r with
    | pairR a a' aR b b' bR =>
      @transport _ (fun t => (t, map BR b) = (a', b')) _ _ (R_in_map AR a a' aR)^
        (@transport _ (fun t => (a', t) = (a', b')) _ _ (R_in_map BR b b' bR)^ idpath)
    end.

(*  *)

Definition ap2 : forall {A B C : Type} {a a' : A} {b b' : B} (f : A -> B -> C),
  a = a' -> b = b' -> f a b = f a' b' :=
    fun A B C a a' b b' f e1 e2 =>
      match e1 with
      | idpath =>
        match e2 with
        | idpath => idpath
        end
      end.

Definition prod_R_in_mapK
  (A A' : Type) (AR : Param40.Rel A A') (B B' : Type) (BR : Param40.Rel B B') :
    forall p p' (r : prodR AR BR p p'),
      prod_map_in_R A A' AR B B' BR p p' (prod_R_in_map A A' AR B B' BR p p' r) = r.
Proof.
Admitted.

Definition Map0_prod A A' (AR : Param00.Rel A A') B B' (BR : Param00.Rel B B') :
  Map0.Has (prodR AR BR).
Proof. constructor. Defined.

Definition Map1_prod A A' (AR : Param10.Rel A A') B B' (BR : Param10.Rel B B') :
  Map1.Has (prodR AR BR).
Proof. constructor. exact (prod_map A A' AR B B' BR). Defined.

Definition Map2a_prod A A' (AR : Param2a0.Rel A A') B B' (BR : Param2a0.Rel B B') :
  Map2a.Has (prodR AR BR).
Proof.
  unshelve econstructor.
  - exact (prod_map A A' AR B B' BR).
  - exact (prod_map_in_R A A' AR B B' BR).
Defined.

Definition Map2b_prod A A' (AR : Param2b0.Rel A A') B B' (BR : Param2b0.Rel B B') :
  Map2b.Has (prodR AR BR).
Proof.
  unshelve econstructor.
  - exact (prod_map A A' AR B B' BR).
  - exact (prod_R_in_map A A' AR B B' BR).
Defined.

Definition Map3_prod A A' (AR : Param30.Rel A A') B B' (BR : Param30.Rel B B') :
  Map3.Has (prodR AR BR).
Proof.
  unshelve econstructor.
  - exact (prod_map A A' AR B B' BR).
  - exact (prod_map_in_R A A' AR B B' BR).
  - exact (prod_R_in_map A A' AR B B' BR).
Defined.

Definition Map4_prod A A' (AR : Param40.Rel A A') B B' (BR : Param40.Rel B B') :
  Map4.Has (prodR AR BR).
Proof.
  unshelve econstructor.
  - exact (prod_map A A' AR B B' BR).
  - exact (prod_map_in_R A A' AR B B' BR).
  - exact (prod_R_in_map A A' AR B B' BR).
  - exact (prod_R_in_mapK A A' AR B B' BR).
Defined.
