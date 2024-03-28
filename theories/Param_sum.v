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
Require Import Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Print sum.

Inductive sumR
  A A' (AR : A -> A' -> Type) B B' (BR : B -> B' -> Type) : A + B -> A' + B' -> Type :=
    | inlR a a' (aR : AR a a') : sumR A A' AR B B' BR (inl a) (inl a')
    | inrR b b' (bR : BR b b') : sumR A A' AR B B' BR (inr b) (inr b').

(*  *)

Definition sum_map
  (A A' : Type) (AR : Param10.Rel A A') (B B' : Type) (BR : Param10.Rel B B') :
    A + B -> A' + B' :=
      fun p =>
        match p with
        | inl a => inl (map AR a)
        | inr b => inr (map BR b)
        end.

Definition inl_inj {A B} {a1 a2 : A}  :
  @inl A B a1 = inl a2 -> a1 = a2 :=
    fun e => 
      match e in @paths _ _ (inl a1) return _ = a1 with
      | @idpath _ _ => @idpath _ a1
      end.

Definition inr_inj {A B} {b1 b2 : B}  :
  @inr A B b1 = inr b2 -> b1 = b2 :=
    fun e => 
      match e in @paths _ _ (inr b1) return _ = b1 with
      | @idpath _ _ => @idpath _ b1
      end.

Definition inl_inr {A B a b} : @inl A B a = inr b -> False.
Proof. discriminate. Defined.

Definition inr_inl {A B b a} : @inr A B b = inl a -> False.
Proof. discriminate. Defined.

Definition sum_map_in_R
  (A A' : Type) (AR : Param2a0.Rel A A') (B B' : Type) (BR : Param2a0.Rel B B') :
    forall p p', sum_map A A' AR B B' BR p = p' -> sumR A A' AR B B' BR p p'.
Proof.
case=> [a|b] [a'|b']; do ?discriminate.
- by move=> /inl_inj<-; constructor; apply: map_in_R.
- by move=> /inr_inj<-; constructor; apply: map_in_R.
Defined.

(*  *)

Definition sum_R_in_map
  (A A' : Type) (AR : Param2b0.Rel A A') (B B' : Type) (BR : Param2b0.Rel B B') :
    forall p p', sumR A A' AR B B' BR p p' -> sum_map A A' AR B B' BR p = p'.
Proof.
by move=> _ _ [a a' aR|b b' bR]/=; apply: ap; apply: R_in_map.
Defined.

Definition sum_R_in_mapK
  (A A' : Type) (AR : Param40.Rel A A') (B B' : Type) (BR : Param40.Rel B B') :
    forall p p' (r : sumR A A' AR B B' BR p p'),
      sum_map_in_R A A' AR B B' BR p p' (sum_R_in_map A A' AR B B' BR p p' r) = r.
Proof.
  move=> _ _ [a a' aR|b b' bR]/=; rewrite /internal_paths_rew.
Admitted.

Definition Map0_sum A A' (AR : Param00.Rel A A') B B' (BR : Param00.Rel B B') :
  Map0.Has (sumR A A' AR B B' BR).
Proof. constructor. Defined.

Definition Map1_sum A A' (AR : Param10.Rel A A') B B' (BR : Param10.Rel B B') :
  Map1.Has (sumR A A' AR B B' BR).
Proof. constructor. exact (sum_map A A' AR B B' BR). Defined.

Definition Map2a_sum A A' (AR : Param2a0.Rel A A') B B' (BR : Param2a0.Rel B B') :
  Map2a.Has (sumR A A' AR B B' BR).
Proof.
  unshelve econstructor.
  - exact (sum_map A A' AR B B' BR).
  - exact (sum_map_in_R A A' AR B B' BR).
Defined.

Definition Map2b_sum A A' (AR : Param2b0.Rel A A') B B' (BR : Param2b0.Rel B B') :
  Map2b.Has (sumR A A' AR B B' BR).
Proof.
  unshelve econstructor.
  - exact (sum_map A A' AR B B' BR).
  - exact (sum_R_in_map A A' AR B B' BR).
Defined.

Definition Map3_sum A A' (AR : Param30.Rel A A') B B' (BR : Param30.Rel B B') :
  Map3.Has (sumR A A' AR B B' BR).
Proof.
  unshelve econstructor.
  - exact (sum_map A A' AR B B' BR).
  - exact (sum_map_in_R A A' AR B B' BR).
  - exact (sum_R_in_map A A' AR B B' BR).
Defined.

Definition Map4_sum A A' (AR : Param40.Rel A A') B B' (BR : Param40.Rel B B') :
  Map4.Has (sumR A A' AR B B' BR).
Proof.
  unshelve econstructor.
  - exact (sum_map A A' AR B B' BR).
  - exact (sum_map_in_R A A' AR B B' BR).
  - exact (sum_R_in_map A A' AR B B' BR).
  - exact (sum_R_in_mapK A A' AR B B' BR).
Defined.

Definition Param01_sum A A' (AR : Param01.Rel A A') B B' (BR : Param01.Rel B B') :
  Param01.Rel (A + B) (A' + B').
exists (sumR A A' AR B B' BR).
- exact: Map0_sum.
- admit.
Admitted.
