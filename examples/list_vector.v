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
From Trocq Require Import Param_nat Param_trans Param_bool Param_vector.

(* WIP: nlist_to_vector is not provable in the current state *)

Definition length {A : Type} : list A -> nat :=
  fix F l :=
    match l with
    | nil => O
    | cons a l => S (F l)
    end.

Definition nlist (A : Type) : nat -> Type := fun _ => list A.
Definition nnil {A : Type} : nlist A O := nil.
Definition ncons {A : Type} {n : nat} (a : A) (l : nlist A n) : nlist A (S n) := cons a l.

Inductive vector_nlist_R (A : Type) : forall (n : nat), Vector.t A n -> nlist A n -> Type :=
  | nilR : vector_nlist_R A O Vector.nil nnil
  | consR :
    forall (n : nat) (a : A) (v : Vector.t A n) (l : nlist A n) (r : vector_nlist_R A n v l),
      vector_nlist_R A (S n) (Vector.cons a v) (ncons a l).

Definition vector_to_nlist (A : Type) : forall (n : nat), Vector.t A n -> nlist A n :=
  fix F n v :=
    match v with
    | Vector.nil => nnil
    | Vector.cons k a u => ncons a (F k u)
    end.

Axiom vreverse : forall (A : Type) (n : nat), Vector.t A n -> Vector.t A n.
Axiom reverse : forall (A : Type), list A -> list A.
Definition nreverse (A : Type) : forall (n : nat), nlist A n -> nlist A n := fun _ => reverse A.

Axiom cheat : forall A, A.
Ltac cheat := apply cheat.

Definition list_to_vector (A : Type) (l : list A) : Vector.t A (length l).
Proof.
  induction l as [|a l IHl].
  - apply Vector.nil.
  - simpl. exact (@Vector.cons A (length l) a IHl).

Axiom nlist_to_vector : forall (A : Type) (n : nat), nlist A n -> Vector.t A n.

Definition vector_list_inj A n : @SplitInj.type (Vector.t A n) (nlist A n).
Proof.
  unshelve econstructor.
  - apply vector_to_nlist.
  - apply nlist_to_vector.
  - cheat.
Defined.

Definition vector_list_R A n : Param42b.Rel (Vector.t A n) (nlist A n) := SplitInj.toParam (vector_list_inj A n).

Definition Param44_42b_trans {A B C : Type} :
  Param44.Rel A B -> Param42b.Rel B C -> Param42b.Rel A C.
Proof.
  intros R1 R2.
  unshelve econstructor.
  - exact (R_trans R1 R2).
  - cheat.
  - cheat.
Defined.

Definition Param42b_vector_nlist
  (A A' : Type) (AR : Param44.Rel A A') (n n' : nat) (nR : natR n n') :
    Param42b.Rel (Vector.t A n) (nlist A' n').
Proof.
  unshelve eapply Param44_42b_trans.
  - exact (Vector.t A' n').
  - exact (Vector.Param44 A A' AR n n' nR).
  - exact (vector_list_R A' n').
Defined.

Axiom reverseR :
  forall (A : Type) (n : nat) (v : Vector.t A n) (l : nlist A n) (r : vector_list_R A n v l),
    vector_list_R A n (vreverse A n v) (nreverse A n l).
Axiom vreverseR :
  forall
    (A A' : Type) (AR : Param00.Rel A A')
    (n n' : nat) (nR : natR n n')
    (v : Vector.t A n) (v' : Vector.t A' n') (vR : Vector.tR A A' AR n n' nR v v'),
      Vector.tR A A' AR n n' nR (vreverse A n v) (vreverse A' n' v').
Definition vreverse_nreverse_R
  (A A' : Type) (AR : Param44.Rel A A')
  (n n' : nat) (nR : natR n n')
  (v : Vector.t A n) (l' : nlist A' n') (r : Param42b_vector_nlist A A' AR n n' nR v l') :
      Param42b_vector_nlist A A' AR n n' nR (vreverse A n v) (nreverse A' n' l').
Proof.
  destruct r as [v' [vR r]].
  simpl in *. unfold R_trans.
  exact (vreverse A' n' v'; (vreverseR A A' AR n n' nR v v' vR, reverseR A' n' v' l' r)).
Defined.

Trocq Use Param42b_vector_nlist.
Trocq Use vreverse_nreverse_R.
Trocq Use Param01_paths.
Trocq Use Param2a0_nat.

Goal forall A n (v : Vector.t A n), vreverse A n (vreverse A n v) = v.
  trocq. unfold nlist, nreverse. intros A _ l. Search reverse.

