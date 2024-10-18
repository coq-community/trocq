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
From Trocq Require Import Param_trans Param_list.

Set Universe Polymorphism.

Definition option_to_list {A : Type} (xo : option A) : list A :=
  match xo with
  | None => nil
  | Some x => cons x nil
  end.

Definition list_to_option {A : Type} (l : list A) : option A :=
  match l with
  | nil => None
  | cons x _ => Some x
  end.

Theorem option_to_listR (A : Type) (xo : option A) : list_to_option (option_to_list xo) = xo.
Proof. destruct xo; reflexivity. Qed.

Definition option_list_inj (A : Type) : @SplitInj.type (option A) (list A) :=
  SplitInj.Build (option_to_listR A).

Definition Param_option_list_d (A : Type) : Param42b.Rel (option A) (list A) :=
  SplitInj.toParam (option_list_inj A).

Definition Param42b_option_list (A A' : Type) (AR : Param42b.Rel A A') :
  Param42b.Rel (option A) (list A').
Proof.
  apply (@Param42b_trans _ (list A)).
  - apply Param_option_list_d.
  - apply (Param42b_list A A' AR).
Defined.
Trocq Use Param42b_option_list.

Definition omap {A B : Type} (f : A -> B) (xo : option A) : option B :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Definition map {A B : Type} (f : A -> B) : list A -> list B :=
  fix F l :=
    match l with
    | nil => nil
    | cons a l => cons (f a) (F l)
    end.

Definition mapR
  (A A' : Type) (AR : Param00.Rel A A')
  (B B' : Type) (BR : Param00.Rel B B')
  (f : A -> B) (f' : A' -> B') (fR : R_arrow AR BR f f')
  (l : list A) (l' : list A') (lR : listR A A' AR l l') :
    listR B B' BR (map f l) (map f' l').
Proof.
  induction lR; simpl.
  - apply nilR.
  - apply consR.
    + apply (fR a a' aR).
    + apply IHlR.
Defined.

Lemma option_to_list_map_morph (A B : Type) (f : A -> B) (xo : option A) :
  option_to_list (omap f xo) = map f (option_to_list xo).
Proof. destruct xo; reflexivity. Qed.

Definition omap_map_R
  (A A' : Type) (AR : Param42b.Rel A A')
  (B B' : Type) (BR : Param42b.Rel B B')
  (f : A -> B) (f' : A' -> B') (fR : R_arrow AR BR f f')
  (xo : option A) (l' : list A') (r : Param42b_option_list A A' AR xo l') :
    Param42b_option_list B B' BR (omap f xo) (map f' l').
Proof.
  destruct r as [l [r lR]].
  unshelve econstructor.
  - exact (map f l).
  - split.
    + rewrite <- r. apply option_to_list_map_morph.
    + exact (mapR A A' AR B B' BR f f' fR l l' lR).
Defined.
Trocq Use omap_map_R.

Trocq Use Param01_paths.

Theorem map_compose (A B C : Type) (l : list A) (f : A -> B) (g : B -> C) :
  map g (map f l) = map (fun x => g (f x)) l.
Proof.
  induction l; simpl.
  - reflexivity.
  - apply ap. apply IHl.
Qed.

Goal forall A B C (xo : option A) (f : A -> B) (g : B -> C),
  omap g (omap f xo) = omap (fun x => g (f x)) xo.
Proof.
  trocq.
  apply map_compose.
Qed.