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
Require Import HoTT_additions Hierarchy.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive listR (A A' : Type) (AR : A -> A' -> Type) : list A -> list A' -> Type :=
  | nilR : listR A A' AR (@nil A) (@nil A')
  | consR :
    forall (a : A) (a' : A') (aR : AR a a')
           (l : list A) (l' : list A') (lR : listR A A' AR l l'),
      listR A A' AR (cons a l) (cons a' l').

Definition map_list (A A' : Type) (AR : Param10.Rel A A') : list A -> list A' :=
  fix F (l : list A) : list A' :=
    match l with
    | nil => nil
    | cons a l => cons (map AR a) (F l)
    end.

Definition map_in_R_list (A A' : Type) (AR : Param2a0.Rel A A') :
  forall (l : list A) (l' : list A'), map_list A A' AR l = l' -> listR A A' AR l l' :=
    fun l l' e =>
      match e with
      | idpath =>
        (fix F l : listR A A' AR l (map_list A A' AR l) :=
          match l with
          | nil => nilR A A' AR
          | cons a l =>
            consR A A' AR
              a (map AR a) (map_in_R AR a (map AR a) idpath)
              l (map_list A A' AR l) (F l)
          end) l
      end.


Definition R_in_map_list (A A' : Type) (AR : Param2b0.Rel A A') :
  forall (l : list A) (l' : list A'), listR A A' AR l l' -> map_list A A' AR l = l' :=
    fix F l l' lR :=
      match lR with
      | nilR => idpath
      | consR a a' aR l l' lR =>
        match R_in_map AR a a' aR with
        | idpath =>
          match F l l' lR with
          | idpath => idpath
          end
        end
      end.

Definition Map2a_list (A A' : Type) (AR : Param2a0.Rel A A') : Map2a.Has (listR A A' AR).
Proof.
  unshelve econstructor.
  - exact (map_list A A' AR).
  - exact (map_in_R_list A A' AR).
Defined.

Definition Map2b_list (A A' : Type) (AR : Param2b0.Rel A A') : Map2b.Has (listR A A' AR).
Proof.
  unshelve econstructor.
  - exact (map_list A A' AR).
  - exact (R_in_map_list A A' AR).
Defined.

Definition Map3_list (A A' : Type) (AR : Param30.Rel A A') : Map3.Has (listR A A' AR).
Proof.
  unshelve econstructor.
  - exact (map_list A A' AR).
  - exact (map_in_R_list A A' AR).
  - exact (R_in_map_list A A' AR).
Defined.

Definition Map4_list (A A' : Type) (AR : Param40.Rel A A') : Map4.Has (listR A A' AR).
Proof.
  unshelve econstructor.
  - exact (map_list A A' AR).
  - exact (map_in_R_list A A' AR).
  - exact (R_in_map_list A A' AR).
  - move=> a b; elim => //= {}a {}a' aR l l' lR /=.
    elim: {2}_ / => //=.
    case:  _ / (R_in_map_list A A' AR l l' lR) => {l' lR}.
    rewrite -{2}[aR](R_in_mapK AR).
    by case: _ / (R_in_map AR a a' aR).
Qed.

Definition listR_flip (A A' : Type) (AR : A -> A' -> Type) :
  forall (l : list A) (l' : list A'), listR A A' AR l l' -> listR A' A (sym_rel AR) l' l :=
    fix F l l' lR :=
      match lR with
      | nilR => nilR A' A (sym_rel AR)
      | consR a a' aR l l' lR =>
        consR A' A (sym_rel AR) a' a aR l' l (F l l' lR)
      end.

Definition listR_flipK (A A' : Type) (AR : A -> A' -> Type) :
  forall (l : list A) (l' : list A') (lR : listR A A' AR l l'),
    listR_flip A' A (sym_rel AR) l' l (listR_flip A A' AR l l' lR) = lR :=
      fix F l l' lR :=
        match lR with
        | nilR => idpath
        | consR a a' aR l l' lR =>
          ap (fun lR => consR A A' AR a a' aR l l' lR) (F l l' lR)
        end.

Definition listR_sym (A A' : Type) (AR : A -> A' -> Type) :
  forall (l' : list A') (l : list A),
    listR A A' AR l l' <~> listR A' A (sym_rel AR) l' l.
Proof.
  intros l' l.
  unshelve econstructor.
  - exact (listR_flip A A' AR l l').
  - unshelve econstructor.
    + exact (listR_flip A' A (sym_rel AR) l' l).
    + exact (listR_flipK A' A (sym_rel AR) l' l).
    + exact (listR_flipK A A' AR l l').
    + intros lR.
      induction lR as [|a a' aR l l' lR IHlR]; simpl.
      * reflexivity.
      * rewrite IHlR.
        elim (listR_flipK A A' AR l l' lR).
        simpl. reflexivity.
Defined.

Definition Param00_list (A A' : Type) (AR : Param00.Rel A A') : Param00.Rel (list A) (list A').
Proof.
  unshelve econstructor.
  - exact (listR A A' AR).
  - constructor.
  - constructor.
Defined.

Definition Param42a_list (A A' : Type) (AR : Param42a.Rel A A') : Param42a.Rel (list A) (list A').
Proof.
  unshelve econstructor.
  - exact (listR A A' AR).
  - exact (Map4_list A A' AR).
  - refine (eq_Map2a _ _).
    + apply listR_sym.
    + exact (Map2a_list A' A (Param2a2a_sym _ _ AR)).
Defined.

Definition Param33_list (A A' : Type) (AR : Param33.Rel A A') : Param33.Rel (list A) (list A').
Proof.
  unshelve econstructor.
  - exact (listR A A' AR).
  - exact (Map3_list A A' AR).
  - refine (eq_Map3 _ _).
    + apply listR_sym.
    + exact (Map3_list A' A (Param33_sym _ _ AR)).
Defined.


Definition Param44_list (A A' : Type) (AR : Param44.Rel A A') : Param44.Rel (list A) (list A').
Proof.
  unshelve econstructor.
  - exact (listR A A' AR).
  - exact (Map4_list A A' AR).
  - refine (eq_Map4 _ _).
    + apply listR_sym.
    + exact (Map4_list A' A (Param44_sym _ _ AR)).
Defined.