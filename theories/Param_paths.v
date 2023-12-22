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

Inductive pathsR@{i}
  (A A' : Type@{i}) (AR : A -> A' -> Type@{i}) (x : A) (x' : A') (xR : AR x x') :
  forall (y : A) (y' : A') (yR : AR y y'), x = y -> x' = y' -> Type@{i} :=
    | idpathR : pathsR A A' AR x x' xR x x' xR idpath idpath.

Definition paths_map@{i}
  (A A' : Type@{i}) (AR : Param2b0.Rel@{i} A A')
  (x : A) (x' : A') (xR : AR x x')
  (y : A) (y' : A') (yR : AR y y') :
    x = y -> x' = y' :=
  fun e => (R_in_map AR x x' xR)^ @ ap (map AR) e @ (R_in_map AR y y' yR).

Definition paths_map_in_R@{i}
  (A A' : Type@{i}) (AR : Param40.Rel@{i} A A')
  (x : A) (x' : A') (xR : AR x x')
  (y : A) (y' : A') (yR : AR y y') :
    forall (e : x = y) (e' : x' = y'),
      paths_map A A' AR x x' xR y y' yR e = e' -> pathsR A A' AR x x' xR y y' yR e e'.
Proof.
  intros e e'.
  destruct e.
  destruct e'.
  exact (fun H =>
    transport (fun t => pathsR A A' AR x x' xR x x' t 1%path 1%path)
      ((R_in_mapK AR x x' xR)^ @
        ap (map_in_R AR x x')
          ((inv_V (R_in_map AR x x' xR))^ @
            inverse2
              ((concat_p1 (R_in_map AR x x' xR)^)^ @
                (moveL_1V ((R_in_map AR x x' xR)^ @ 1) (R_in_map AR x x' yR) H))
            @ (inv_V (R_in_map AR x x' yR)))
        @ (R_in_mapK AR x x' yR))
      (idpathR A A' AR x x' xR)).
Defined.

Definition paths_R_in_map@{i}
  (A A' : Type@{i}) (AR : Param2b0.Rel@{i} A A')
  (x : A) (x' : A') (xR : AR x x')
  (y : A) (y' : A') (yR : AR y y') :
    forall (e : x = y) (e' : x' = y'),
      pathsR A A' AR x x' xR y y' yR e e' -> paths_map A A' AR x x' xR y y' yR e = e'.
Proof.
  intros e e' r.
  destruct r.
  unfold paths_map.
  simpl.
  apply moveR_pM.
  unshelve refine (concat _ _).
  - exact (R_in_map AR x x' xR)^.
  - apply concat_p1.
  - apply inverse. apply concat_1p.
Defined.

Set Printing Universes.

Definition paths_R_in_mapK@{i}
  (A A' : Type@{i}) (AR : Param40.Rel@{i} A A')
  (x : A) (x' : A') (xR : AR x x')
  (y : A) (y' : A') (yR : AR y y') :
    forall (e : x = y) (e' : x' = y') u,
    paths_map_in_R@{i} A A' AR x x' xR y y' yR e e'
        (paths_R_in_map@{i} A A' AR x x' xR y y' yR e e' u) = u.
Proof.
  intros e e' r.
  destruct r.
  simpl.
  elim (R_in_mapK AR x x' xR).
  simpl.
Admitted.

Definition Map0_paths
  A A' (AR : Param00.Rel A A') (x : A) (x' : A') (xR : AR x x')(y : A) (y' : A') (yR : AR y y') :
    Map0.Has (pathsR A A' AR x x' xR y y' yR).
Proof. constructor. Defined.

Definition Map1_paths
  A A' (AR : Param2b0.Rel A A') (x : A) (x' : A') (xR : AR x x')(y : A) (y' : A') (yR : AR y y') :
    Map1.Has (pathsR A A' AR x x' xR y y' yR).
Proof. constructor. exact (paths_map A A' AR x x' xR y y' yR). Defined.

Definition Map2a_paths
  A A' (AR : Param40.Rel A A') (x : A) (x' : A') (xR : AR x x')(y : A) (y' : A') (yR : AR y y') :
    Map2a.Has (pathsR A A' AR x x' xR y y' yR).
Proof.
  unshelve econstructor.
  - exact (paths_map A A' AR x x' xR y y' yR).
  - exact (paths_map_in_R A A' AR x x' xR y y' yR).
Defined.

Definition Map2b_paths
  A A' (AR : Param2b0.Rel A A') (x : A) (x' : A') (xR : AR x x')(y : A) (y' : A') (yR : AR y y') :
    Map2b.Has (pathsR A A' AR x x' xR y y' yR).
Proof.
  unshelve econstructor.
  - exact (paths_map A A' AR x x' xR y y' yR).
  - exact (paths_R_in_map A A' AR x x' xR y y' yR).
Defined.

Definition Map3_paths
  A A' (AR : Param40.Rel A A') (x : A) (x' : A') (xR : AR x x')(y : A) (y' : A') (yR : AR y y') :
    Map3.Has (pathsR A A' AR x x' xR y y' yR).
Proof.
  unshelve econstructor.
  - exact (paths_map A A' AR x x' xR y y' yR).
  - exact (paths_map_in_R A A' AR x x' xR y y' yR).
  - exact (paths_R_in_map A A' AR x x' xR y y' yR).
Defined.

Definition Map4_paths
  A A' (AR : Param40.Rel A A') (x : A) (x' : A') (xR : AR x x')(y : A) (y' : A') (yR : AR y y') :
    Map4.Has (pathsR A A' AR x x' xR y y' yR).
Proof.
  unshelve econstructor.
  - exact (paths_map A A' AR x x' xR y y' yR).
  - exact (paths_map_in_R A A' AR x x' xR y y' yR).
  - exact (paths_R_in_map A A' AR x x' xR y y' yR).
  - exact (paths_R_in_mapK A A' AR x x' xR y y' yR).
Defined.

Definition pathsR_sym@{i} :
  forall (A A' : Type@{i}) (AR : Param01.Rel@{i} A A')
         (a1 : A) (a1' : A') (a1R : AR a1 a1') (a2 : A) (a2' : A') (a2R : AR a2 a2')
         (e' : a1' = a2') (e : a1 = a2),
    sym_rel (pathsR A A' AR a1 a1' a1R a2 a2' a2R) e' e <->>
    pathsR A' A (sym_rel AR) a1' a1 a1R a2' a2 a2R e' e.
Proof.
  intros A A' AR a1 a1' a1R a2 a2' a2R e' e.
  unshelve econstructor.
  - intros []; apply idpathR.
  - unshelve econstructor.
    + intros []; apply idpathR.
    + intros []; reflexivity.
Defined.

Definition Param01_paths@{i}
  (A A' : Type@{i}) (AR : Param02b.Rel@{i} A A')
  (a1 : A) (a1' : A') (a1R : AR a1 a1') (a2 : A) (a2' : A') (a2R : AR a2 a2') :
    Param01.Rel@{i} (a1 = a2) (a1' = a2').
Proof.
  unshelve econstructor.
  - exact (pathsR A A' AR a1 a1' a1R a2 a2' a2R).
  - exact (Map0_paths A A' AR a1 a1' a1R a2 a2' a2R).
  - apply (@eq_Map1 _ _ _ _ (pathsR_sym A A' AR a1 a1' a1R a2 a2' a2R)).
    exact (Map1_paths A' A (Param02b_sym A A' AR) a1' a1 a1R a2' a2 a2R).
Defined.

Definition Param10_paths@{i}
  (A A' : Type@{i}) (AR : Param2b0.Rel@{i} A A')
  (a1 : A) (a1' : A') (a1R : AR a1 a1') (a2 : A) (a2' : A') (a2R : AR a2 a2') :
    Param10.Rel@{i} (a1 = a2) (a1' = a2').
Proof.
  unshelve econstructor.
  - exact (pathsR A A' AR a1 a1' a1R a2 a2' a2R).
  - exact (Map1_paths A A' AR a1 a1' a1R a2 a2' a2R).
  - constructor.
Defined.

(* todo generator *)
