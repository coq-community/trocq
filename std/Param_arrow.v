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

From elpi Require Import elpi.
Require Import ssreflect.
Require Import Stdlib Hierarchy Database Param_lemmas.

From Trocq.Elpi.generation Extra Dependency "param-arrow.elpi" as param_arrow_generation.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Import HoTTNotations.
Local Open Scope param_scope.

(* relation for arrow *)

Definition R_arrow@{i j}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param00.Rel@{j} B B') :=
    fun f f' => forall a a', PA a a' -> PB (f a) (f' a').

(* MapN for arrow *)

(* (00, 00) -> 00 *)
Definition Map0_arrow@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param00.Rel@{j} B B') :
    Map0.Has@{k} (R_arrow PA PB).
Proof. exists. Defined.

(* (01, 10) -> 10 *)
Definition Map1_arrow@{i j k}
  {A A' : Type@{i}} (PA : Param01.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param10.Rel@{j} B B') :
    Map1.Has@{k} (R_arrow PA PB).
Proof.
  exists; exact (fun f a' => map PB (f (comap PA a'))).
Defined.

(* (02b, 2a0) -> 2a0 *)
Definition Map2a_arrow@{i j k}
  {A A' : Type@{i}} (PA : Param02b.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param2a0.Rel@{j} B B') :
    Map2a.Has@{k} (R_arrow PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_arrow@{i j k} PA PB)).
  move=> f f' /= e a a' aR; apply (map_in_R@{j} PB).
  apply (transport@{k j} (fun t => _ = t a') e) => /=.
  by apply (transport@{i j} (fun t => _ = map _ (f t))
     (R_in_comap@{i} PA _ _ aR)^).
Defined.

(* (02a, 2b0) + funext -> 2b0 *)
Definition Map2b_arrow@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param2b0.Rel@{j} B B') :
    Map2b.Has@{k} (R_arrow PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_arrow PA PB)).
  move=> f f' /= fR; apply path_forall => a'.
  by apply (R_in_map PB); apply fR; apply (comap_in_R PA).
Defined.

(* (03, 30) + funext -> 30 *)
Definition Map3_arrow@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param03.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param30.Rel@{j} B B') :
    Map3.Has@{k} (R_arrow PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_arrow PA PB)).
  - exact: (Map2a.map_in_R _ (Map2a_arrow PA PB)).
  - move=> f f' /= fR; apply path_arrow => a'.
    by apply (R_in_map PB); apply fR; apply (comap_in_R PA).
Defined.

(* (04, 40) + funext -> 40 *)
Definition Map4_arrow@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B B' : Type@{j}} (PB : Param40.Rel@{j} B B') :
    Map4.Has@{k} (R_arrow PA PB).
Proof.
  exists
    (Map1.map@{k} _ (Map1_arrow PA PB))
    (Map2a.map_in_R _ (Map2a_arrow PA PB))
    (Map2b.R_in_map _ (Map2b_arrow PA PB)).
  (***)
  move=> f f' fR /=.
  apply path_forall@{i k} => a.
  apply path_forall@{i k} => a'.
  apply path_arrow@{i k} => aR /=.
  rewrite -[in X in _ = X](R_in_comapK PA a' a aR).
  set t := (R_in_comap PA a' a aR).
  dependent inversion t.
  rewrite transport_apD10@{i j j k} /=.
  rewrite apD10_path_forall_cancel/=.
  rewrite <- (R_in_mapK PB).
  set u := (R_in_map _ _ _ _).
  by dependent inversion u.
Defined.

(* Param_arrowMN : forall A A' AR B B' BR, ParamMN.Rel (A -> B) (A' -> B') *)

Elpi Command genparamarrow.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_arrow_generation.
Elpi Query lp:{{
  coq.univ.new Ui,
  coq.univ.variable Ui Li,
  coq.univ.new Uj,
  coq.univ.variable Uj Lj,
  coq.univ.alg-max Ui Uj Uk,
  % cannot have only 2 binders in the declaration because this line creates a fresh level:
  coq.univ.variable Uk Lk,
  map-class.all-of-kind all Classes,
  std.forall Classes (m\
    std.forall Classes (n\
      generate-param-arrow (pc m n) Ui Uj Li Lj Lk
    )
  ).
}}.
