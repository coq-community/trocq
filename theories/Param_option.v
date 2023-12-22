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

Notation Unit := unit.
Notation none := None.

Inductive optionR (A A' : Type) (AR : A -> A' -> Type) :
  option A -> option A' -> Type :=
    | someR :
      forall (a : A) (a' : A'), AR a a' ->
        optionR A A' AR (Some a) (Some a')
    | noneR : optionR A A' AR None None.

Definition option_map :
forall (A A' : Type) (AR : Param10.Rel A A'), option A -> option A' :=
  fun A A' AR =>
    fun oa =>
      match oa in option _ return option A' with
      | Some a => Some (map AR a)
      | None => None
      end.

Definition some_inj1 :
forall (A : Type) (a1 a2 : A), Some a1 = Some a2 -> a1 = a2 :=
  fun A a1 a2 e =>
    let proj1 (oa : option A) :=
      match oa with
      | Some a => a
      | None => a1
      end
    in ap proj1 e.

Definition exfalso_option_some_none :
  forall (T : Type) (A : Type) (a : A), Some a = None -> T :=
    fun T A a e =>
      match e in @paths _ _ t
      return
        match t with
        | Some _ => Unit
        | _ => T
        end
      with
      | idpath => tt
      end.

Definition exfalso_option_none_some :
  forall (T : Type) (A : Type) (a : A), None = Some a -> T :=
    fun T A a e =>
      match e in @paths _ _ t
      return
        match t with
        | None => Unit
        | Some _ => T
        end
      with
      | idpath => tt
      end.

Definition option_map_in_R :
  forall (A A' : Type) (AR : Param2a0.Rel A A')
         (oa : option A) (oa' : option A'),
    option_map A A' AR oa = oa' -> optionR A A' AR oa oa' :=
  fun A A' AR =>
    fun oa oa' =>
      match oa with
      | Some a =>
        match oa' with
        | Some a' =>
          fun e =>
            someR A A' AR a a' (map_in_R AR a a' (some_inj1 A' (map AR a) a' e))
        | none =>
          fun e =>
            exfalso_option_some_none (optionR A A' AR (Some a) (None))
              A' (map AR a) e
        end
      | none =>
        match oa' with
        | Some a' =>
          fun e =>
            exfalso_option_none_some (optionR A A' AR (None) (Some a'))
              A' a' e
        | none => fun e => noneR A A' AR
        end
      end.


Definition option_R_in_map :
  forall (A A' : Type) (AR : Param2b0.Rel A A')
         (oa : option A) (oa' : option A'),
    optionR A A' AR oa oa' -> option_map A A' AR oa = oa'
    :=
  fun A A' AR =>
    fun oa oa' oaR =>
      match oaR in optionR _ _ _ oa oa' return option_map A A' AR oa = oa' with
      | @someR _ _ _ a a' aR =>
        @transport A' (fun t => Some t = Some a')
          a' (map AR a) (R_in_map AR a a' aR)^
            idpath
      | @noneR _ _ _ => idpath
      end.

Definition option_R_in_mapK :
  forall (A A' : Type) (AR : Param40.Rel A A')
         (oa : option A) (oa' : option A') (oaR : optionR A A' AR oa oa'),
    option_map_in_R A A' AR oa oa' (option_R_in_map A A' AR oa oa' oaR) = oaR.
Proof.
Admitted.