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
From elpi Require Export elpi.
Require Import HoTT_additions.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi Db trocq.db lp:{{
  pred trocq.db.r o:param-class, o:constant.
  :name "default-r"
  trocq.db.r C R :- var C, !,
    declare_constraint (trocq.db.r C R) [C].

  pred trocq.db.gref->class o:gref, o:param-class.

  pred trocq.db.ptype o:constant.

  pred trocq.db.weaken o:constant.

  pred trocq.db.param-type o:param-class, o:param-class, o:constant.

  pred trocq.db.pparam-type o:param-class, o:constant.
  trocq.db.pparam-type C _ :-
    util.when-debug dbg.steps (coq.say "pparam" C), fail.
  :name "default-pparam-type"
  trocq.db.pparam-type C PParamType :- var C, !,
    declare_constraint (trocq.db.pparam-type C PParamType) [C].

  pred trocq.db.param-arrow o:param-class, o:constant.
  trocq.db.param-arrow C _ :-
    util.when-debug dbg.steps (coq.say "arrow" C), fail.
  :name "default-param-arrow"
  trocq.db.param-arrow C ParamArrow :- var C, !,
    declare_constraint (trocq.db.param-arrow C ParamArrow) [C].

  pred trocq.db.param-forall o:param-class, o:constant.
  trocq.db.param-forall C _ :-
    util.when-debug dbg.steps (coq.say "forall" C), fail.
  :name "default-param-forall"
  trocq.db.param-forall C ParamForall :- var C, !,
    declare_constraint (trocq.db.param-forall C ParamForall) [C].

  pred trocq.db.univalence o:constant.
  :name "default-univalence"
  trocq.db.univalence _ :- coq.error "univalence axiom required".

  pred trocq.db.funext o:constant.
  :name "default-funext"
  trocq.db.funext _ :- coq.error "function extensionality axiom required".

  pred trocq.db.gref o:gref, o:param-class, o:list param-class, o:gref, o:gref.
  :name "default-gref"
  trocq.db.gref GR Out _ _ _ :- coq.error "cannot find" GR "at out class" Out.
}}.
