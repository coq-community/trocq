(**************************************************************************************************)
(*                            *                               Trocq                               *)
(*  _______                   *                      Copyright (C) 2023 MERCE                     *)
(* |__   __|                  *               (Mitsubishi Electric R&D Centre Europe)             *)
(*    | |_ __ ___   ___ __ _  *                  Cyril Cohen <cyril.cohen@inria.fr>               *)
(*    | | '__/ _ \ / __/ _` | *                  Enzo Crance <enzo.crance@inria.fr>               *)
(*    | | | | (_) | (_| (_| | *              Assia Mahboubi <assia.mahboubi@inria.fr>             *)
(*    |_|_|  \___/ \___\__, | *********************************************************************)
(*                        | | *           This file is distributed under the terms of the         *)
(*                        |_| *             GNU Lesser General Public License Version 3           *)
(*                            *            (see LICENSE file for the text of the license)         *)
(**************************************************************************************************)

From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
Require Import HoTT_additions.
From elpi Require Import elpi.

(* included to remove Elpi typechecker warnings *)
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.

From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi Db param.db lp:{{
  pred param.db.r o:param-class, o:constant.
  :name "default-r"
  param.db.r C R :- var C, !,
    declare_constraint (param.db.r C R) [C].
  pred param.db.ptype o:constant.
  pred param.db.weaken o:constant.
  pred param.db.param-type o:param-class, o:param-class, o:constant.
  pred param.db.pparam-type o:param-class, o:constant.
  param.db.pparam-type C _ :- coq.say "pparam" C, fail.
  :name "default-pparam-type"
  param.db.pparam-type C PParamType :- var C, !,
    declare_constraint (param.db.pparam-type C PParamType) [C].
  pred param.db.param-arrow o:param-class, o:constant.
  param.db.param-arrow C _ :- coq.say "arrow" C, fail.
  :name "default-param-arrow"
  param.db.param-arrow C ParamArrow :- var C, !,
    declare_constraint (param.db.param-arrow C ParamArrow) [C].
  pred param.db.param-forall o:param-class, o:constant.
  param.db.param-forall C _ :- coq.say "forall" C, fail.
  :name "default-param-forall"
  param.db.param-forall C ParamForall :- var C, !,
    declare_constraint (param.db.param-forall C ParamForall) [C].
  pred param.db.univalence o:constant.
  :name "default-univalence"
  param.db.univalence _ :- coq.error "univalence axiom required".
  pred param.db.funext o:constant.
  :name "default-funext"
  param.db.funext _ :- coq.error "function extensionality axiom required".
  pred param.db.gref o:gref, o:param-class, o:list param-class, o:gref, o:gref.
  :name "default-gref"
  param.db.gref GR Out _ _ _ :- coq.error "cannot find" GR "at out class" Out.
}}.

Elpi Command Param.
Elpi Accumulate Db param.db.
Elpi Accumulate File util.
Elpi Accumulate File annot.
Elpi Accumulate File param_class.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints.
Elpi Typecheck.
Elpi Accumulate lp:{{
  main [str "Register", str "Univalence", str S] :- !, std.do! [
    std.assert! (coq.locate S GR) "unknown global reference",
    coq.univ-instance UI0 [],
    @uinstance! UI0 => coq.env.global GR U,
    coq.locate "Univalence" GRU,
    @uinstance! UI0 => coq.env.global GRU ExpectedUTy,
    coq.typecheck U UTy ok,
    std.assert-ok! (coq.unify-eq UTy ExpectedUTy) {std.string.concat "" [
      "type mismatch, expected ",
      {coq.term->string ExpectedUTy},
      ", got ",
      {coq.term->string UTy},
      "."
    ]},
    GR = const Const,
    coq.elpi.accumulate _ "param.db"
      (clause _ (before "default-univalence") (param.db.univalence Const)),
    coq.say "Univalence axiom successfully registered."
  ].
  
  main [str "Register", str "Funext", str S] :- !, std.do! [
    std.assert! (coq.locate S GR) "unknown global reference",
    coq.univ-instance UI0 [],
    @uinstance! UI0 => coq.env.global GR F,
    coq.locate "Funext" GRF,
    @uinstance! UI0 => coq.env.global GRF ExpectedFTy,
    coq.typecheck F FTy ok,
    std.assert-ok! (coq.unify-eq FTy ExpectedFTy) {std.string.concat "" [
      "type mismatch, expected ",
      {coq.term->string ExpectedFTy},
      ", got ",
      {coq.term->string FTy},
      "."
    ]},
    GR = const Const,
    coq.elpi.accumulate _ "param.db"
      (clause _ (before "default-funext") (param.db.funext Const)),
    coq.say "Function extensionality axiom successfully registered."
  ].

  main [str "Usage"] :- !, coq.say {usage-msg}.
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage:",
      "- Param Register Univalence <u>",
      "- Param Register Funext <f>",
      "", "",
    ] U.
}}.
Elpi Typecheck.
Elpi Export Param.
