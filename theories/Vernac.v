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
From elpi Require Import elpi.
From Trocq Require Import HoTT_additions Hierarchy Param_Type Param_forall
  Param_arrow Database Param Param_paths.

 (* included to remove Elpi typechecker warnings *)
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.

From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.

Elpi Command Trocq.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File annot.
Elpi Accumulate File param_class.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints.
Elpi Typecheck.
Elpi Accumulate lp:{{
  % command to register the univalence axiom
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
    coq.elpi.accumulate _ "trocq.db"
      (clause _ (before "default-univalence") (trocq.db.univalence Const)),
    coq.say "Univalence axiom successfully registered."
  ].

  % command to register the funext axiom
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
    coq.elpi.accumulate _ "trocq.db"
      (clause _ (before "default-funext") (trocq.db.funext Const)),
    coq.say "Function extensionality axiom successfully registered."
  ].

  % command to add custom witnesses to the database

  main [str "Use", str X] :- !,
    coq.locate X GR, main [str "Use", trm (global GR)].

  main [str "Use", trm X] :- !, std.do! [
    coq.term->gref X GRR,
    coq.env.typeof GRR XTy,
    param-class.type->classes XTy Class CList GR GR',
    coq.say "accumultating" GR "@" Class "(" CList ") ~" GR' ":." GRR,
    coq.elpi.accumulate _ "trocq.db"
      (clause _ (before "default-gref")
        (trocq.db.gref GR Class CList GR' GRR)),
    std.forall {param-class.all-weakenings-from Class} subclass\
        sigma WTRR BaseName Suffix WName WCRR \
      if (do-not-fail => trocq.db.gref GR subclass _ _ _) true (std.do! [
        param-class.weaken-out subclass GRR WTRR,
        coq.gref->id GRR BaseName,
        param-class.to-string subclass Suffix,
        WName is BaseName ^ "_weakened_to_" ^ Suffix,
        @udecl! [] tt [] tt =>
          coq.env.add-const WName WTRR _ @transparent! WCRR,
        coq.elpi.accumulate _ "trocq.db"
          (clause _ (before "default-gref")
            (trocq.db.gref GR subclass CList GR' (const WCRR))),
        coq.say "accumultating" GR "@" subclass "(" CList ") ~" GR'
          ":." (const WCRR),
    ])
  ].
  % coq.elpi.accumulate _ "trocq.db"
  %   (clause _ (before "default-gref")
  %     (trocq.db.gref GR (pc map4 map2b) [] {{:gref int}} {{:gref Rp42b}})),

  % serveral use in one go!
  main [str "Use", X, Y | Rest] :- !, std.do![
      main [str "Use", X], main [str "Use", Y | Rest]].

  main [str "Usage"] :- !, coq.say {usage-msg}.
  main _ :- coq.error {std.string.concat "\n" ["command syntax error", {usage-msg}]}.

  pred usage-msg o:string.
  usage-msg U :-
    std.string.concat "\n" [
      "usage:",
      "- Trocq Register Univalence <u>",
      "- Trocq Register Funext <f>",
      "- Trocq Use <RTrocq>",
      "", "",
    ] U.
}}.
Elpi Typecheck.
Elpi Export Trocq.
