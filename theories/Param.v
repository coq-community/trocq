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
From Coq Require Import ssreflect.
From HoTT Require Import HoTT.
Require Export Database.
Require Import HoTT_additions Hierarchy.
Require Export Param_Type Param_arrow Param_forall.

From Trocq.Elpi Extra Dependency "annot.elpi" as annot.
From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.
From Trocq.Elpi Extra Dependency "param.elpi" as param.
From Trocq.Elpi Extra Dependency "trocq.elpi" as trocq.
From Trocq.Elpi.constraints Extra Dependency "simple-graph.elpi" as simple_graph.
From Trocq.Elpi.constraints Extra Dependency "constraint-graph.elpi" as constraint_graph.
From Trocq.Elpi.constraints Extra Dependency "constraints.elpi" as constraints.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi Command genpparam.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.

(* generate
  PParamMN_Type P Q := ParamMN_TypePQ for all M N under 2b
  PParamMN_Type P Q := ParamMN_Type44 for all M N containing 2b+
*)

Elpi Command genpparamtype.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.
Elpi Accumulate lp:{{
  pred generate-branch i:univ-instance, i:param-class, i:param-class, o:term.
  generate-branch UI2 Class RClass (pglobal ParamType UI2) :-
    coq.locate
      {calc ("Param" ^ {param-class->string Class} ^ "_Type" ^ {param-class->string RClass})}
      ParamType.

  pred generate-match2
    i:term, i:univ-instance, i:param-class, i:term, i:map-class, o:term.
  generate-match2 RetType UI2 Class QVar P Match :-
    map-classes all Classes, std.map Classes
      (q\ b\ generate-branch UI2 Class (pc P q) b) Branches,
    coq.locate "map_class" MapClass,
    coq.univ-instance UI0 [],
    Match = (match QVar (fun `_` (pglobal MapClass UI0) _\ RetType) Branches).

  pred generate-match1
    i:term, i:univ-instance, i:param-class, i:term, i:term, o:term.
  generate-match1 RetType UI2 Class PVar QVar Match :-
    map-classes all Classes, std.map Classes
      (p\ b\ generate-match2 RetType UI2 Class QVar p b) Branches,
    coq.locate "map_class" MapClass,
    coq.univ-instance UI0 [],
    Match = (match PVar (fun `_` (pglobal MapClass UI0) _\ RetType) Branches).

  pred generate-pparam-type
    i:univ.variable, i:univ.variable, i:param-class.
  generate-pparam-type L L1 Class :-
    coq.locate {calc ("Param" ^ {param-class->string Class} ^ ".Rel")} ParamRel,
    coq.univ-instance UI1 [L1],
    RetType = app [pglobal ParamRel UI1, sort (typ U), sort (typ U)],
    coq.univ-instance UI2 [L, L1],
    (pi p q\ generate-match1 RetType UI2 Class p q (MatchF p q)),
    Decl = (fun `p` {{ map_class }} p\ fun `q` {{ map_class }} q\ MatchF p q),
    % this typecheck is very important: it adds L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    PParamType is "PParam" ^ {param-class->string Class} ^ "_Type",
    @udecl! [L, L1] ff [lt L L1] ff =>
      coq.env.add-const PParamType Decl _ @transparent! Const,
    coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.pparam-type Class Const)).
  
  pred generate-pparam-type44
    i:univ.variable, i:univ.variable, i:param-class.
  generate-pparam-type44 L L1 Class :-
    coq.univ-instance UI2 [L, L1],
    coq.locate {calc ("Param" ^ {param-class->string Class} ^ "_Type44")} ParamType,
    Decl = (fun `_` {{ map_class }} _\ fun `_` {{ map_class }} _\ pglobal ParamType UI2),
    % this typecheck is very important: it adds L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    PParamType is "PParam" ^ {param-class->string Class} ^ "_Type",
    @udecl! [L, L1] ff [lt L L1] ff =>
      coq.env.add-const PParamType Decl _ @transparent! Const,
    coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.pparam-type Class Const)).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.super U U1,
  coq.univ.variable U1 L1,
  map-classes low Classes1,
  map-classes high Classes2,
  map-classes all Classes,
  % first the ones where the arguments matter
  std.forall Classes1 (m\
    std.forall Classes1 (n\
      generate-pparam-type L L1 (pc m n)
    )
  ),
  % then the ones where the (4,4) relation is always returned
  std.forall Classes (m\
    std.forall Classes2 (n\
      generate-pparam-type44 L L1 (pc m n)
    )
  ),
  std.forall Classes2 (m\
    std.forall Classes1 (n\
      generate-pparam-type44 L L1 (pc m n)
    )
  ).
}}.

Elpi Tactic trocq.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File annot.
Elpi Accumulate File param_class.
Elpi Accumulate File simple_graph.
Elpi Accumulate File constraint_graph.
Elpi Accumulate File constraints.
Elpi Accumulate File param.
Elpi Accumulate File trocq.
Elpi Typecheck.

Elpi Accumulate lp:{{
  :before "coq-assign-evar"
  evar _ _ _ :- !.
}}.

Elpi Accumulate lp:{{
  solve InitialGoal NewGoals :- debug dbg.none => std.do! [
    InitialGoal = goal _Context _ G _ Args,
    util.when-debug dbg.full (coq.say "translating args" Args),
    std.map Args util.argument->gref GRArgs,
    util.when-debug dbg.full (coq.say "loading rels" GRArgs),
    trocq.load-rels GRArgs DB,
    util.when-debug dbg.full (coq.say "local DB" DB),
    util.when-debug dbg.full (coq.say "goal" G),
    translate-goal DB G (pc map0 map1) G' GR,
    util.when-debug dbg.full (coq.say "trocq:" G "~" G' "by" GR),
    FinalProof = {{ @comap lp:G lp:G' lp:GR (_ : lp:G') }},
    util.when-debug dbg.full (coq.say FinalProof),
    std.assert-ok! (coq.elaborate-skeleton FinalProof G EFinalProof) "proof elaboration error",
    std.assert-ok! (coq.typecheck EFinalProof G2) "proof typechecking error",
    std.assert-ok! (coq.unify-leq G2 G) "goal unification error",
    refine.no_check EFinalProof InitialGoal NewGoals
  ].

  pred translate-goal i:list prop, i:term, i:param-class, o:term, o:term.
  translate-goal DB G (pc M N) G' GR' :- DB => std.do! [
    cstr.init,
    T = (app [pglobal (const {trocq.db.ptype}) _, {map-class->term M}, {map-class->term N}]),
    % first annotate the initial goal with fresh parametricity class variables
    term->annot-term G AG,
    util.when-debug dbg.steps (
      coq.say "will translate" AG "at level" T,
      coq.say "***********************************************************************************"
    ),
    % generate the associated goal G' and witness GR
    param AG T G' GR,
    util.when-debug dbg.steps (
      coq.say "***********************************************************************************",
      coq.say "after translation:",
      coq.say "goal:" G',
      coq.say "proof:" GR,
      coq.say "***********************************************************************************"
    ),
    % reduce the graph, so the variables all become ground in the terms
    cstr.local-db DB,
    cstr.reduce-graph,
    % now we can remove the weaken placeholders and replace them with real weakening functions
    % or nothing if it is weaken α α
    param.subst-weaken GR GR',
    util.when-debug dbg.steps (
      coq.say "***********************************************************************************",
      coq.say "after reduction:",
      coq.say "goal:" {coq.term->string G'},
      coq.say "proof:" {coq.term->string GR'},
      coq.say "***********************************************************************************"
    )
    % no need to remove the remaining annotations because they are invisible modulo conversion
  ].
}}.
Elpi Typecheck.

Tactic Notation "trocq" ident_list(l) := elpi trocq ltac_string_list:(l).