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
From elpi Require Export elpi.
Require Import HoTT_additions.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Elpi Db trocq.db lp:{{

  % get various values of the ParamMN module from the (M,N) class
  % trocq.db.rel (pc M N) {{ParamMN.Rel}} {{ParamMN.BuildRel}}
  %   {{ParamMN.R}} {{ParamMN.covariant}} {{ParamMN.contravariant}}
  pred trocq.db.rel o:param-class, o:gref, o:gref,
    o:gref, o:gref, o:gref.

  pred trocq.db.r o:param-class, o:constant.
  :name "default-r"
  trocq.db.r C R :- var C, !,
    declare_constraint (trocq.db.r C R) [C].

  % subsummed by trocq.db.rel
  pred trocq.db.gref->class o:gref, o:param-class.

  % constants PType and Weaken registered so that we do not coq.locate every time
  pred trocq.db.ptype o:constant.
  pred trocq.db.pprop o:constant.
  pred trocq.db.weaken o:constant.

  pred trocq.db.ptype-or-pprop i:term, o:constant.
  trocq.db.ptype-or-pprop (pglobal (const PCst) _) PCst :- !,
    (trocq.db.ptype PCst; trocq.db.pprop PCst).

  % param-type β α {{ Param(β)_Type(α) }}
  % with α the level of the R field, and β the structure given to it
  pred trocq.db.param-type o:param-class, o:param-class, o:constant.

  % pparam-type (M,N) {{ PParamTypeMN }}
  % cf Param.v
  pred trocq.db.pparam-type o:param-class, o:constant.
  % first case always fails, just here for debug
  trocq.db.pparam-type C _ :-
    util.when-debug dbg.steps (coq.say "pparam" C), fail.
  :name "default-pparam-type"
  trocq.db.pparam-type C PParamType :- var C, !,
    declare_constraint (trocq.db.pparam-type C PParamType) [C].

  % param-arrow (M,N) {{ ParamArrowMN }}
  pred trocq.db.param-arrow o:param-class, o:constant.
  trocq.db.param-arrow C _ :-
    util.when-debug dbg.steps (coq.say "arrow" C), fail.
  :name "default-param-arrow"
  trocq.db.param-arrow C ParamArrow :- var C, !,
    declare_constraint (trocq.db.param-arrow C ParamArrow) [C].

  % param-forall (M,N) {{ ParamForallMN }}
  pred trocq.db.param-forall o:param-class, o:constant.
  trocq.db.param-forall C _ :-
    util.when-debug dbg.steps (coq.say "forall" C), fail.
  :name "default-param-forall"
  trocq.db.param-forall C ParamForall :- var C, !,
    declare_constraint (trocq.db.param-forall C ParamForall) [C].

  % dedicated databases to store the univalence/funext axioms
  % these predicates will be called every time an axiom is required
  % if an axiom has not been declared, the associated database is empty,
  % and the predicate fails to tell the user that translation cannot happen
  pred trocq.db.univalence o:constant.
  :name "default-univalence"
  trocq.db.univalence _ :- coq.error "univalence axiom required".

  pred trocq.db.funext o:constant.
  :name "default-funext"
  trocq.db.funext _ :- coq.error "function extensionality axiom required".

  % gref GR ω [α_1, ..., α_n] GR' GRR
  % GR related to GR' by witness GRR
  % ω is the output class of GRR
  % if GR is a type former then GRR : Param(ω) (GR ...) (GR' ...)
  % the α_i are the classes present in the type of GR, to give the dependency information
  % e.g. list44 : forall A A' (AR : Param44.Rel A A'), Param44.Rel (list A) (list A')
  %      gref {{ list }} (4, 4) [(4, 4)] {{ list }} {{ list44 }}
  pred trocq.db.gref o:gref, o:param-class, o:list param-class, o:gref, o:gref.
  :name "default-gref"
  trocq.db.gref _ _ _ _ _ :- do-not-fail, !, false.
  trocq.db.gref GR Out _ _ _ :- coq.error "cannot find" GR "at out class" Out.
}}.
