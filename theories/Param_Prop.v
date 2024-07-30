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

From elpi Require Import elpi.
From Coq Require Import ssreflect.
Require Import HoTT_additions Hierarchy Database.
From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.
From Trocq.Elpi Extra Dependency "util.elpi" as util.

Set Warnings "+elpi.typecheck".
Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(* generate MapM_PropNP@{i} :
    MapM.Has Prop@{i} Prop@{i} ParamNP.Rel@{i},
  for all N P, for M = map2a and below (above, NP is always 44)
  + symmetry MapM_Prop_symNP *)

Elpi Command genmapprop.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.
Elpi Accumulate File util.
Elpi Accumulate lp:{{
  pred generate-fields
    i:map-class, i:term, i:param-class, o:list term.
  generate-fields map0 R _ [R].
  generate-fields map1 R _ [R, Map] :-
    Map = (fun `T` (sort prop) t\ t).
  generate-fields map2a R RClass [R, Map, MapInR] :- std.do! [
    Prop = sort prop,
    Map = (fun `T` Prop t\ t),
    (pi a\ coq.mk-app R [a] (RF a)),
    coq.locate "paths" Paths,
    coq.locate "transport" Transport,
    coq.locate {calc ("id_Param" ^ {param-class->string RClass})} IdParam,
    coq.env.global Transport TransportTm,
    coq.env.global IdParam IdParamTm,
    MapInR =
      (fun `A` Prop a\ fun `B` Prop b\
        fun `e` (app [global Paths, Prop, a, b]) e\
          app [TransportTm, Prop, RF a, a, b,
            e, app [IdParamTm, a]])
  ].

  pred generate-map-prop i:map-class, i:param-class.
  generate-map-prop M RClass :- std.do! [
    coq.locate {calc ("Param" ^ {param-class->string RClass} ^ ".Rel")} R,
    Prop = sort prop,
    coq.env.global R RTm,
    % RTm = {{fun A B : Prop => lp:RTmNoEta A B}},
    generate-fields M RTm RClass Fields,
    coq.locate "sym_rel" SymRel,
    coq.env.global SymRel SymRelTm,
    generate-fields
      M (app [SymRelTm, Prop, Prop, RTm])
      RClass FieldsSym,
    coq.locate {calc ("Map" ^ {map-class->string M} ^ ".BuildHas")} BuildHas,
    coq.env.global BuildHas BuildHasTm,
    coq.mk-app BuildHasTm [Prop, Prop | Fields] Decl,
    coq.mk-app BuildHasTm [Prop, Prop | FieldsSym] DeclSym,
    MapProp is
      "Map" ^ {map-class->string M} ^ "_Prop" ^ {param-class->string RClass},
    MapPropSym is
      "Map" ^ {map-class->string M} ^ "_Prop_sym" ^
      {param-class->string RClass},
    % these typechecks are very important: they add L < L1 to the constraint graph
    std.assert-ok! (coq.elaborate-skeleton Decl _Ty Decl')
      "generate-map-prop: Decl cannot be elaborated",
    std.assert-ok! (coq.elaborate-skeleton DeclSym _Ty' DeclSym')
      "generate-map-prop: Decl cannot be elaborated",
    % std.assert-ok! (coq.typecheck Decl _)
    %    "generate-map-prop: Decl ill-typed",
    % std.assert-ok! (coq.typecheck DeclSym _)
    %    "generate-map-prop: DeclSym ill-typed",
    @udecl! [] tt [] tt =>
      coq.env.add-const MapProp Decl' _ @transparent! _,
    @udecl!  [] tt [] tt =>
      coq.env.add-const MapPropSym DeclSym' _ @transparent! _
  ].
}}.
Elpi Typecheck.

Set Printing Universes.
Set Printing All.
Print Param00.Rel.
Eval compute in (@Map0.BuildHas Prop Prop (@Param00.Rel)).

Elpi Query lp:{{
  % cannot have only one binder in the declaration because this line creates a fresh level:
  map-classes all Classes,
  map-classes low LowClasses,
  std.forall LowClasses (m\
    std.forall Classes (n\
      std.forall Classes (p\
        generate-map-prop m (pc n p)
      )
    )
  ).
}}.


(* Elpi Command genparamtype.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File util.
Elpi Accumulate File param_class.
Elpi Accumulate lp:{{
  pred generate-param-type
    i:param-class, i:param-class, i:univ, i:univ.variable, i:univ.variable.
  generate-param-type (pc M N as Class) RClass U L L1 :-
    map-class->string M MStr,
    map-class->string N NStr,
    coq.univ-instance UI [L],
    coq.univ-instance UI1 [L1],
    coq.univ-instance UI2 [L, L1],
    coq.locate {calc ("Param" ^ MStr ^ NStr ^ ".BuildRel")} BuildRel,
    coq.locate
      {calc ("Map" ^ MStr ^ "_Prop" ^ {param-class->string RClass})} MapProp,
    coq.locate
      {calc ("Map" ^ NStr ^ "_Prop_sym" ^ {param-class->string RClass})}
      MapPropSym,
    coq.locate {calc ("Param" ^ {param-class->string RClass} ^ ".Rel")} R,
    if (std.mem! [map2b, map3, map4] M) (
      UnivalentDecl = true,
      MapPropF = (u\ app [pglobal MapProp UI2, u]),
      if (std.mem! [map2b, map3, map4] N)
        (MapPropSymF = (u\ app [pglobal MapPropSym UI2, u]))
        (MapPropSymF = (_\ pglobal MapPropSym UI2))
    ) (
      MapPropF = (_\ pglobal MapProp UI2),
      if (std.mem! [map2b, map3, map4] N) (
        MapPropSymF = (u\ app [pglobal MapPropSym UI2, u]),
        UnivalentDecl = true
      ) (
        MapPropSymF = (_\ pglobal MapPropSym UI2),
        UnivalentDecl = false
      )
    ),
    % in the univalent case, add the axiom in the binder
    if (UnivalentDecl) (
      coq.locate "Univalence" Univalence,
      Decl =
        (fun `H` (global Univalence) u\
          app [pglobal BuildRel UI1, sort prop, sort prop, pglobal R UI,
            MapPropF u, MapPropSymF u])
    ) (
      Dummy = (fun `x` (sort prop) x\ x),
      Decl =
        app [pglobal BuildRel UI1, sort prop, sort prop, pglobal R UI,
          MapPropF Dummy, MapPropSymF Dummy]
    ),
    ParamProp is "Param" ^ MStr ^ NStr ^ "_Prop" ^ {param-class->string RClass},
    % this typecheck is very important: it adds L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    @udecl! [L, L1] ff [lt L L1] tt =>
      coq.env.add-const ParamProp Decl _ @transparent! Const,
    coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.param-type Class RClass Const)).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.super U U1,
  % cannot have only one binder in the declaration because this line creates a fresh level:
  coq.univ.variable U1 L1,
  AllClasses = [map0, map1, map2a, map2b, map3, map4],
  Classes__ = [map0, map1, map2a],
  std.forall Classes__ (m\
    std.forall Classes__ (n\
      std.forall AllClasses (p\
        std.forall AllClasses (q\
          generate-param-type (pc m n) (pc p q) U L L1
        )
      )
    )
  ).
}}.
(* 
 Set Printing Universes. About Param00_Prop40.
Set Printing Universes. Print Param12a_Prop31.
Set Printing Universes. About Param30_Prop44.
Set Printing Universes. Print Param44_Prop44. *) *)
