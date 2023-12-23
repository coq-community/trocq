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
Require Import HoTT_additions Hierarchy Database.
From Trocq.Elpi Extra Dependency "util.elpi" as util.
From Trocq.Elpi Extra Dependency "param-class.elpi" as param_class.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

(* generate MapM_TypeNP@{i} :
    MapM.Has Type@{i} Type@{i} ParamNP.Rel@{i},
  for all N P, for M = map2a and below (above, NP is always 44)
  + symmetry MapM_Type_symNP *)

Elpi Command genmaptype.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.
Elpi Accumulate lp:{{
  pred generate-fields
    i:map-class, i:term, i:param-class, i:univ,
    i:univ.variable, i:univ.variable, o:list term.
  generate-fields map0 R _ _ _ _ [R].
  generate-fields map1 R _ U _ _ [R, Map] :-
    Map = (fun `T` (sort (typ U)) t\ t).
  generate-fields map2a R RClass U L L1 [R, Map, MapInR] :-
    Type = sort (typ U),
    coq.univ-instance UI [L],
    coq.univ-instance UI1 [L1],
    coq.univ-instance UI11 [L1, L1],
    Map = (fun `T` Type t\ t),
    (pi a\ coq.mk-app R [a] (RF a)),
    coq.locate "paths" Paths,
    coq.locate "transport" Transport,
    coq.locate {calc ("id_Param" ^ {param-class->string RClass})} IdParam,
    MapInR =
      (fun `A` Type a\ fun `B` Type b\
        fun `e` (app [pglobal Paths UI1, Type, a, b]) e\
          app [pglobal Transport UI11, Type, RF a, a, b,
            e, app [pglobal IdParam UI, a]]).

  pred generate-map-type
    i:map-class, i:param-class, i:univ, i:univ.variable, i:univ.variable.
  generate-map-type M RClass U L L1 :-
    coq.locate {calc ("Param" ^ {param-class->string RClass} ^ ".Rel")} R,
    Type = sort (typ U),
    coq.univ-instance UI [L],
    coq.univ-instance UI1 [L1],
    generate-fields M (pglobal R UI) RClass U L L1 Fields,
    coq.locate "sym_rel" SymRel,
    generate-fields
      M (app [pglobal SymRel UI1, Type, Type, pglobal R UI])
      RClass U L L1 FieldsSym,
    coq.locate {calc ("Map" ^ {map-class->string M} ^ ".BuildHas")} BuildHas,
    Decl = app [pglobal BuildHas UI1, Type, Type | Fields],
    DeclSym = app [pglobal BuildHas UI1, Type, Type | FieldsSym],
    MapType is
      "Map" ^ {map-class->string M} ^ "_Type" ^ {param-class->string RClass},
    MapTypeSym is
      "Map" ^ {map-class->string M} ^ "_Type_sym" ^
      {param-class->string RClass},
    % these typechecks are very important: they add L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    coq.typecheck DeclSym _ ok,
    @udecl! [L, L1] ff [lt L L1] ff =>
      coq.env.add-const MapType Decl _ @transparent! _,
    @udecl! [L, L1] ff [lt L L1] ff =>
      coq.env.add-const MapTypeSym DeclSym _ @transparent! _.
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.super U U1,
  % cannot have only one binder in the declaration because this line creates a fresh level:
  coq.univ.variable U1 L1,
  map-classes all Classes,
  map-classes low LowClasses,
  std.forall LowClasses (m\
    std.forall Classes (n\
      std.forall Classes (p\
        generate-map-type m (pc n p) U L L1
      )
    )
  ).
}}.

(* Check Map0_Type01.
Check Map1_Type_sym32b.
Check Map2a_Type44. *)

(* now R is always Param44.Rel *)

Definition Map2b_Type44@{i j | i < j} `{Univalence} :
  @Map2b.Has@{j} Type@{i} Type@{i} Param44.Rel@{i}.
Proof.
  unshelve econstructor.
  - exact idmap.
  - move=> A B /uparam_equiv. apply: path_universe_uncurried.
Defined.

Definition Map2b_Type_sym44@{i j | i < j} `{Univalence} :
  @Map2b.Has@{j} Type@{i} Type@{i} (sym_rel@{j} Param44.Rel@{i}).
Proof.
  unshelve econstructor.
  - exact idmap.
  - move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact.
Defined.

Definition Map3_Type44@{i j | i < j} `{Univalence} :
  @Map3.Has@{j} Type@{i} Type@{i} Param44.Rel@{i}.
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv. apply: path_universe_uncurried.
Defined.

Definition Map3_Type_sym44@{i j | i < j} `{Univalence} :
  @Map3.Has@{j} Type@{i} Type@{i} (sym_rel@{j} Param44.Rel@{i}).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact.
Defined.

Definition Map4_Type44@{i j | i < j} `{Univalence} :
  @Map4.Has@{j} Type@{i} Type@{i} Param44.Rel@{i}.
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv. apply: path_universe_uncurried.
  - move=> A B; elim/uparam_induction.
    by rewrite uparam_equiv_id /= [path_universe_uncurried _] path_universe_1.
Defined.

Definition Map4_Type_sym44@{i j | i < j} `{Univalence} :
  @Map4.Has@{j} Type@{i} Type@{i} (sym_rel@{j} Param44.Rel@{i}).
Proof.
  unshelve econstructor.
  - exact idmap.
  - exact (fun A B e => e # id_Param44 A).
  - move=> A B /uparam_equiv /path_universe_uncurried /inverse. exact.
  - move=> A B; elim/uparam_induction.
    by rewrite uparam_equiv_id /= [path_universe_uncurried _] path_universe_1.
Defined.

(* generate ParamMN_TypePQ@{i} :
    ParamMN.Rel Type@{i} Type@{i},
  for all M N, having ParamPQ.Rel as the R field
  (for M or N in [2b, 3, 4] PQ is always 44) *)

Elpi Command genparamtype.
Elpi Accumulate File util.
Elpi Accumulate Db trocq.db.
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
      {calc ("Map" ^ MStr ^ "_Type" ^ {param-class->string RClass})} MapType,
    coq.locate
      {calc ("Map" ^ NStr ^ "_Type_sym" ^ {param-class->string RClass})}
      MapTypeSym,
    coq.locate {calc ("Param" ^ {param-class->string RClass} ^ ".Rel")} R,
    if (std.mem! [map2b, map3, map4] M) (
      UnivalentDecl = true,
      MapTypeF = (u\ app [pglobal MapType UI2, u]),
      if (std.mem! [map2b, map3, map4] N)
        (MapTypeSymF = (u\ app [pglobal MapTypeSym UI2, u]))
        (MapTypeSymF = (_\ pglobal MapTypeSym UI2))
    ) (
      MapTypeF = (_\ pglobal MapType UI2),
      if (std.mem! [map2b, map3, map4] N) (
        MapTypeSymF = (u\ app [pglobal MapTypeSym UI2, u]),
        UnivalentDecl = true
      ) (
        MapTypeSymF = (_\ pglobal MapTypeSym UI2),
        UnivalentDecl = false
      )
    ),
    % in the univalent case, add the axiom in the binder
    if (UnivalentDecl) (
      coq.locate "Univalence" Univalence,
      Decl =
        (fun `H` (global Univalence) u\
          app [pglobal BuildRel UI1, sort (typ U), sort (typ U), pglobal R UI,
            MapTypeF u, MapTypeSymF u])
    ) (
      Dummy = (fun `x` (sort (typ U)) x\ x),
      Decl =
        app [pglobal BuildRel UI1, sort (typ U), sort (typ U), pglobal R UI,
          MapTypeF Dummy, MapTypeSymF Dummy]
    ),
    ParamType is "Param" ^ MStr ^ NStr ^ "_Type" ^ {param-class->string RClass},
    % this typecheck is very important: it adds L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    @udecl! [L, L1] ff [lt L L1] ff =>
      coq.env.add-const ParamType Decl _ @transparent! Const,
    coq.elpi.accumulate _ "trocq.db" (clause _ _ (trocq.db.param-type Class RClass Const)).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ.super U U1,
  % cannot have only one binder in the declaration because this line creates a fresh level:
  coq.univ.variable U1 L1,
  map-classes all AllClasses,
  map-classes low Classes__,
  map-classes high Classes44,
  std.forall Classes__ (m\
    std.forall Classes__ (n\
      std.forall AllClasses (p\
        std.forall AllClasses (q\
          generate-param-type (pc m n) (pc p q) U L L1
        )
      )
    ),
    std.forall Classes44 (n\
      generate-param-type (pc m n) (pc map4 map4) U L L1
    )
  ),
  std.forall Classes44 (m\
    std.forall AllClasses (n\
      generate-param-type (pc m n) (pc map4 map4) U L L1
    )
  ).
}}.

(* Set Printing Universes. About Param00_Type40.
Set Printing Universes. About Param12a_Type31.
Set Printing Universes. About Param30_Type44.
Set Printing Universes. About Param44_Type44. *)
