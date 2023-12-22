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

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Local Open Scope param_scope.

Elpi Command genparamforall.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.

  
Definition R_forall@{i j}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param00.Rel@{j} (B a) (B' a')) :=
    fun f f' => forall a a' aR, (PB a a' aR) (f a) (f' a').

(* we can also declare everything from Coq-Elpi if we do not trust inference *)
(* Elpi Query lp:{{
  coq.univ.new U,
  coq.univ.variable U L,
  coq.univ-instance UI [L],
  coq.univ.new U',
  coq.univ.variable U' L',
  coq.univ-instance UI' [L'],
  coq.locate "Param00.Rel" Rel00,
  coq.locate "Param00.R" R00,
  Decl = (
    fun `A` (sort (typ U)) a\
    fun `A'` (sort (typ U)) a'\
    fun `PA` (app [pglobal Rel00 UI, a, a']) pa\
    fun `B` (prod `_` a _\ sort (typ U')) b\
    fun `B'` (prod `_` a' _\ sort (typ U')) b'\
    fun `PB` (prod `a` a x\ prod `a'` a' x'\
              prod `_` (app [pglobal R00 UI, a, a', pa, x, x']) _\
                app [pglobal Rel00 UI', app [b, x], app [b', x']]) pb\
      fun `f` (prod `a` a x\ app [b, x]) f\
      fun `f'` (prod `a'` a' x'\ app [b', x']) f'\
        prod `a` a t\
        prod `a'` a' t'\
        prod `aR` (app [pglobal R00 UI, a, a', pa, t, t']) tR\
          app [pglobal R00 UI', app [b, t], app [b', t'], app [pb, t, t', tR],
            app [f, t], app [f', t']]
  ),
  @udecl! [L, L'] ff [] ff =>
    coq.env.add-const "R_forall" Decl _ @transparent! _.
}}. *)

(* MapN for forall *)

(* (00, 00) -> 00 *)
Definition Map0_forall@{i j k | i <= k, j <= k}
  {A A' : Type@{i}} (PA : Param00.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param00.Rel@{j} (B a) (B' a')) :
    Map0.Has@{k} (R_forall@{i j} PA PB).
Proof. constructor. Defined.

(* (02a, 10) -> 1 *)
Definition Map1_forall@{i j k}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param10.Rel@{j} (B a) (B' a')) :
    Map1.Has@{k} (R_forall@{i j} PA PB).
Proof.
  constructor.
  exact (fun f a' => map (PB _ _ (comap_in_R _ _ _ 1)) (f (comap PA a'))).
Defined.

(* (04, 2a0) -> 2a0 *)
Definition Map2a_forall@{i j k}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param2a0.Rel@{j} (B a) (B' a')) :
    Map2a.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_forall@{i j k} PA PB)).
  move=> f f' e a a' aR; apply (map_in_R@{j} (PB _ _ _)).
  apply (transport@{j j} (fun t => _ = t a') e) => /=.
  by elim/(comap_ind@{i j} a a' aR): _.
Defined.

(* (02a, 2b0) + funext -> 2b0 *)
Definition Map2b_forall@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param02a.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param2b0.Rel@{j} (B a) (B' a')) :
    Map2b.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_forall PA PB)).
  - move=> f f' fR; apply path_forall => a'.
    apply (R_in_map (PB _ _ _)); exact: fR.
Defined.

(* (04, 30) + funext -> 30 *)
Definition Map3_forall@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param30.Rel@{j} (B a) (B' a')) :
    Map3.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists (Map1.map@{k} _ (Map1_forall PA PB)).
  - exact: (Map2a.map_in_R _ (Map2a_forall PA PB)).
  - move=> f f' fR; apply path_forall => a'.
    apply (R_in_map (PB _ _ _)); exact: fR.
Defined.

(* (04, 40) + funext -> 40 *)
Definition Map4_forall@{i j k} `{Funext}
  {A A' : Type@{i}} (PA : Param04.Rel@{i} A A')
  {B : A -> Type@{j}} {B' : A' -> Type@{j}}
  (PB : forall (a : A) (a' : A'), PA a a' -> Param40.Rel@{j} (B a) (B' a')) :
    Map4.Has@{k} (R_forall@{i j} PA PB).
Proof.
  exists
    (Map1.map@{k} _ (Map1_forall PA PB))
    (Map3.map_in_R _ (Map3_forall PA PB))
    (Map3.R_in_map _ (Map3_forall PA PB)).
  move=> f f' fR /=.
  apply path_forall@{i k} => a.
  apply path_forall@{i k} => a'.
  apply path_forall => aR.
  unfold comap_ind.
  elim (R_in_comapK PA a' a aR) => /=.
  (* elim (R_in_comap PA a' a aR).
  rewrite transport_apD10.
  rewrite apD10_path_forall_cancel/=.
  rewrite <- (R_in_mapK (PB _ _ _)).
  by elim: (R_in_map _ _ _ _). *)
Admitted.
(* Param_forallMN : forall A A' AR B B' BR,
     ParamMN.Rel (forall a, B a) (forall a', B' a') *)

Elpi Accumulate lp:{{
  pred generate-param-forall
    i:param-class, i:univ, i:univ, i:univ.variable, i:univ.variable,
    i:univ.variable.
  generate-param-forall (pc M N as Class) Ui Uj Li Lj Lk :-
    % we need to generate Map in both ways, so we must add the dependencies
    % from both sides to get the final classes we shall ask for A and B
    map-class.dep-pi M ClassAM ClassBM,
    map-class.dep-pi N NegClassAN NegClassBN,
    param-class.negate NegClassAN ClassAN,
    param-class.negate NegClassBN ClassBN,
    param-class.union ClassAM ClassAN ClassA,
    ClassA = pc MA NA,
    param-class.union ClassBM ClassBN ClassB,
    ClassB = pc MB NB,
    map-class->string M MStr,
    map-class->string N NStr,
    map-class->string MA MAStr,
    map-class->string MB MBStr,
    map-class->string NA NAStr,
    map-class->string NB NBStr,
    coq.univ-instance UIi [Li],
    coq.univ-instance UIj [Lj],
    coq.univ-instance UIk [Lk],
    coq.univ-instance UIij [Li, Lj],
    coq.univ-instance UIik [Li, Lk],
    coq.univ-instance UIijk [Li, Lj, Lk],
    coq.locate {calc ("Param" ^ MAStr ^ NAStr ^ ".Rel")} RelA,
    coq.locate {calc ("Param" ^ MAStr ^ NAStr ^ ".R")} RA,
    coq.locate {calc ("Param" ^ MBStr ^ NBStr ^ ".Rel")} RelB,
    coq.locate {calc ("Param" ^ MBStr ^ NBStr ^ ".R")} RB,
    coq.locate {calc ("Param" ^ MStr ^ NStr ^ ".BuildRel")} BuildRel,
    coq.locate "R_forall" RForall,
    coq.locate {calc ("Map" ^ MStr ^ "_forall")} MapM,
    coq.locate {calc ("Map" ^ NStr ^ "_forall")} MapN,
    coq.locate {calc ("eq_Map" ^ NStr)} EqMapN,
    coq.locate "equiv_flip" EquivFlip,
    coq.locate {calc ("Param" ^ MAStr ^ NAStr ^ "_sym")} ParamSymA,
    coq.locate {calc ("Param" ^ NAStr ^ MAStr ^ ".R")} RSymA,
    coq.locate {calc ("Param" ^ MBStr ^ NBStr ^ "_sym")} ParamSymB,
    % build functions doing several weakenings at once
    param-class.forget ClassA (pc map0 map0) ForgetA0F,
    param-class.forget ClassB (pc map0 map0) ForgetB0F,
    param-class.forget ClassA ClassAM ForgetADepMF,
    param-class.forget ClassB ClassBM ForgetBDepMF,
    param-class.forget {param-class.negate ClassA} NegClassAN ForgetADepNF,
    param-class.forget {param-class.negate ClassB} NegClassBN ForgetBDepNF,
    % we cut the proof into multiple parts for readability
    RForallF = (a\ a'\ aR\ b\ b'\ bR\
      app [pglobal RForall UIij,
        a, a', ForgetA0F UIi a a' aR, b, b',
        fun `a` a x\ fun `a'` a' x'\
        fun `aR` (app [pglobal RA UIi, a, a', aR, x, x']) xR\
          ForgetB0F UIj (app [b, x]) (app [b', x']) (app [bR, x, x', xR])]
    ),
    EqMapR1F = (a\ a'\ aR\ b\ b'\ bR\
      fun `f'` (prod `a'` a' x'\ app [b', x']) f'\
      fun `f` (prod `a` a x\ app [b, x]) f\
        prod `a` a x\ prod `a'` a' x'\
          prod `aR` (app [pglobal RA UIi, a, a', aR, x, x']) xR\
            app [pglobal RB UIj, app [b, x], app [b', x'], app [bR, x, x', xR],
              app [f, x], app [f', x']]
    ),
    EqMapR2F = (a\ a'\ aR\ b\ b'\ bR\
      fun `f'` (prod `a'` a' x'\ app [b', x']) f'\
      fun `f` (prod `a` a x\ app [b, x]) f\
        prod `a'` a' x'\ prod `a` a x\
          prod `aR` (app [pglobal RA UIi, a, a', aR, x, x']) xR\
            app [pglobal RB UIj, app [b, x], app [b', x'], app [bR, x, x', xR],
              app [f, x], app [f', x']]
    ),
    EqMapR1R2EquivF = (a\ a'\ aR\ b\ b'\ bR\
      fun `f'` (prod `a'` a' x'\ app [b', x']) f'\
      fun `f` (prod `a` a x\ app [b, x]) f\
        app [pglobal EquivFlip UIik, a, a',
          (fun `a` a x\ fun `a'` a' x'\
            prod `aR` (app [pglobal RA UIi, a, a', aR, x, x']) xR\
              app [pglobal RB UIj, app [b, x], app [b', x'],
                app [bR, x, x', xR],
                app [f, x], app [f', x']])]
    ),
    % there is one call to MapM_forall and one on MapN_forall on the symmetric
    % relation; both can need funext depending on M and N
    MapMArgsF = (a\ a'\ aR\ b\ b'\ bR\ [
      a, a', ForgetADepMF UIi a a' aR, b, b',
      fun `a` a x\ fun `a'` a' x'\
      fun `aR` (app [pglobal RA UIi, a, a', aR, x, x']) xR\
        ForgetBDepMF UIj (app [b, x]) (app [b', x']) (app [bR, x, x', xR])
    ]),
    MapNArgsF = (a\ a'\ aR\ b\ b'\ bR\ [
      a', a, ForgetADepNF UIi a' a (app [pglobal ParamSymA UIi, a, a', aR]),
      b', b,
      (fun `a'` a' x'\ fun `a` a x\
        fun `aR` (app [pglobal RSymA UIi, a', a,
                    app [pglobal ParamSymA UIi, a, a', aR], x', x]) xR\
          ForgetBDepNF UIj (app [b', x']) (app [b, x])
            (app [pglobal ParamSymB UIj, app [b, x], app [b', x'],
              app [bR, x, x', xR]]))
    ]),
    if (std.mem! [map2b, map3, map4] M) (
      FunextDecl = true,
      MapMF = (funext\ a\ a'\ aR\ b\ b'\ bR\
        app [pglobal MapM UIijk, funext | MapMArgsF a a' aR b b' bR]),
      if (std.mem! [map2b, map3, map4] N) (
        MapNF = (funext\ a\ a'\ aR\ b\ b'\ bR\
          app [pglobal MapN UIijk, funext | MapNArgsF a a' aR b b' bR])
      ) (
        MapNF = (_\ a\ a'\ aR\ b\ b'\ bR\
          app [pglobal MapN UIijk | MapNArgsF a a' aR b b' bR])
      )
    ) (
      MapMF = (_\ a\ a'\ aR\ b\ b'\ bR\
        app [pglobal MapM UIijk | MapMArgsF a a' aR b b' bR]),
      if (std.mem! [map2b, map3, map4] N) (
        FunextDecl = true,
        MapNF = (funext\ a\ a'\ aR\ b\ b'\ bR\
          app [pglobal MapN UIijk, funext | MapNArgsF a a' aR b b' bR])
      ) (
        FunextDecl = false,
        MapNF = (_\ a\ a'\ aR\ b\ b'\ bR\
          app [pglobal MapN UIijk | MapNArgsF a a' aR b b' bR])
      )
    ),
    % ParamMN_forall proof
    DeclF = (funext\
      fun `A` (sort (typ Ui)) a\
      fun `A'` (sort (typ Ui)) a'\
      fun `AR` (app [pglobal RelA UIi, a, a']) aR\
      fun `B` (prod `_` a _\ sort (typ Uj)) b\
      fun `B'` (prod `_` a' _\ sort (typ Uj)) b'\
      fun `BR`
        (prod `a` a x\ prod `a'` a' x'\
          prod `_` (app [pglobal RA UIi, a, a', aR, x, x']) _\
            app [pglobal RelB UIj, app [b, x], app [b', x']]) bR\
        app [pglobal BuildRel UIk,
          (prod `a` a x\ app [b, x]),
          (prod `a'` a' x'\ app [b', x']),
          RForallF a a' aR b b' bR,
          MapMF funext a a' aR b b' bR,
          app [pglobal EqMapN UIk,
            (prod `a'` a' x'\ app [b', x']),
            (prod `a` a x\ app [b, x]),
            EqMapR1F a a' aR b b' bR,
            EqMapR2F a a' aR b b' bR,
            EqMapR1R2EquivF a a' aR b b' bR,
            MapNF funext a a' aR b b' bR]]
    ),
    % add an additional binder for funext in case it is needed
    if (FunextDecl) (
      coq.locate "Funext" Funext,
      Decl = (fun `H` (global Funext) funext\ DeclF funext)
    ) (
      Dummy = (fun `x` (sort (typ Ui)) x\ x),
      Decl = DeclF Dummy
    ),
    ParamForall is "Param" ^ MStr ^ NStr ^ "_forall",
    % this typecheck is very important: it adds L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    @udecl! [Li, Lj, Lk] ff [le Li Lk, le Lj Lk] tt =>
      coq.env.add-const ParamForall Decl _ @transparent! Const,
    coq.elpi.accumulate _ "trocq.db" (clause _ (after "default-param-forall")
      (trocq.db.param-forall Class Const)).
}}.
Elpi Typecheck.

Elpi Query lp:{{
  coq.univ.new Ui,
  coq.univ.variable Ui Li,
  coq.univ.new Uj,
  coq.univ.variable Uj Lj,
  coq.univ.max Ui Uj Uk,
  % cannot have only 2 binders in the declaration because this line creates a fresh level:
  coq.univ.variable Uk Lk,
  Classes = [map0, map1, map2a, map2b, map3, map4],
  std.forall Classes (m\
    std.forall Classes (n\
      generate-param-forall (pc m n) Ui Uj Li Lj Lk
    )
  ).
}}.

(* Set Printing Universes. About Param2a1_forall.
Set Printing Universes. About Param2b1_forall.
Set Printing Universes. About Param33_forall. *)
