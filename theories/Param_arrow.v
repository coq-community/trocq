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

Elpi Command genparamarrow.
Elpi Accumulate Db trocq.db.
Elpi Accumulate File param_class.

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
  apply (transport@{j j} (fun t => _ = t a') e) => /=.
  by apply (transport@{j j} (fun t => _ = map _ (f t))
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
  move=> f f' fR /=.
  apply path_forall@{i k} => a.
  apply path_forall@{i k} => a'.
  apply path_arrow@{i k} => aR /=.
  rewrite -[in X in _ = X](R_in_comapK PA a' a aR).
Admitted.

(* Param_arrowMN : forall A A' AR B B' BR, ParamMN.Rel (A -> B) (A' -> B') *)

Elpi Accumulate lp:{{
  pred generate-param-arrow
    i:param-class, i:univ, i:univ, i:univ.variable, i:univ.variable,
    i:univ.variable.
  generate-param-arrow (pc M N as Class) Ui Uj Li Lj Lk :-
    % we need to generate Map in both ways, so we must add the dependencies
    % from both sides to get the final classes we shall ask for A and B
    map-class.dep-arrow M ClassAM ClassBM,
    map-class.dep-arrow N NegClassAN NegClassBN,
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
    coq.locate "R_arrow" RArrow,
    coq.locate {calc ("Map" ^ MStr ^ "_arrow")} MapM,
    coq.locate {calc ("Map" ^ NStr ^ "_arrow")} MapN,
    coq.locate {calc ("eq_Map" ^ NStr)} EqMapN,
    coq.locate "equiv_flip" EquivFlip,
    coq.locate {calc ("Param" ^ MAStr ^ NAStr ^ "_sym")} ParamSymA,
    coq.locate {calc ("Param" ^ MBStr ^ NBStr ^ "_sym")} ParamSymB,
    % build functions doing several weakenings at once
    param-class.forget ClassA (pc map0 map0) ForgetA0F,
    param-class.forget ClassB (pc map0 map0) ForgetB0F,
    param-class.forget ClassA ClassAM ForgetADepMF,
    param-class.forget ClassB ClassBM ForgetBDepMF,
    param-class.forget {param-class.negate ClassA} NegClassAN ForgetADepNF,
    param-class.forget {param-class.negate ClassB} NegClassBN ForgetBDepNF,
    % we cut the proof into multiple parts for readability
    RArrowF = (a\ a'\ aR\ b\ b'\ bR\
      app [pglobal RArrow UIij,
        a, a', ForgetA0F UIi a a' aR, b, b', ForgetB0F UIj b b' bR]
    ),
    EqMapR1F = (a\ a'\ aR\ b\ b'\ bR\
      fun `f'` (prod `_` a' _\ b') f'\
      fun `f` (prod `_` a _\ b) f\
        prod `a` a x\ prod `a'` a' x'\
          prod `_` (app [pglobal RA UIi, a, a', aR, x, x']) _\
            app [pglobal RB UIj, b, b', bR, app [f, x], app [f', x']]
    ),
    EqMapR2F = (a\ a'\ aR\ b\ b'\ bR\
      fun `f'` (prod `_` a' _\ b') f'\
      fun `f` (prod `_` a _\ b) f\
        prod `a'` a' x'\ prod `a` a x\
          prod `_` (app [pglobal RA UIi, a, a', aR, x, x']) _\
            app [pglobal RB UIj, b, b', bR, app [f, x], app [f', x']]
    ),
    EqMapR1R2EquivF = (a\ a'\ aR\ b\ b'\ bR\
      fun `f'` (prod `_` a' _\ b') f'\
      fun `f` (prod `_` a _\ b) f\
        app [pglobal EquivFlip UIik, a, a',
          (fun `a` a x\ fun `a'` a' x'\
            prod `aR` (app [pglobal RA UIi, a, a', aR, x, x']) xR\
              app [pglobal RB UIj, b, b', bR, app [f, x], app [f', x']])]
    ),
    % there is one call to MapM_arrow and one on MapN_arrow on the symmetric
    % relation; both can need funext depending on M and N
    MapMArgsF = (a\ a'\ aR\ b\ b'\ bR\ [
      a, a', ForgetADepMF UIi a a' aR, b, b', ForgetBDepMF UIj b b' bR
    ]),
    MapNArgsF = (a\ a'\ aR\ b\ b'\ bR\ [
      a', a, ForgetADepNF UIi a' a (app [pglobal ParamSymA UIi, a, a', aR]),
      b', b, ForgetBDepNF UIj b' b (app [pglobal ParamSymB UIj, b, b', bR])
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
    % ParamMN_arrow proof
    DeclF = (funext\
      fun `A` (sort (typ Ui)) a\
      fun `A'` (sort (typ Ui)) a'\
      fun `AR` (app [pglobal RelA UIi, a, a']) aR\
      fun `B` (sort (typ Uj)) b\
      fun `B'` (sort (typ Uj)) b'\
      fun `BR` (app [pglobal RelB UIj, b, b']) bR\
        app [pglobal BuildRel UIk,
          (prod `_` a _\ b),
          (prod `_` a' _\ b'),
          RArrowF a a' aR b b' bR,
          MapMF funext a a' aR b b' bR,
          app [pglobal EqMapN UIk,
            (prod `_` a' _\ b'),
            (prod `_` a _\ b),
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
    ParamArrow is "Param" ^ MStr ^ NStr ^ "_arrow",
    % this typecheck is very important: it adds L < L1 to the constraint graph
    coq.typecheck Decl _ ok,
    @udecl! [Li, Lj, Lk] ff [le Li Lk, le Lj Lk] tt =>
      coq.env.add-const ParamArrow Decl _ @transparent! Const,
    coq.elpi.accumulate _ "trocq.db" (clause _ (after "default-param-arrow")
      (trocq.db.param-arrow Class Const)).
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
      generate-param-arrow (pc m n) Ui Uj Li Lj Lk
    )
  ).
}}.

(* Set Printing Universes. About Param2a1_arrow.
Set Printing Universes. About Param2b1_arrow.
Set Printing Universes. About Param33_arrow. *)
