From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Elpi.inductives Extra Dependency "relnm.elpi" as relnm.
From Trocq.generic.inductives Require Import sym symK RsymK mapn map4. 
From Trocq Require Import Param_lemmas.
Import HoTTNotations.

From elpi.apps Require Import derive derive.param2.

From Trocq Require Export Stdlib Hierarchy Param_lemmas.
Unset Uniform Inductive Parameters. 

Elpi Command derive.relnm.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db Header derive.rsymK.db.
Elpi Accumulate Db Header trocq.db.
Elpi Accumulate File derive_hook.
Elpi Accumulate File relnm.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.rsymK.db.
Elpi Accumulate Db trocq.db.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.relnm.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.relnm <object name>".
}}. 

(* hook into derive *)
Elpi Accumulate Db Header derive.rsymK.db.
Elpi Accumulate derive File relnm.
Elpi Accumulate Db derive.rsymK.db.
Elpi Accumulate Db trocq.db.
Elpi Accumulate derive lp:{{

dep1 "relnm" "rsymK".
dep1 "relnm" "mapn".
derivation (indt T) Prefix ff (derive "relnm" (derive.relnm.main T Prefix) (trocq.db.param-ind-done T)).

}}.
