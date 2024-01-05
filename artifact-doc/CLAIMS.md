# Claims of the paper supported by the artifact

### Our formulation of type equivalence enables automation in the proofs.

As this variant of type equivalence is symmetrical, the parametricity lemmas can be proved by combining atomic proofs over map classes. Indeed, for example, in file `Param_forall.v`, the following lemma is proved:
```coq
Definition Map2a_forall
  (A A' : Type) (AR : Param04.Rel A A') (B : A -> Type) (B' : A' -> Type)
  (BR : forall a a', AR a a' -> Param2a0.Rel (B a) (B' a')) :
    Map2a.Has (R_forall AR BR).
```
6 such lemmas are written, one for each level of the map class hierarchy. Then, by combining *e.g.* `Map1_forall` and a `Map2a_forall`, we can get the following parametricity lemma:
```coq
Param12a_forall :
  (A A' : Type) (AR : Param42a.Rel A A') (B : A -> Type) (B' : A' -> Type)
  (BR : forall a a', AR a a' -> Param12a.Rel (B a) (B' a')) :
    Param12a.Rel (forall a, B a) (forall a', B' a').
```
In the present implementation, all the possible combinations are generated with a meta-program, hence showing a high level of automation. The same remark can be made with other files such as `Param_Type.v`.

### Trocq can avoid univalence in some cases, whereas univalent parametricity systematically needs it.

As explained in the paper, univalent parametricity makes use of the univalence axiom for every occurrence of `Type` in the initial goal. Yet, in our `peano_bin_nat.v` example file, we show that it is possible to perform proof transfer on the induction principle of natural numbers, between Coq representations `nat` and `N` of this mathematical concept, without resorting to the univalence axiom, even though it features an occurrence of `Type` in the codomain of the predicate `P`.

### Trocq handles non-bijective relations.

In the `int_to_Zp.v` file, we present proof transfer done by Trocq on a goal featuring integers modulo a hypothetical constant $p$, which is not equivalent to the whole set of integers, but a weaker relation — a split surjection — can still be stated between them. Whereas tools like univalent parametricity propagate type equivalences everywhere, Trocq can handle more diverse relations in a finer-grained way.

### Trocq supports polymorphism and dependent types.

The `Vector_tuple.v` file defines a type equivalence between fixed-size vectors and iterated tuples, which are both implemented in Coq using polymorphism — elements inside these data structures can be anything — and dependent types — to ensure the size is a fixed integer $n$.
Proof transfer is then performed on a few goals to prove over iterated tuples, in order to be able to exploit standard library lemmas about vectors and get these properties "for free".

### Trocq subsumes the core features of generalised rewriting.

Files `*_rewrite.v` show that Trocq can be used to rewrite with relations different from Leibniz equality, such as a custom equality over integers or an order relation over integers.

### Combining an inference-rule-based presentation of parametricity with the logic programming paradigm of Coq-Elpi allows to write the code in a readable way.

The most telling example supporting this claim is the `elpi/param.elpi` file, featuring an instance of the Elpi `param` predicate for each syntactic construction, in correspondence with the inference rules of the paper.
