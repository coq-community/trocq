# Tutorial

This tutorial for Trocq first explains how to use the plugin in general, then covers several examples of proof transfer cases.

## Use of the plugin

The Trocq plugin must be used in two steps:
1. First, the user fills in the knowledge base by declaring pairs of terms linked by a parametricity relation.
These terms can be inductive types or any constants. Two terms `a : A` and `a' : A'` must be related by an instance of the relation `AR` linking their types `A` and `A'`, *i.e.*, an inhabitant of `AR a a'`. In the particular case of types, two types `A` and `B` must be related by an inhabitant of `ParamNK.Rel A B` with `(N, K)` the parametricity class describing the structure given to the relation between `A` and `B`, ranging from a raw relation to a full type equivalence.
Declaring these relations can be done by filling every desired field of the `Param` record, but can be made easier by going through the definitions in `theories/Common.v`. Indeed, we offer to the user a way to generate `Param` records from functions (module `Fun`), split injections (module `SplitInj`), split surjections (module `SplitSurj`), or isomorphisms (module `Iso`), respectively yielding instances of `Param` at levels $(4, 0)$, $(4, 2_b)$, $(4, 2_a)$, and $(4, 4)$.
2. Second, the user states a goal to prove featuring terms that are left-hand components in the previously declared pairs, so that Trocq can perform proof transfer and rephrase the goal with the right-hand components, by combining the parametricity relations provided with the pairs of terms.

The first step is done with the `Trocq Use` command whose only argument is the parametricity relation. The second step is done by calling the `trocq` tactic after stating the goal to prove. The tactic then automatically proves the goal substitution with a generated transfer proof and only leaves the associated goal to prove.

## Examples

In this section, we show various use cases of Trocq related to arithmetic, containers, mathematics, and rewriting.

### Arithmetic

Trocq can be used to perform proof transfer in arithmetic goals, and thus enable proof reuse by allowing to use standard library lemmas on user-defined custom arithmetic types.

#### Binary natural numbers (`peano_bin_nat.v`)

todo

#### Modular arithmetic (`int_to_Zp.v`)

todo

<!-- ```coq
Lemma Radd : forall (x : Zp) (x' : int) (xR : Rp x x') (y : Zp) (y' : int) (yR : Rp y y'), Rp (x + y)%Zp (x' + y')%int.
Proof. (...) Qed.

Trocq Use Radd.
```
will enable the translation of the addition over type Zp (integers mod p) to type int (integers) because Rp is defined as the embedding of an integer mod p into int via a suitable `pmap` function:

```coq
Definition Rp (x : Zp) (n : int) := pmap x = n.
```

As soon as Rp is equipped with the suitable structure (which is not an equivalence in this case!), we can use it to transfer to Zp the obvious consequences of the arithemtic on integers. For instance:
```coq
Goal (forall x y, x + y = y + x)%Zp.
Proof.
trocq. (* here we obtain the corresponding goal type int *)
apply int_add_comm. (* here we use the commutativity of addition on  type int *)
Qed.
``` -->

#### Bitwise arithmetic (`Vector_tuple.v`)

todo

### Containers

todo

### Lifting equivalences to lists

`list nat` `list binnat`
todo

### Vectors and iterated tuples (`Vector_tuple.v`)

todo

<!-- ```coq
Lemma head_const {n : nat} : forall (i : int), Vector.hd (Vector.const i (S n)) = i.
Proof. destruct n; simpl; reflexivity. Qed.
```
states that the head of a vector filled with `(n + 1)` copies of any `(i : int)` is equal to `i`, for vectors as the type `Vector.t` from Coq's standard library. The `trocq` tactic transfers it to its analogue on the head of a tuple filled with `(n + 1)` copies of any `(z : Zp)`, with type `tuple` being defined as a fixpoint-generated iterated product and `Zp` a type for integers modulo p:
```coq
Lemma head_const' : forall {n : nat} (z : Zp), head (const z (S n)) = z.
Proof. trocq. apply @head_const. Qed.
```
The database used by the `trocq` tactic  has proofs that `vector A` and `tuple A'` are (4-4)-related (i.e, equivalent) when `A` and `A'` are related and that Zp and int are (4, 2b)-related (as well as the corollaries on weaker relations), plus proofs that the respective `head`, `const` and successor operations on these types are related.

Types `Vector.t` and `tuple` play here the role of a pair of arbitrary equivalent polymorphic data structures, and `Zp` that of a refinement of `int`. -->

### Mathematics

infinite summation
todo

### Rewriting

setoid / gen rewriting
todo