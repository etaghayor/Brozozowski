# Project #

This project deals with regular expressions ([regexps][]) and Brzozowski [derivatives][] and aims at formalizing Brzozowski finiteness theorem in Coq. It was translated and adapted from a project by Pierre Letouzey.


[regexps]: https://en.wikipedia.org/wiki/Regular_expression
[derivatives]: https://en.wikipedia.org/wiki/Brzozowski_derivative
[expression rationelle]: https://fr.wikipedia.org/wiki/Expression_rationnelle
[dérivées]: https://fr.wikipedia.org/wiki/D%C3%A9riv%C3%A9e_de_Brzozowski

**Beware** : Doing all proos of the project would be **very**
long, but they constitute a global result that we wanted to provide to you nevertheless. Given that, several files are  **optional**. 
The mandatory part to get the best grade consists in :

  - completion of both files of part 1 : [Languages.v](Languages.v) et [Regular.v](Regular.v)
  
  - completion of two files from part 2 among [ListUtils.v](ListUtils.v), [Finiteness.v](Finiteness.v), [Explore.v](Explore.v) et [EquivDec.v](EquivDec.v).

For each of those files, your work shall be to replace, as much as possible, the  `Admitted` with axiomless Coq proofs. It may be the case that some proofs are already provided. 
You can freel add intermediate lemmas or aditional commands helping you in your proofs such as `Hint` for instance. 
On the other hand, you shoul not modify the statements and definitions which are given (`Definition`, `Fixpoint`, ...) unless you are told to do so.

The optional files [RegOrder.v](RegOrder.v) et [Similar.v](Similar.v) should be read anyway as the definitions and lemmas they contain are needed for the project, but you do not have to prove the `Admitted`
that they may contain (but you can if you want to...).

You can work on proofs in any order you want. Simply note that prior to start working on a file, you should have compiled those which come before either via make `make` (or `coqc` or via the IDE compile command, on each file in the appropriate order, even though it is not recommended). 
Any recent enough version of  Coq is sufficient to do the project.

At any moment, if you think that you miis some technical content to make progress, first go nd investigate the Coq documentation and otherwise please contact us. 

## Part 1 : Definitions of basic notions and first properties

  - [Languages.v](Languages.v) : general definitions of a  language over an alphabet, given as Coq predicates
  
  - [Regular.v](Regular.v) : structure of a regexp, language of a  regexp, derivative of a regexp, etc.

To give you an order of magnitide, each proof of this part
can be done in about 15-20 lines and often less (of a fairly compact style).

## Part 2 : Finiteness of Brzozowski's derivatives

  In this part, you are asked to complete **two** files among those writtent as non-optional below (the **optional** ones are not to be completed):

  - [ListUtils.v](ListUtils.v) : some complementary notions on lists, such as equivalence, inclusions, etc.
  
  - [RegOrder.v](RegOrder.v) : **optional**, comparison and equality test on regexps, finite sets of regexp, complements on lists of regexps.

  - [Similar.v](Similar.v) : **optional** a relation  `sim` (written `=~=`) of regexp similarity, which approximates regexp equivalence `===`. A function `canon` giving the canonical form of a regexp wrt `sim`.

  - [Finiteness.v](Finiteness.v) : Brzozowski's theorem stating that a regexp has a finite number of derivatives in canonical form. 
  Here, we provide a list containing (at least) those derivatives (and more).

  - [Explore.v](Explore.v) : efficient search of the derivatives of a  regexp, by graph traversals. The obtained bound in the previous file allows to prove termination of the search.

  - [EquivDec.v](EquivDec.v) : from what comes before, one can now provide an algorithm testing the equivalence `===` of two regexps, and thus giving the various dinstinct derivatives wrt. `===`. 


## Some useful tactis ##

- [`tauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.tauto)
  to solve intuitionistic propositional tautologies (i.e. by successive `apply` without instanciation of quantifiers).
- [`firstorder`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.firstorder)
  may solve goals requiring to instanciate quantified hypotheses from the context.
- [`btauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.btauto)
  solves tautological boolean equalities (use `Require Import Btauto`).
- [`congruence`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.congruence)
  solves a goal by equational reasoning (useful if the context
  contains, eg. both `H0: x = 0` and `H1: x = 1`).
- [`lia`](https://coq.inria.fr/refman/addendum/micromega.html#coq:tacn.lia)
  solves arithmetical goal (use `Require Import Lia`).
- [`intuition`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.intuition)
  to be used in comination with a tactic that proves the remaining goals after `btauto` or `congruence` (eg `intuition btauto`,
  `intuition congruence`, `intuition lia`, etc.)
- [`eauto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.eauto)
  more powerful that 
  [`auto`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.auto)
  as Coq tries to guess existencial cases, such as in a transitivity reasnoning, by using existencial variables. To be used with other existential tactics such as 
  [`eapply`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.eapply)
  or
  [`eexists`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.eexists),
  for which Coq creates existential variables `?` at places where information is missing to instantiate, waiting for a `eauto`  to guess them.
- `f_equiv` analogous to `f_equal` to be used with an equivalence instead of Coq standard equality. For isntance, if one uses `f_equiv`
  on the goal `Or r s =~= Or r' s'`, it remains to prove `r =~= r'`
  and `s =~= s'`. Only works with functions which are known (by Coq) to be compatible with the corresponding equivalence (cf. `Instance` commands given).

## Some useful lemmas ##

### on booleans ###

- `eq_true_iff_eq : forall b1 b2 : bool, b1 = true <-> b2 = true -> b1 = b2`
- `orb_true_iff : forall b1 b2 : bool, b1 || b2 = true <-> b1 = true \/ b2 = true`
- `andb_true_iff : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true`
- `List.existsb_exists : forall (A : Type) (f : A -> bool) (l : list A),
  List.existsb f l = true <-> (exists x : A, List.In x l /\ f x = true)`

### on lists ###

```
List.app_nil_r : forall (A : Type) (l : list A), l ++ [] = l
```

Numerous other lemmas as available, use `Search`. For isntance, `Search "++" List.In`.

## Some advice for file : Langages.v ##

### To prove equalities ###

Equality `==` over languages is defined as an equivalence,
you may thus usually start your proofs of an `==` with `split`,
unless you can rewrite some part with an alreay known equality.


### Simplifying expressions ###

To force sumplifying whan languages are applied to  words:
`simpl` does not work so you can use
[`red`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.red). Just as
`simpl`, `red` allows for a clause `in` whuch reduce in an 
hypothesis, or everywhere using  `in *`.

### Inductions ###

Some proofs require inductions. In that case, it is
useful to generalize as much as possible the resut to prove with tactic
[`revert`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.revert).

## Some advice for Regular.v ##

One uses here several boolean functions, such as
 - `Letter.eqb` (equality test of two letters)
 - `is_nullable` (test to detect if a regexp accepts the empty word)

In further proofs, when facing an `if f arg ...` where `f` is such a boolean function, one usually uses `destruct (f arg) eqn:H`
for case reasoning. Option `eqn:H` allows to record in an
hypothesis `H` the quation `f arg = true` or `f arg = false`, in order to know in which case we are. Even better, if you have a lemma describing `f` via predicate `reflect`, let us call it `f_spec`,
then one can directly use `case f_spec` (without providing arguments), and both cases automatically propose the appropriate hypotheses.

Eg, for `Letter.eqb`, a `case LetterB.eqb_spec` will break an
`if Letter.eqb .. .. then .. else ..`, and propose either an hypothesis
`.. = ..`, or `.. <> ..`, depending on the case.

For `is_nullable`, a `case nullable_spec`  will break 
`if is_nullable ..`, providing hypotheses `Lang .. []`, or `~Lang .. []`.

## Advices for files in part 2 ##

### Explore.v

Finite sets `REs.t` manipulated in  `Explore.v` are an instance of the library [MSets](https://coq.inria.fr/distrib/current/stdlib/Coq.MSets.MSetInterface.html), which is close to the `Set` of OCaml. Some advice to use them :

 - One can find the list of set-theoretic operations via `Print Module REs`.
   The main operations are `REs.add`, `REs.union`, `REs.elements`, `REs.cardinal`.
   
 - Each operation comes with a lemmagiving its main specification, for instance `REs.add_spec` for `REs.add`.
 
 - For `REs.elements`, to convert a set to a list, use  lemma `REs_elements_spec` rather that `REs.elements_spec1`.
 
 - A  large class of set-theoretic problems is automatically solved by tactic `REsdec`, more details in the long initial comment of file [MSetDecide.v](https://coq.inria.fr/distrib/current/stdlib/Coq.MSets.MSetDecide.html).
 
 - `REsP` is a module containing additional properties on finite sets.
   A priori the only lemmas useful here are those contained in `REs.cardinal`, in particular
   `REsP.add_cardinal_2`. Here again `Search REs.cardinal` will tell you more about this.

 - Tactic `REsP.FM.set_iff` can be  interesting to rewrite as much as possible the specified set-theoretic operations.
   
 - Do not try to look into the implementation of operation in `REs`.
   If you see  `REs.Raw` appear in your proofs, something is wrong
   (too many `unfold` or other similar issue). As well for `Test.v`, 
   do not use `Compute` directely
   on a  `REs.t` (the result would be completely unreadable...), but rather try showing the correpsonding list : `Compute REs.elements ...`.
