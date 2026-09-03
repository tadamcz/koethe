import Mathlib

/-!
# Köthe conjecture: disproof (Krempa's matrix form)

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/K%C3%B6the_conjecture)

Köthe's conjecture (1930) asks whether the sum of two nil left ideals of a ring is always nil,
equivalently whether every ring has a largest nil left ideal. Krempa (1972) showed it equivalent
to several other statements, among them that for every ring `R` and nil two-sided ideal `I` the
matrix ideal `M_n(I)` is nil in `M_n(R)` (already for `n = 2`), and that `N[x]` is Jacobson
radical for every nil ring `N`. Amitsur proved the conjecture over uncountable fields;
Smoktunowicz (2000) refuted the related Amitsur conjecture that polynomial rings over nil rings
are nil. The conjecture itself has been open for over ninety years.

The matrix form is **false**: there is a ring `R` (a unital algebra over the countable field
`\overline{𝔽_2}`), a nil two-sided ideal `I ⊆ R` and a `2 × 2` matrix with entries in `I` that is
not nilpotent. Formally, the theorem proved is the negation of the Formal Conjectures statement
`Koethe.KotherConjecture.variants.general_matrix`. Since `M_n(I)` is the sum of its `n` column
left ideals, each of which is nil when `I` is, Köthe's original statement implies the matrix form;
the counterexample therefore also refutes the conjecture as originally stated, though that
implication is not part of the formal development.

This file is the small statement surface a reader should audit: the theorem
`Koethe.KotherConjecture.variants.general_matrix.disproof` below is the compared declaration, and
the conjecture is refuted (its negation is proved) in `Solution.lean` and the module it imports.
Only the theorem's `sorry` is filled in there.

The definitions and the statement inside this file are copied verbatim from
`FormalConjectures/Wikipedia/Koethe.lean` in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) (Google DeepMind, Apache-2.0) at commit
`9cbe1d3c12998c786b7c2cd99ce28a21b6631f66`, which is the statement the AI system was given (isolated statement file
`apn/data/wikipedia/Isolated/Koethe.KotherConjecture.variants.general_matrix.lean` on the `wikipedia-dataset` branch of [LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems) at commit
`0ef96d7b12cfa96a93761b4bba1c635f4546c5ca`).
-/
open Ideal TwoSidedIdeal Polynomial

open Matrix

variable {R : Type*}

variable [Ring R]

namespace Koethe

/-- Say a subset `I` of a ring `R` is nilpotent if all its elements are nilpotent. -/
def IsNil {S : Type*} [SetLike S R] (I : S) := ∀ i ∈ I, IsNilpotent i

open scoped Classical in
/--
**Disproof of the Köthe conjecture in Krempa's matrix form.** The bracketed statement is the conjecture
`KotherConjecture.variants.general_matrix` exactly as formalized in Formal Conjectures: for any ring `R`,
any nil (two-sided) ideal `I` of `R` and any finite index type `n`, the matrix ideal `M_n(I)` is a nil ideal
of `M_n(R)` (the `DecidableEq n` instance needed by `matrix n I` is the classical one, as in the source).
This theorem says that is false: some ring has a nil ideal `I` with a non-nilpotent matrix in `M_n(I)`.
-/
theorem KotherConjecture.variants.general_matrix.disproof : ¬ (∀ {R : Type*} [Ring R] {I : TwoSidedIdeal R},
    IsNil I → ∀ (n : Type*) [Fintype n], IsNil (matrix n I)) := by
  sorry

end Koethe
