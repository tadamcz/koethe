# Köthe conjecture: disproof (Krempa's matrix form)

[![CI](https://github.com/tadamcz/koethe/actions/workflows/ci.yml/badge.svg)](https://github.com/tadamcz/koethe/actions/workflows/ci.yml)

> **Note.** This README, the documentation in `Challenge.lean` and `formalization.yaml` were machine-written by Claude (Anthropic)
> at the direction of Tom Adamczewski, from the run's files and the module documentation inside the proof file, and reviewed by
> him. The Lean proof itself was written by GPT-6 Astra, as described below, and the proof account below was machine-generated
> from that proof.

Machine-checked disproof of the [Köthe conjecture](https://en.wikipedia.org/wiki/K%C3%B6the_conjecture) in Lean 4 with Mathlib, found autonomously by a
pre-release version of **GPT-6 Astra** (OpenAI) in an evaluation run by Epoch AI over the open problems of Formal Conjectures'
Wikipedia collection. The repository packages the AI-written proof for the [Palomar registry](https://palomar-registry.org/):
`Challenge.lean` is the small statement a reader audits, `Solution.lean` proves it, and
[Comparator](https://github.com/leanprover/comparator) checks that the two statements coincide and that only the standard axioms
are used.

## The result

Köthe's conjecture (1930) asks whether the sum of two nil left ideals of a ring is always nil, equivalently whether
every ring has a largest nil left ideal. Krempa (1972) showed it equivalent to several other statements, among them that
for every ring `R` and nil two-sided ideal `I` the matrix ideal `M_n(I)` is nil in `M_n(R)` (already for `n = 2`), and
that `N[x]` is Jacobson radical for every nil ring `N`. Amitsur proved the conjecture over uncountable fields;
Smoktunowicz (2000) refuted the related Amitsur conjecture that polynomial rings over nil rings are nil. The conjecture
itself has been open for over ninety years.

The matrix form is **false**: there is a ring `R` (a unital algebra over the countable field `\overline{𝔽_2}`), a nil
two-sided ideal `I ⊆ R` and a `2 × 2` matrix with entries in `I` that is not nilpotent. Formally, the theorem proved is
the negation of the Formal Conjectures statement `Koethe.KotherConjecture.variants.general_matrix`. Since `M_n(I)` is
the sum of its `n` column left ideals, each of which is nil when `I` is, Köthe's original statement implies the matrix
form; the counterexample therefore also refutes the conjecture as originally stated, though that implication is not part
of the formal development.

The compared declaration, from `Challenge.lean`:

```lean
open scoped Classical in
theorem KotherConjecture.variants.general_matrix.disproof : ¬ (∀ {R : Type*} [Ring R] {I : TwoSidedIdeal R},
    IsNil I → ∀ (n : Type*) [Fintype n], IsNil (matrix n I)) := by
  sorry
```

The benchmark file states the conjecture and its negation `….disproof`, both with `sorry`, and the model fills in exactly one.
Here the compared theorem is the negation, written out explicitly instead of via `type_of%` (see *Edits* below).

**Fidelity.** The compared theorem is exactly the negation of the Formal Conjectures statement `general_matrix`, restated explicitly:
for all `R : Type u_1` with `[Ring R]`, all two-sided ideals `I` with `IsNil I` (every element nilpotent), and all
finite index types `n : Type u_2`, `IsNil (TwoSidedIdeal.matrix n I)`. `TwoSidedIdeal.matrix n I` is Mathlib's entrywise
matrix ideal `M_n(I)` and requires a `DecidableEq n` instance, supplied classically (`open scoped Classical in`) exactly
as in the Formal Conjectures file. The definition `Koethe.IsNil` is copied verbatim from that file. The statement is
universe-polymorphic in `R` and `n`; the witness is built in every universe (`AlgebraicClosure (ULift (ZMod 2))`, index
type `ULift (Fin 2)`). The relation to Köthe's original formulation (sums of nil left ideals) is a standard argument
stated in the README but not formalized.

## Provenance

**Run.** The proof was produced in the evaluation run `wikipedia-vega-1000usd` of Epoch AI's LeanOpenProblems harness (2026-09), in which a pre-release version of GPT-6 Astra attempted, autonomously and once each, all 222 research-open statements of the `Wikipedia` collection of Formal Conjectures under a budget of $1,000 and 96 hours of working time per statement. The agent works in a
network-isolated Docker container with a Lean 4 toolchain (v4.27.0) and Mathlib, SageMath and Python; its final `Spec.lean` is
checked in a separate pristine container by Comparator against the trusted statement, permitting only `propext`, `Quot.sound` and
`Classical.choice`. The harness is public at [epoch-research/LeanOpenProblems](https://github.com/epoch-research/LeanOpenProblems); the dataset used here lives on its
`wikipedia-dataset` branch. No human saw or steered the proof search.

**Statement.** The definitions and the statement come verbatim from [`FormalConjectures/Wikipedia/Koethe.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9cbe1d3c12998c786b7c2cd99ce28a21b6631f66/FormalConjectures/Wikipedia/Koethe.lean) in
Google DeepMind's Formal Conjectures at commit `9cbe1d3c1299`, where the problem is stated with `sorry` as open. The harness isolated the
statement into [`apn/data/wikipedia/Isolated/Koethe.KotherConjecture.variants.general_matrix.lean`](https://github.com/epoch-research/LeanOpenProblems/blob/0ef96d7b12cfa96a93761b4bba1c635f4546c5ca/apn/data/wikipedia/Isolated/Koethe.KotherConjecture.variants.general_matrix.lean) (with a `.disproof` negation added), and that file
is exactly what the model received.

## Proof account

The following account was machine-generated from the Lean proof (it refers to the actual declarations) and has not been checked
by a human mathematician; Comparator establishes only that the compared theorem is proved.

Let `k = \overline{𝔽_2}`, `K = k(t)`, `V = K^ℕ`, and choose nonzero weights `v_n ∈ k^3`. Three weighted backward shifts
`(a_i u)(n) = v_n(i) u(n+1)` generate a non-unital `k`-algebra `A`; `R = k ⊕ A` is its unitization and `I = A`. The
operator `a_0 + t a_1 + t^2 a_2` (a `K`-combination, not an element of `A`) fixes an explicit nonzero vector, and once
`A` is nil this produces a companion matrix `H ∈ M_2(R)` with a nonzero eigenvalue, so `W = H^2 ∈ M_2(I)` is not
nilpotent (`ShiftWitness`, `nonnil_matrix_of_fixed_vector`). The bulk of the development shows that `v` can be chosen so
that `A` is nil: each `x ∈ A` is linearized into a pencil `P(X)` whose nilpotence implies that of `x`
(`nil_of_all_pencils_nil`); powers of a pencil act through products of scalar matrices over `k[X]` along windows of `v`;
a mask-mortality lemma (`maskMortality`) kills any given pencil on a periodic pattern by rank reduction, using a
multiprojective common-zero theorem (`exists_common_zero`, proved via the Segre cone, the Nullstellensatz and Krull's
height theorem) and an `X`-degree bound; a diagonal construction (`exists_universalMortalSequence`) over the countably
many pencils yields a universal mortal sequence. `KoetheCounterexample.counterexample` assembles the witness and the
final theorem transports it to an arbitrary universe.

## Repository layout

- `Challenge.lean` — the statement surface: definitions copied verbatim from the benchmark statement and the compared theorem with `sorry`.
- `Solution.lean` — imports the proof module, in whose environment the compared theorem is proved.
- `Koethe.lean`, `Koethe/Resolutions/Koethe.lean` — the AI-written proof module (the model's final `Spec.lean`, edited as listed below).
- `comparator.json` — Comparator configuration naming `Koethe.KotherConjecture.variants.general_matrix.disproof`.
- `formalization.yaml` — structured metadata (provenance, sources, classification, automation, review) in the mathlib-initiative v0.4 format.
- `provenance/` — SHA-256 of the run's output file and the unified diff from it to the module here.
- `scripts/verify-comparator.sh` runs the pinned Comparator, lean4export, NanoDa and Landrun locally (Linux); `scripts/validate-formalization.rb` checks the metadata file.
- `.github/workflows/ci.yml` — builds the project and runs Comparator (layout from the Palomar template; the template's doc-gen4 job is omitted because the module imports all of Mathlib).

## Edits relative to the run's output

The proof module is the model's final `Spec.lean`, verified in the harness, with only the following mechanical changes (exact diff in
`provenance/`; SHA-256 of the original: `4ee27278289c32141dad62c835beba78aa77f07e11b5a04eaa0362e002aea433`). The toolchain was moved from Lean v4.27.0 / Mathlib (via Formal Conjectures at commit
`9cbe1d3c`) to Lean v4.28.0 / Mathlib v4.28.0, the oldest release Palomar accepts.

- line 1: `import FormalConjecturesUtil` → `import Mathlib`
- removed the sorry'd stub of the original conjecture `KotherConjecture.variants.general_matrix` (lines 3222–3227 of the original) together with its docstring and `open scoped Classical in`
- restated `Koethe.KotherConjecture.variants.general_matrix.disproof` explicitly under `open scoped Classical in` (the original used `¬ (type_of% @Koethe.KotherConjecture.variants.general_matrix)`, which referenced the removed stub) and added a docstring

## Verification

```sh
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux: Comparator + NanoDa under Landrun
```

CI runs the same checks. The compared theorem depends on no `sorry` and on no axioms beyond `propext`, `Quot.sound` and
`Classical.choice`. This repository is prepared for submission to Palomar through the
[submission form](https://submit.palomar-registry.org/) with the full commit SHA; registration is a separate step by the maintainer.

## Licence and attribution

This repository snapshot is licensed under the Apache License 2.0 (see `LICENSE`). The benchmark statement it reproduces is
from Formal Conjectures, © The Formal Conjectures Authors, Apache-2.0 (see `NOTICE`). Cited papers, Wikipedia and Mathlib retain
their own licences.
