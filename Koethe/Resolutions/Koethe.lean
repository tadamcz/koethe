import Mathlib

/-!
# Köthe conjecture

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/K%C3%B6the_conjecture)
-/

/- ## KoetheMultiProjective -/

noncomputable section KoetheProofPart01

set_option autoImplicit false

/-
# Common zeros on products of projective planes

Scratch development, independent of `Submission/Spec.lean`.
The multihomogeneity convention is coefficientwise, so the zero polynomial
is homogeneous of every multidegree.  No projective intersection theorem is
assumed as an axiom.
-/


open scoped BigOperators
open MvPolynomial

namespace KoetheMultiProjective

variable {k : Type*} {N : ℕ}

/-- The polynomial variables, grouped into triples. -/
abbrev Vars (N : ℕ) := Fin N × Fin 3

/-- The degree of an exponent vector in one block. -/
def blockDegree (d : Vars N →₀ ℕ) (b : Fin N) : ℕ :=
  ∑ j : Fin 3, d (b, j)

@[simp] theorem blockDegree_zero (b : Fin N) : blockDegree 0 b = 0 := by
  simp [blockDegree]

@[simp] theorem blockDegree_add (d e : Vars N →₀ ℕ) (b : Fin N) :
    blockDegree (d + e) b = blockDegree d b + blockDegree e b := by
  simp [blockDegree, Finset.sum_add_distrib]

/-- All block degrees of an exponent vector are equal. -/
def Balanced (d : Vars N →₀ ℕ) : Prop :=
  ∀ b c : Fin N, blockDegree d b = blockDegree d c

instance (d : Vars N →₀ ℕ) : Decidable (Balanced d) :=
  inferInstanceAs (Decidable (∀ b c : Fin N, blockDegree d b = blockDegree d c))

@[simp] theorem balanced_zero : Balanced (0 : Vars N →₀ ℕ) := by
  intro b c
  simp

theorem Balanced.add {d e : Vars N →₀ ℕ} (hd : Balanced d) (he : Balanced e) :
    Balanced (d + e) := by
  intro b c
  simp only [blockDegree_add, hd b c, he b c]

theorem Balanced.add_iff_right {d e : Vars N →₀ ℕ} (hd : Balanced d) :
    Balanced (d + e) ↔ Balanced e := by
  constructor
  · intro h b c
    have := h b c
    simpa only [blockDegree_add, hd b c, Nat.add_left_cancel_iff] using this
  · exact hd.add

/-- Coefficientwise multihomogeneity with a specified degree in each block. -/
def IsMultiHomogeneous [CommSemiring k] (f : MvPolynomial (Vars N) k)
    (r : Fin N → ℕ) : Prop :=
  ∀ d, coeff d f ≠ 0 → ∀ b, blockDegree d b = r b

/-- Every nonzero monomial has the same degree `r` in every block. -/
def IsMultiHomogeneousOfDegree [CommSemiring k] (f : MvPolynomial (Vars N) k)
    (r : ℕ) : Prop :=
  IsMultiHomogeneous f (fun _ => r)

/-- Polynomials all of whose monomials have balanced block degrees.
Different monomials may have different common degrees. -/
def HasBalancedSupport [CommSemiring k] (f : MvPolynomial (Vars N) k) : Prop :=
  ∀ d, coeff d f ≠ 0 → Balanced d

theorem IsMultiHomogeneousOfDegree.hasBalancedSupport [CommSemiring k]
    {f : MvPolynomial (Vars N) k} {r : ℕ} (hf : IsMultiHomogeneousOfDegree f r) :
    HasBalancedSupport f := by
  intro d hd b c
  exact (hf d hd b).trans (hf d hd c).symm

section MultihomogeneityAPI

variable [CommSemiring k]

@[simp] theorem isMultiHomogeneous_zero (r : Fin N → ℕ) :
    IsMultiHomogeneous (0 : MvPolynomial (Vars N) k) r := by
  intro d hd
  simp at hd

@[simp] theorem isMultiHomogeneousOfDegree_zero (r : ℕ) :
    IsMultiHomogeneousOfDegree (0 : MvPolynomial (Vars N) k) r :=
  isMultiHomogeneous_zero _

theorem isMultiHomogeneous_monomial {d : Vars N →₀ ℕ} {r : Fin N → ℕ}
    (hd : ∀ b, blockDegree d b = r b) (a : k) :
    IsMultiHomogeneous (monomial d a) r := by
  classical
  intro e he
  by_cases h : d = e
  · subst e
    exact hd
  · simp [coeff_monomial, h] at he

theorem IsMultiHomogeneous.add {p q : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (hq : IsMultiHomogeneous q r) :
    IsMultiHomogeneous (p + q) r := by
  intro d hd
  by_cases h : coeff d p = 0
  · apply hq d
    simpa [coeff_add, h] using hd
  · exact hp d h

theorem IsMultiHomogeneous.smul {p : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (a : k) : IsMultiHomogeneous (a • p) r := by
  intro d hd
  apply hp d
  exact right_ne_zero_of_mul (by simpa only [coeff_smul] using hd)

theorem IsMultiHomogeneous.mul {p q : MvPolynomial (Vars N) k} {r s : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (hq : IsMultiHomogeneous q s) :
    IsMultiHomogeneous (p * q) (r + s) := by
  classical
  intro d hd b
  rw [coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  rw [← Finset.mem_antidiagonal.mp hef, blockDegree_add,
    hp e (left_ne_zero_of_mul h) b, hq f (right_ne_zero_of_mul h) b]
  rfl

theorem IsMultiHomogeneous.pow {p : MvPolynomial (Vars N) k} {r : Fin N → ℕ}
    (hp : IsMultiHomogeneous p r) (n : ℕ) :
    IsMultiHomogeneous (p ^ n) (fun b => n * r b) := by
  induction n with
  | zero =>
    simpa only [pow_zero, Nat.zero_mul] using
      (isMultiHomogeneous_monomial (fun b : Fin N => blockDegree_zero b) (1 : k))
  | succ n ih =>
    simpa only [pow_succ, Nat.add_mul, Nat.one_mul] using ih.mul hp

theorem IsMultiHomogeneousOfDegree.add {p q : MvPolynomial (Vars N) k} {r : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (hq : IsMultiHomogeneousOfDegree q r) :
    IsMultiHomogeneousOfDegree (p + q) r := IsMultiHomogeneous.add hp hq

theorem IsMultiHomogeneousOfDegree.mul {p q : MvPolynomial (Vars N) k} {r s : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (hq : IsMultiHomogeneousOfDegree q s) :
    IsMultiHomogeneousOfDegree (p * q) (r + s) := IsMultiHomogeneous.mul hp hq

theorem IsMultiHomogeneousOfDegree.pow {p : MvPolynomial (Vars N) k} {r : ℕ}
    (hp : IsMultiHomogeneousOfDegree p r) (n : ℕ) :
    IsMultiHomogeneousOfDegree (p ^ n) (n * r) := IsMultiHomogeneous.pow hp n

end MultihomogeneityAPI

section BalancedAlgebra

variable [CommSemiring k]

theorem hasBalancedSupport_monomial {d : Vars N →₀ ℕ} (hd : Balanced d) (a : k) :
    HasBalancedSupport (monomial d a) := by
  classical
  intro e he
  by_cases h : d = e
  · simpa [← h] using hd
  · simp [coeff_monomial, h] at he

theorem hasBalancedSupport_add {p q : MvPolynomial (Vars N) k}
    (hp : HasBalancedSupport p) (hq : HasBalancedSupport q) :
    HasBalancedSupport (p + q) := by
  intro d hd
  by_cases h : coeff d p = 0
  · apply hq d
    simpa [coeff_add, h] using hd
  · exact hp d h

theorem hasBalancedSupport_mul {p q : MvPolynomial (Vars N) k}
    (hp : HasBalancedSupport p) (hq : HasBalancedSupport q) :
    HasBalancedSupport (p * q) := by
  classical
  intro d hd
  rw [coeff_mul] at hd
  obtain ⟨⟨e, f⟩, hef, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have he : coeff e p ≠ 0 := left_ne_zero_of_mul h
  have hf : coeff f q ≠ 0 := right_ne_zero_of_mul h
  rw [← Finset.mem_antidiagonal.mp hef]
  exact (hp e he).add (hq f hf)

/-- The diagonal (balanced-degree) monomial subalgebra. -/
def balancedAlgebra (k : Type*) [CommSemiring k] (N : ℕ) :
    Subalgebra k (MvPolynomial (Vars N) k) where
  carrier := {p | HasBalancedSupport p}
  zero_mem' := by intro d hd; simp at hd
  one_mem' := hasBalancedSupport_monomial balanced_zero 1
  add_mem' := hasBalancedSupport_add
  mul_mem' := hasBalancedSupport_mul
  algebraMap_mem' a := hasBalancedSupport_monomial balanced_zero a

@[simp] theorem mem_balancedAlgebra {p : MvPolynomial (Vars N) k} :
    p ∈ balancedAlgebra k N ↔ HasBalancedSupport p := Iff.rfl

/-- Exponent vector of a degree-one Segre coordinate. -/
def segreExponent (j : Fin N → Fin 3) : Vars N →₀ ℕ :=
  ∑ b : Fin N, Finsupp.single (b, j b) 1

@[simp] theorem segreExponent_apply (j : Fin N → Fin 3) (b : Fin N) (c : Fin 3) :
    segreExponent j (b, c) = if j b = c then 1 else 0 := by
  classical
  simp only [segreExponent, Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single b]
  · simp [Finsupp.single_apply, Prod.mk.injEq]
  · intro a _ ha
    simp [Prod.mk.injEq, ha]
  · simp

@[simp] theorem blockDegree_segreExponent (j : Fin N → Fin 3) (b : Fin N) :
    blockDegree (segreExponent j) b = 1 := by
  classical
  simp [blockDegree]

theorem balanced_segreExponent (j : Fin N → Fin 3) : Balanced (segreExponent j) := by
  intro b c
  simp

/-- A degree-one Segre coordinate, as a polynomial in the original triples. -/
def segreMonomial (j : Fin N → Fin 3) : MvPolynomial (Vars N) k :=
  ∏ b : Fin N, X (b, j b)

theorem segreMonomial_eq_monomial (j : Fin N → Fin 3) :
    segreMonomial (k := k) j = monomial (segreExponent j) 1 := by
  classical
  simp [segreMonomial, segreExponent, monomial_sum_one, X]

theorem isMultiHomogeneousOfDegree_segreMonomial (j : Fin N → Fin 3) :
    IsMultiHomogeneousOfDegree (segreMonomial (k := k) j) 1 := by
  rw [segreMonomial_eq_monomial]
  exact isMultiHomogeneous_monomial (blockDegree_segreExponent j) 1

theorem segreMonomial_mem (j : Fin N → Fin 3) :
    segreMonomial (k := k) j ∈ balancedAlgebra k N := by
  rw [segreMonomial_eq_monomial]
  exact hasBalancedSupport_monomial (balanced_segreExponent j) 1

theorem exponent_eq_zero_of_blockDegree_zero {d : Vars N →₀ ℕ}
    (hd : ∀ b, blockDegree d b = 0) : d = 0 := by
  classical
  ext ⟨b, j⟩
  have h : d (b, j) ≤ blockDegree d b :=
    Finset.single_le_sum (f := fun j : Fin 3 => d (b, j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa [hd b] using h

theorem exists_segreExponent_le {d : Vars N →₀ ℕ} {r : ℕ}
    (hd : ∀ b, blockDegree d b = r + 1) :
    ∃ j : Fin N → Fin 3, segreExponent j ≤ d := by
  classical
  have hpos : ∀ b, ∃ j : Fin 3, 0 < d (b, j) := by
    intro b
    by_contra! h
    have hzero : blockDegree d b = 0 := by
      simp [blockDegree, Nat.eq_zero_of_le_zero (h _)]
    have := hd b
    omega
  choose j hj using hpos
  refine ⟨j, ?_⟩
  intro ⟨b, c⟩
  simp only [segreExponent_apply]
  split_ifs with h
  · subst c
    exact hj b
  · exact Nat.zero_le _

/-- A balanced monomial factors into degree-one Segre monomials.
This is the finite-generation step, proved by induction on the common degree. -/
theorem monomial_mem_adjoin_segre {d : Vars N →₀ ℕ} {r : ℕ}
    (hd : ∀ b, blockDegree d b = r) (a : k) :
    monomial d a ∈ Algebra.adjoin k (Set.range (segreMonomial (k := k) (N := N))) := by
  classical
  induction r generalizing d with
  | zero =>
    have : d = 0 := exponent_eq_zero_of_blockDegree_zero hd
    subst d
    exact Subalgebra.algebraMap_mem _ a
  | succ r ih =>
    obtain ⟨j, hj⟩ := exists_segreExponent_le hd
    have hde : segreExponent j + (d - segreExponent j) = d := add_tsub_cancel_of_le hj
    have hrem : ∀ b, blockDegree (d - segreExponent j) b = r := by
      intro b
      have h := congrArg (fun e => blockDegree e b) hde
      simp only [blockDegree_add, blockDegree_segreExponent, hd b] at h
      omega
    have hm : monomial d a = segreMonomial j * monomial (d - segreExponent j) a := by
      rw [segreMonomial_eq_monomial, monomial_mul, one_mul, hde]
    rw [hm]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨j, rfl⟩) (ih hrem)

/-- The balanced subalgebra is generated by the finitely many Segre coordinates. -/
theorem adjoin_segre_eq_balancedAlgebra [NeZero N] :
    Algebra.adjoin k (Set.range (segreMonomial (k := k) (N := N))) = balancedAlgebra k N := by
  classical
  apply le_antisymm
  · refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    exact segreMonomial_mem j
  · intro p hp
    rw [p.as_sum]
    apply Subalgebra.sum_mem
    intro d hd
    apply monomial_mem_adjoin_segre (r := blockDegree d 0)
    intro b
    exact hp d (mem_support_iff.mp hd) b 0

end BalancedAlgebra

instance balancedAlgebra_isNoetherianRing [CommRing k] [IsNoetherianRing k] [NeZero N] :
    IsNoetherianRing (balancedAlgebra k N) := by
  apply isNoetherianRing_of_fg
  exact Subalgebra.fg_def.mpr ⟨Set.range segreMonomial, Set.finite_range _,
    adjoin_segre_eq_balancedAlgebra⟩

section Retraction

variable [CommSemiring k]

/-- Keep just the monomials whose block degrees are all equal. -/
def balancedPart : MvPolynomial (Vars N) k →ₗ[k] MvPolynomial (Vars N) k := by
  classical
  exact
    { toFun := Finsupp.filter Balanced
      map_add' := fun _ _ => Finsupp.filter_add
      map_smul' := fun _ _ => Finsupp.filter_smul }

@[simp] theorem coeff_balancedPart (p : MvPolynomial (Vars N) k) (d : Vars N →₀ ℕ) :
    coeff d (balancedPart p) = if Balanced d then coeff d p else 0 := by
  classical
  exact Finsupp.filter_apply _ _ _

theorem balancedPart_mem (p : MvPolynomial (Vars N) k) :
    balancedPart p ∈ balancedAlgebra k N := by
  classical
  intro d hd
  by_contra h
  simp [h] at hd

@[simp] theorem balancedPart_of_mem {p : MvPolynomial (Vars N) k}
    (hp : p ∈ balancedAlgebra k N) : balancedPart p = p := by
  classical
  ext d
  rw [coeff_balancedPart]
  by_cases h : Balanced d
  · simp [h]
  · have hc : coeff d p = 0 := by
      by_contra hc
      exact h (hp d hc)
    simp [h, hc]

@[simp] theorem balancedPart_monomial (d : Vars N →₀ ℕ) (a : k) :
    balancedPart (monomial d a) = if Balanced d then monomial d a else 0 := by
  classical
  by_cases hd : Balanced d
  · simp only [if_pos hd]
    exact balancedPart_of_mem (hasBalancedSupport_monomial hd a)
  · simp only [if_neg hd]
    exact Finsupp.filter_single_of_neg Balanced hd

theorem balancedPart_monomial_mul {d : Vars N →₀ ℕ} (hd : Balanced d)
    (a : k) (q : MvPolynomial (Vars N) k) :
    balancedPart (monomial d a * q) = monomial d a * balancedPart q := by
  classical
  induction q using MvPolynomial.induction_on' with
  | monomial e b =>
    rw [monomial_mul, balancedPart_monomial, balancedPart_monomial]
    simp only [hd.add_iff_right]
    split_ifs <;> simp [monomial_mul]
  | add p q hp hq =>
    simp only [mul_add, map_add, hp, hq]

/-- The balanced-monomial projection is linear over the whole balanced subalgebra,
not merely over the coefficient field. -/
theorem balancedPart_mul {p : MvPolynomial (Vars N) k}
    (hp : p ∈ balancedAlgebra k N) (q : MvPolynomial (Vars N) k) :
    balancedPart (p * q) = p * balancedPart q := by
  classical
  calc
    balancedPart (p * q) =
        balancedPart ((∑ d ∈ p.support, monomial d (coeff d p)) * q) := by
      congr 2
      exact p.as_sum
    _ = ∑ d ∈ p.support, balancedPart (monomial d (coeff d p) * q) := by
      simp only [Finset.sum_mul, map_sum]
    _ = ∑ d ∈ p.support, monomial d (coeff d p) * balancedPart q := by
      apply Finset.sum_congr rfl
      intro d hd
      exact balancedPart_monomial_mul (hp d (mem_support_iff.mp hd)) _ _
    _ = p * balancedPart q := by rw [← Finset.sum_mul, ← p.as_sum]

/-- The same projection with codomain restricted to the balanced algebra. -/
def balancedRetract : MvPolynomial (Vars N) k →ₗ[k] balancedAlgebra k N :=
  balancedPart.codRestrict (balancedAlgebra k N).toSubmodule balancedPart_mem

@[simp] theorem coe_balancedRetract (p : MvPolynomial (Vars N) k) :
    (balancedRetract p : MvPolynomial (Vars N) k) = balancedPart p := rfl

@[simp] theorem balancedRetract_coe (p : balancedAlgebra k N) :
    balancedRetract (p : MvPolynomial (Vars N) k) = p := by
  apply Subtype.ext
  exact balancedPart_of_mem p.property

@[simp] theorem balancedRetract_mul (p : balancedAlgebra k N)
    (q : MvPolynomial (Vars N) k) :
    balancedRetract ((p : MvPolynomial (Vars N) k) * q) = p * balancedRetract q := by
  apply Subtype.ext
  exact balancedPart_mul p.property q

/-- Extending an ideal generated by balanced polynomials to the ambient polynomial
ring and contracting it back introduces no new balanced elements. -/
theorem mem_span_range_coe_iff {ι : Type*} [Fintype ι]
    (f : ι → balancedAlgebra k N) (p : balancedAlgebra k N) :
    (p : MvPolynomial (Vars N) k) ∈
        Ideal.span (Set.range (fun i => (f i : MvPolynomial (Vars N) k))) ↔
      p ∈ Ideal.span (Set.range f) := by
  classical
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
    have h := congrArg balancedRetract ha
    have hsum : (∑ i, balancedRetract (a i) * f i) = p := by
      simpa only [smul_eq_mul, map_sum, mul_comm, balancedRetract_mul,
        balancedRetract_coe] using h
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := i))
  · intro hp
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hp
    have h := congrArg (balancedAlgebra k N).val ha
    simp only [smul_eq_mul, map_sum, map_mul] at h
    change ∑ i, (a i : MvPolynomial (Vars N) k) * (f i : MvPolynomial (Vars N) k) =
      (p : MvPolynomial (Vars N) k) at h
    rw [← h]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_range_self (x := i))

theorem mem_radical_span_range_coe_iff {ι : Type*} [Fintype ι]
    (f : ι → balancedAlgebra k N) (p : balancedAlgebra k N) :
    (p : MvPolynomial (Vars N) k) ∈
        (Ideal.span (Set.range (fun i => (f i : MvPolynomial (Vars N) k)))).radical ↔
      p ∈ (Ideal.span (Set.range f)).radical := by
  simp only [Ideal.mem_radical_iff, ← Subalgebra.coe_pow, mem_span_range_coe_iff]

end Retraction

section Height

variable [Field k]

/-- A Segre coordinate as an element of the balanced subalgebra. -/
def segre (j : Fin N → Fin 3) : balancedAlgebra k N :=
  ⟨segreMonomial j, segreMonomial_mem j⟩

@[simp] theorem coe_segre (j : Fin N → Fin 3) :
    (segre (k := k) j : MvPolynomial (Vars N) k) = segreMonomial j := rfl

theorem segreMonomial_ne_zero (j : Fin N → Fin 3) :
    segreMonomial (k := k) j ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ => X_ne_zero _)

@[simp] theorem constantCoeff_segreMonomial [NeZero N] (j : Fin N → Fin 3) :
    constantCoeff (segreMonomial (k := k) j) = 0 := by
  classical
  simp [segreMonomial, NeZero.ne N]

/-- Set a specified finite set of ambient variables to zero. -/
def killVars (s : Finset (Vars N)) :
    MvPolynomial (Vars N) k →ₐ[k] MvPolynomial (Vars N) k := by
  classical
  exact aeval (fun v => if v ∈ s then 0 else X v)

@[simp] theorem killVars_X (s : Finset (Vars N)) (v : Vars N) :
    killVars (k := k) s (X v) = if v ∈ s then 0 else X v := by
  classical
  simp [killVars]

theorem killVars_comp_of_subset {s t : Finset (Vars N)} (hst : s ⊆ t) :
    (killVars (k := k) t).comp (killVars s) = killVars t := by
  classical
  ext v
  by_cases h : v ∈ s
  · simp [h, hst h]
  · simp [h]

theorem zero_aeval_comp_killVars (s : Finset (Vars N)) :
    (aeval (R := k) (fun _ : Vars N => (0 : k))).comp (killVars (k := k) s) =
      aeval (R := k) (fun _ : Vars N => (0 : k)) := by
  classical
  ext v
  by_cases h : v ∈ s <;> simp [h]

/-- Contract a prime variable ideal to the balanced subalgebra. -/
def killedIdeal (s : Finset (Vars N)) : Ideal (balancedAlgebra k N) :=
  RingHom.ker (((killVars s).comp (balancedAlgebra k N).val).toRingHom)

@[simp] theorem mem_killedIdeal (s : Finset (Vars N)) (p : balancedAlgebra k N) :
    p ∈ killedIdeal s ↔ killVars s (p : MvPolynomial (Vars N) k) = 0 := Iff.rfl

instance killedIdeal_isPrime (s : Finset (Vars N)) :
    (killedIdeal (k := k) s).IsPrime := RingHom.ker_isPrime _

/-- The vertex of the affine Segre cone: the augmentation ideal. -/
def vertexIdeal (k : Type*) [Field k] (N : ℕ) : Ideal (balancedAlgebra k N) :=
  RingHom.ker (((aeval (fun _ : Vars N => (0 : k))).comp
    (balancedAlgebra k N).val).toRingHom)

@[simp] theorem mem_vertexIdeal (p : balancedAlgebra k N) :
    p ∈ vertexIdeal k N ↔ constantCoeff (p : MvPolynomial (Vars N) k) = 0 := by
  change aeval (fun _ : Vars N => (0 : k)) (p : MvPolynomial (Vars N) k) = 0 ↔ _
  simp

instance vertexIdeal_isPrime : (vertexIdeal k N).IsPrime := RingHom.ker_isPrime _

theorem killedIdeal_mono {s t : Finset (Vars N)} (hst : s ⊆ t) :
    killedIdeal (k := k) s ≤ killedIdeal t := by
  intro p hp
  rw [mem_killedIdeal] at hp ⊢
  have h := congrArg (fun φ : MvPolynomial (Vars N) k →ₐ[k] MvPolynomial (Vars N) k =>
    φ (p : MvPolynomial (Vars N) k)) (killVars_comp_of_subset hst)
  simpa [hp] using h.symm

theorem killedIdeal_le_vertexIdeal (s : Finset (Vars N)) :
    killedIdeal (k := k) s ≤ vertexIdeal k N := by
  intro p hp
  rw [mem_killedIdeal] at hp
  rw [mem_vertexIdeal]
  have h := congrArg (fun φ : MvPolynomial (Vars N) k →ₐ[k] k =>
    φ (p : MvPolynomial (Vars N) k)) (zero_aeval_comp_killVars s)
  simpa [hp] using h.symm

theorem killVars_segreMonomial_of_disjoint (s : Finset (Vars N)) (j : Fin N → Fin 3)
    (hj : ∀ b, (b, j b) ∉ s) :
    killVars (k := k) s (segreMonomial j) = segreMonomial j := by
  classical
  simp [segreMonomial, hj]

theorem killVars_segreMonomial_of_mem (s : Finset (Vars N)) (j : Fin N → Fin 3)
    (b : Fin N) (hb : (b, j b) ∈ s) :
    killVars (k := k) s (segreMonomial j) = 0 := by
  classical
  simp only [segreMonomial, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [hb])

/-- Choose the newly killed variable in its block and the protected coordinate `2`
in every other block. -/
def separatingChoice (v : Vars N) (b : Fin N) : Fin 3 :=
  if b = v.1 then v.2 else 2

theorem separatingChoice_avoids {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) {v : Vars N} (hv : v ∉ s) :
    ∀ b, (b, separatingChoice v b) ∉ s := by
  intro b
  by_cases h : b = v.1
  · subst b
    simpa [separatingChoice] using hv
  · simpa [separatingChoice, h] using hprotect b

/-- Each additional killed coordinate strictly increases the contracted prime ideal. -/
theorem killedIdeal_lt_insert {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) {v : Vars N} (hv : v ∉ s) :
    killedIdeal (k := k) s < killedIdeal (insert v s) := by
  classical
  refine lt_of_le_of_ne (killedIdeal_mono (Finset.subset_insert _ _)) ?_
  intro heq
  have hmem : segre (k := k) (separatingChoice v) ∈ killedIdeal (insert v s) := by
    rw [mem_killedIdeal, coe_segre]
    apply killVars_segreMonomial_of_mem _ _ v.1
    simp [separatingChoice]
  rw [← heq, mem_killedIdeal, coe_segre,
    killVars_segreMonomial_of_disjoint s _ (separatingChoice_avoids hprotect hv)] at hmem
  exact segreMonomial_ne_zero _ hmem

/-- The final strict step kills the remaining positive-degree balanced monomials. -/
theorem killedIdeal_lt_vertexIdeal [NeZero N] {s : Finset (Vars N)}
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) :
    killedIdeal (k := k) s < vertexIdeal k N := by
  refine lt_of_le_of_ne (killedIdeal_le_vertexIdeal s) ?_
  intro heq
  have hmem : segre (k := k) (fun _ : Fin N => 2) ∈ vertexIdeal k N := by
    simp
  rw [← heq, mem_killedIdeal, coe_segre,
    killVars_segreMonomial_of_disjoint s _ hprotect] at hmem
  exact segreMonomial_ne_zero _ hmem

/-- The height of a contracted variable ideal is at least the number of killed
coordinates, as long as one coordinate in every block remains protected. -/
theorem card_le_height_killedIdeal (s : Finset (Vars N))
    (hprotect : ∀ b, (b, (2 : Fin 3)) ∉ s) :
    (s.card : ℕ∞) ≤ (killedIdeal (k := k) s).height := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    have hs : ∀ b, (b, (2 : Fin 3)) ∉ s := by
      intro b hb
      exact hprotect b (Finset.mem_insert_of_mem hb)
    have hlt := Ideal.primeHeight_add_one_le_of_lt
      (killedIdeal_lt_insert (k := k) hs hv)
    rw [← Ideal.height_eq_primeHeight, ← Ideal.height_eq_primeHeight] at hlt
    calc
      ((insert v s).card : ℕ∞) = (s.card : ℕ∞) + 1 := by simp [hv]
      _ ≤ (killedIdeal (k := k) s).height + 1 := add_le_add (ih hs) le_rfl
      _ ≤ (killedIdeal (k := k) (insert v s)).height := hlt

/-- The Segre cone vertex has height at least `2*N + 1`.
The proof constructs all `2*N + 1` strict prime-ideal steps explicitly. -/
theorem vertexIdeal_height_lower_bound [NeZero N] :
    (2 * N + 1 : ℕ∞) ≤ (vertexIdeal k N).height := by
  classical
  let s : Finset (Vars N) := Finset.univ ×ˢ ({0, 1} : Finset (Fin 3))
  have hs : ∀ b, (b, (2 : Fin 3)) ∉ s := by
    intro b
    simp [s]
  have hcard : s.card = 2 * N := by
    simp [s, Finset.card_product, Nat.mul_comm]
  have hlt := Ideal.primeHeight_add_one_le_of_lt
    (killedIdeal_lt_vertexIdeal (k := k) hs)
  rw [← Ideal.height_eq_primeHeight, ← Ideal.height_eq_primeHeight] at hlt
  calc
    (2 * N + 1 : ℕ∞) = (s.card : ℕ∞) + 1 := by simp [hcard]
    _ ≤ (killedIdeal (k := k) s).height + 1 :=
      add_le_add (card_le_height_killedIdeal s hs) le_rfl
    _ ≤ (vertexIdeal k N).height := hlt

end Height

section CommonZeros

variable [Field k]

theorem IsMultiHomogeneousOfDegree.constantCoeff_eq_zero [NeZero N]
    {f : MvPolynomial (Vars N) k} {r : ℕ}
    (hf : IsMultiHomogeneousOfDegree f r) (hr : 0 < r) : constantCoeff f = 0 := by
  change coeff 0 f = 0
  by_contra h
  have hdeg := hf 0 h (0 : Fin N)
  simp only [blockDegree_zero] at hdeg
  omega

/-- On an assignment with one zero block, any balanced polynomial evaluates
to its constant coefficient. -/
theorem eval_eq_constantCoeff_of_block_zero [NeZero N]
    {p : MvPolynomial (Vars N) k} (hp : p ∈ balancedAlgebra k N)
    {x : Vars N → k} {b : Fin N} (hx : ∀ j, x (b, j) = 0) :
    eval x p = constantCoeff p := by
  classical
  rw [← adjoin_segre_eq_balancedAlgebra] at hp
  refine Algebra.adjoin_induction (p := fun p _ => eval x p = constantCoeff p)
    ?_ ?_ ?_ ?_ hp
  · rintro _ ⟨j, rfl⟩
    rw [constantCoeff_segreMonomial]
    simp only [segreMonomial, map_prod, eval_X]
    exact Finset.prod_eq_zero (Finset.mem_univ b) (hx (j b))
  · intro a
    simp
  · intro p q _ _ hp hq
    simp only [map_add, hp, hq]
  · intro p q _ _ hp hq
    simp only [map_mul, hp, hq]

variable [IsAlgClosed k] [NeZero N]

/-- If balanced polynomials with zero constant term have no common zero with all
blocks nonzero, their ideal in the balanced subalgebra has radical the vertex.
This is the affine Nullstellensatz plus the explicitly proved retraction. -/
theorem radical_span_eq_vertex_of_no_common_zero {ι : Type*} [Fintype ι]
    (f : ι → balancedAlgebra k N) (hf : ∀ i, f i ∈ vertexIdeal k N)
    (hno : ¬ ∃ x : Vars N → k, (∀ b, ∃ j, x (b, j) ≠ 0) ∧
      ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0) :
    (Ideal.span (Set.range f)).radical = vertexIdeal k N := by
  classical
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff (vertexIdeal_isPrime (k := k) (N := N))).mpr
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hf i
  · intro p hp
    apply (mem_radical_span_range_coe_iff f p).mp
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro x hx
    have hfx : ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0 := by
      intro i
      exact hx _ (Ideal.mem_span_range_self (x := i))
    have hbad : ∃ b, ∀ j, x (b, j) = 0 := by
      by_contra! hgood
      exact hno ⟨x, hgood, hfx⟩
    obtain ⟨b, hb⟩ := hbad
    change eval x (p : MvPolynomial (Vars N) k) = 0
    rw [eval_eq_constantCoeff_of_block_zero p.property hb]
    exact (mem_vertexIdeal p).mp hp

/-- A slightly stronger algebraic theorem: the polynomials may be sums of balanced
monomials of different degrees, provided all constant coefficients vanish. -/
theorem exists_common_zero_balanced {q : ℕ} (hq : q ≤ 2 * N)
    (f : Fin q → balancedAlgebra k N) (hf : ∀ i, f i ∈ vertexIdeal k N) :
    ∃ x : Vars N → k, (∀ b, ∃ j, x (b, j) ≠ 0) ∧
      ∀ i, eval x (f i : MvPolynomial (Vars N) k) = 0 := by
  classical
  by_contra hno
  have hrad := radical_span_eq_vertex_of_no_common_zero f hf hno
  have hmin : vertexIdeal k N ∈ (Ideal.span (Set.range f)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hupper := Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_range f) hmin
  have hcard : (Set.range f).ncard ≤ q := by
    simpa only [Set.image_univ, Set.ncard_univ, Nat.card_fin] using
      (Set.ncard_image_le (s := Set.univ) (f := f) Set.finite_univ)
  have hbound : (2 * N + 1 : ℕ∞) ≤ q :=
    (vertexIdeal_height_lower_bound (k := k) (N := N)).trans
      (hupper.trans (by exact_mod_cast hcard))
  have hnat : 2 * N + 1 ≤ q := by exact_mod_cast hbound
  omega

end CommonZeros

/-- **Multiprojective common-zero theorem.** Over an algebraically closed field,
at most `2*N` polynomials of common positive degree in every one of `N` blocks
of three variables have a common zero with no zero block.

The proof is entirely affine commutative algebra: finite generation of the balanced
monomial algebra, a linear retraction, the Nullstellensatz, an explicit chain of
prime ideals, and Krull's height theorem. -/
theorem exists_common_zero [Field k] [IsAlgClosed k] {q r : ℕ}
    (f : Fin q → MvPolynomial (Fin N × Fin 3) k)
    (hN : 0 < N) (hr : 0 < r) (hq : q ≤ 2 * N)
    (hf : ∀ i, IsMultiHomogeneousOfDegree (f i) r) :
    ∃ x : (Fin N × Fin 3) → k,
      (∀ b : Fin N, (fun j : Fin 3 => x (b, j)) ≠ 0) ∧
      ∀ i : Fin q, eval x (f i) = 0 := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let fs : Fin q → balancedAlgebra k N :=
    fun i => ⟨f i, (hf i).hasBalancedSupport⟩
  have hfs : ∀ i, fs i ∈ vertexIdeal k N := by
    intro i
    rw [mem_vertexIdeal]
    exact (hf i).constantCoeff_eq_zero hr
  obtain ⟨x, hx, hfx⟩ := exists_common_zero_balanced hq fs hfs
  refine ⟨x, ?_, hfx⟩
  intro b hb
  obtain ⟨j, hj⟩ := hx b
  exact hj (congrFun hb j)

/-- An entry point with the multihomogeneity hypothesis fully expanded in terms
of coefficients and blockwise sums of exponents. -/
theorem exists_common_zero_of_coeff [Field k] [IsAlgClosed k] {q r : ℕ}
    (f : Fin q → MvPolynomial (Fin N × Fin 3) k)
    (hN : 0 < N) (hr : 0 < r) (hq : q ≤ 2 * N)
    (hf : ∀ i d, coeff d (f i) ≠ 0 → ∀ b : Fin N, ∑ j : Fin 3, d (b, j) = r) :
    ∃ x : (Fin N × Fin 3) → k,
      (∀ b : Fin N, (fun j : Fin 3 => x (b, j)) ≠ 0) ∧
      ∀ i : Fin q, eval x (f i) = 0 :=
  exists_common_zero f hN hr hq hf

/-- The same result with the assignment written as a family of nonzero vectors. -/
theorem exists_common_zero_vectors [Field k] [IsAlgClosed k] {q r : ℕ}
    (f : Fin q → MvPolynomial (Fin N × Fin 3) k)
    (hN : 0 < N) (hr : 0 < r) (hq : q ≤ 2 * N)
    (hf : ∀ i, IsMultiHomogeneousOfDegree (f i) r) :
    ∃ x : Fin N → Fin 3 → k, (∀ b, x b ≠ 0) ∧
      ∀ i, eval (fun v => x v.1 v.2) (f i) = 0 := by
  obtain ⟨x, hx, hfx⟩ := exists_common_zero f hN hr hq hf
  exact ⟨fun b j => x (b, j), hx, hfx⟩

end KoetheMultiProjective

end KoetheProofPart01

/- ## KoethePencilDefs -/

noncomputable section KoetheProofPart02

set_option autoImplicit false


namespace KoetheCounterexample

abbrev Triple (k : Type*) := Fin 3 → k

/-- A homogeneous three-letter pencil, affine in one central parameter, whose
parameter coefficient is supported in the distinguished row. -/
structure Pencil (k : Type*) [Field k] (d : ℕ) where
  constant : Fin 3 → Matrix (Fin (d + 1)) (Fin (d + 1)) k
  linear : Fin 3 → Matrix (Fin (d + 1)) (Fin (d + 1)) k
  linear_off_root : ∀ i row col, row ≠ 0 → linear i row col = 0

namespace Pencil

variable {k : Type*} [Field k] {d : ℕ}

@[ext] theorem ext {P Q : Pencil k d}
    (hc : P.constant = Q.constant) (hl : P.linear = Q.linear) : P = Q := by
  cases P
  cases Q
  simp_all

instance [Countable k] : Countable (Pencil k d) := by
  letI : Countable (Matrix (Fin (d + 1)) (Fin (d + 1)) k) := by
    change Countable (Fin (d + 1) → Fin (d + 1) → k)
    infer_instance
  exact Function.Injective.countable (f := fun P : Pencil k d => (P.constant, P.linear))
    (fun _ _ h => Pencil.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Evaluation at a constant letter vector. -/
def eval (P : Pencil k d) (v : Triple k) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial k) :=
  fun row col => Polynomial.C (∑ i : Fin 3, v i * P.constant i row col) +
    Polynomial.X * Polynomial.C (∑ i : Fin 3, v i * P.linear i row col)

/-- Evaluation at three elements of an arbitrary algebra. -/
def lift {R : Type*} [Ring R] [Algebra k R] (P : Pencil k d) (a : Fin 3 → R) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial R) :=
  fun row col => Polynomial.C (∑ i : Fin 3, algebraMap k R (P.constant i row col) * a i) +
    Polynomial.X * Polynomial.C
      (∑ i : Fin 3, algebraMap k R (P.linear i row col) * a i)

/-- Forward chronological multiplication. This is the transfer convention for
backward shifts `(a_i u)(n) = v_n(i) u(n+1)`. -/
def wordProd (P : Pencil k d) (w : List (Triple k)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial k) :=
  (w.map P.eval).prod

@[simp] theorem wordProd_nil (P : Pencil k d) : P.wordProd [] = 1 := rfl

@[simp] theorem wordProd_append (P : Pencil k d) (u w : List (Triple k)) :
    P.wordProd (u ++ w) = P.wordProd u * P.wordProd w := by
  simp [wordProd]

def window (P : Pencil k d) (v : ℕ → Triple k) (start len : ℕ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial k) :=
  P.wordProd (List.ofFn fun i : Fin len => v (start + i.val))

end Pencil

/-- A finite periodic collection of assigned nonzero letter vectors. Unassigned
occurrences of a residue remain independent choices. -/
structure PeriodicMask (k : Type*) [Field k] where
  period : ℕ
  period_pos : 0 < period
  value : Fin period → Option (Triple k)
  nonzero : ∀ i v, value i = some v → v ≠ 0

namespace PeriodicMask

variable {k : Type*} [Field k]

def lookup (M : PeriodicMask k) (n : ℕ) : Option (Triple k) :=
  M.value ⟨n % M.period, Nat.mod_lt n M.period_pos⟩

noncomputable def holes (M : PeriodicMask k) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => M.value i = none).card

noncomputable def assigned (M : PeriodicMask k) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => M.value i ≠ none).card

def Compatible (M : PeriodicMask k) (w : List (Triple k)) : Prop :=
  ∀ (i : Fin w.length) (z : Triple k), M.lookup i.val = some z → w.get i = z

def SeqCompatible (M : PeriodicMask k) (v : ℕ → Triple k) : Prop :=
  ∀ (n : ℕ) (z : Triple k), M.lookup n = some z → v n = z

end PeriodicMask

/-- The algebraic matrix-mortality property needed by the mask construction. -/
def MaskMortality (k : Type*) [Field k] : Prop :=
  ∀ (d : ℕ) (P : Pencil k d) (M : PeriodicMask k),
    M.period < 2 * M.holes →
    ∃ w : List (Triple k), M.period ≤ w.length ∧ M.period ∣ w.length ∧
      (∀ z ∈ w, z ≠ 0) ∧ M.Compatible w ∧ P.wordProd w = 0

/-- A nonvanishing edge sequence killing every one-row pencil on uniformly
bounded windows. Nil bounds are permitted to depend on the pencil. -/
def UniversalMortalSequence (k : Type*) [Field k] (v : ℕ → Triple k) : Prop :=
  (∀ n, v n ≠ 0) ∧ ∀ (d : ℕ) (P : Pencil k d),
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, P.window v n N = 0

end KoetheCounterexample

end KoetheProofPart02

/- ## KoethePencilMortalityMinors -/

noncomputable section KoetheProofPart03

set_option autoImplicit false

/-
# Determinantal rank and sandwich compression

The mortality proof uses vanishing minors as a natural-number rank bound.
This avoids choosing bases for exterior powers.  All matrix products in this
file are ordinary products over a commutative scalar ring.
-/


open scoped BigOperators
open Matrix

namespace KoetheCounterexample.Mortality

section Determinants

variable {R : Type*} [CommRing R] {n m : Type*}
variable {r : ℕ}

/-- All minors of a specified size vanish.  Repeated rows or columns are allowed
in the indexing functions; their determinants are automatically zero. -/
def MinorsVanish (A : Matrix n n R) (r : ℕ) : Prop :=
  ∀ I J : Fin r → n, (A.submatrix I J).det = 0

theorem det_submatrix_zero_of_not_injective (A : Matrix n m R)
    (I : Fin r → n) (J : Fin r → m) (hI : ¬ Function.Injective I) :
    (A.submatrix I J).det = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hI
  exact Matrix.det_zero_of_row_eq hne (by ext c; simp [hij])

theorem injective_of_det_submatrix_ne_zero (A : Matrix n m R)
    (I : Fin r → n) (J : Fin r → m) (h : (A.submatrix I J).det ≠ 0) :
    Function.Injective I := by
  by_contra hi
  exact h (det_submatrix_zero_of_not_injective A I J hi)

theorem minorsVanish_above [Fintype n] (A : Matrix n n R) (h : Fintype.card n < r) :
    MinorsVanish A r := by
  intro I J
  apply det_submatrix_zero_of_not_injective A I J
  intro hi
  have := Fintype.card_le_of_injective I hi
  simp only [Fintype.card_fin] at this
  omega

theorem eq_zero_of_minorsVanish_one (A : Matrix n n R) (h : MinorsVanish A 1) :
    A = 0 := by
  ext i j
  simpa using h (fun _ => i) (fun _ => j)

/-- Expansion by multilinearity in the rows.  Unlike a compound-matrix formula,
this involves no ordering of subsets and no division by a factorial. -/
theorem det_mul_expand_rows [Fintype n] (A : Matrix (Fin r) n R) (B : Matrix n (Fin r) R) :
    (A * B).det = ∑ f : Fin r → n,
      (∏ i : Fin r, A i (f i)) * (B.submatrix f id).det := by
  classical
  let D := (Matrix.detRowAlternating : (Fin r → R) [⋀^Fin r]→ₗ[R] R).toMultilinearMap
  have heq : A * B = fun i => ∑ j : n, A i j • B j := by
    ext i j
    simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change D (A * B) = _
  rw [heq, D.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [D.map_smul_univ]
  rfl

/-- Restricting only the outside indices of a rectangular product. -/
theorem submatrix_mul_outer [Fintype n] {l o p q : Type*}
    (A : Matrix l n R) (B : Matrix n o R) (I : p → l) (J : q → o) :
    (A * B).submatrix I J = A.submatrix I id * B.submatrix id J := by
  simpa using (Matrix.submatrix_mul_equiv A B I (Equiv.refl n) J).symm

theorem det_map {S : Type*} [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin r) (Fin r) R) :
    (A.map φ).det = φ A.det := (φ.map_det A).symm

end Determinants

section Compression

variable {K : Type*} [Field K] {n : Type*} {r : ℕ}

/-- A nonzero `r`-minor, together with vanishing `(r+1)`-minors, gives the
usual pivot factorization.  The inverse is taken only over a field. -/
theorem pivot_factorization (P : Matrix n n K)
    (I J : Fin r → n) (hp : (P.submatrix I J).det ≠ 0)
    (hnext : MinorsVanish P (r + 1)) :
    P = P.submatrix id J * (P.submatrix I J)⁻¹ * P.submatrix I id := by
  classical
  let A := P.submatrix I J
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hp)
  ext i j
  let B : Matrix (Fin r) (Fin 1) K := fun a _ => P (I a) j
  let C : Matrix (Fin 1) (Fin r) K := fun _ b => P i (J b)
  let D : Matrix (Fin 1) (Fin 1) K := fun _ _ => P i j
  let I' : Fin r ⊕ Fin 1 → n := Sum.elim I (fun _ => i)
  let J' : Fin r ⊕ Fin 1 → n := Sum.elim J (fun _ => j)
  have hz : (P.submatrix I' J').det = 0 := by
    let e : Fin (r + 1) ≃ (Fin r ⊕ Fin 1) := finSumFinEquiv.symm
    have h := hnext (I' ∘ e) (J' ∘ e)
    simpa only [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self] using h
  have hblocks : P.submatrix I' J' = Matrix.fromBlocks A B C D := by
    ext a b
    cases a <;> cases b <;> rfl
  rw [hblocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    Matrix.det_unique (D - C * A⁻¹ * B)] at hz
  have hz' := (mul_eq_zero.mp hz).resolve_left hp
  change P i j - (P.submatrix id J * (P.submatrix I J)⁻¹ *
    P.submatrix I id) i j = 0 at hz'
  exact sub_eq_zero.mp hz'

/-- The pivot detects every `r`-minor of a sandwiched product. -/
theorem sandwich_minors_vanish_field [Fintype n] (P C : Matrix n n K)
    (I J : Fin r → n) (hp : (P.submatrix I J).det ≠ 0)
    (hnext : MinorsVanish P (r + 1))
    (hz : ((P * C * P).submatrix I J).det = 0) :
    MinorsVanish (P * C * P) r := by
  classical
  let A := P.submatrix I J
  let U := P.submatrix id J
  let V := P.submatrix I id
  have hP : P = U * A⁻¹ * V := pivot_factorization P I J hp hnext
  have hT : (V * C * U).det = 0 := by
    simpa only [submatrix_mul_outer, Matrix.submatrix_submatrix,
      Matrix.submatrix_id_id, Function.comp_id, Function.id_comp] using hz
  have hB : P * C * P = U * A⁻¹ * (V * C * U) * A⁻¹ * V := by
    calc
      P * C * P = (U * A⁻¹ * V) * C * (U * A⁻¹ * V) :=
        congrArg₂ (fun X Y => X * C * Y) hP hP
      _ = _ := by simp only [Matrix.mul_assoc]
  intro I' J'
  rw [hB]
  simp only [submatrix_mul_outer, Matrix.submatrix_id_id]
  simp only [Matrix.det_mul, hT, mul_zero, zero_mul]

end Compression

section DomainCompression

variable {R : Type*} [CommRing R] [IsDomain R] {n : Type*} [Fintype n] {r : ℕ}

/-- Polynomial/domain version of sandwich compression.  Localization is used
only to invert the fixed nonzero pivot; injectivity returns the identity to
its original commutative domain. -/
theorem sandwich_minors_vanish (P C : Matrix n n R)
    (I J : Fin r → n) (hp : (P.submatrix I J).det ≠ 0)
    (hnext : MinorsVanish P (r + 1))
    (hz : ((P * C * P).submatrix I J).det = 0) :
    MinorsVanish (P * C * P) r := by
  classical
  let φ := algebraMap R (FractionRing R)
  have hφ : Function.Injective φ := IsFractionRing.injective R (FractionRing R)
  have hp' : ((P.map φ).submatrix I J).det ≠ 0 := by
    rw [Matrix.submatrix_map, det_map]
    exact fun h => hp (hφ (by simpa using h))
  have hnext' : MinorsVanish (P.map φ) (r + 1) := by
    intro I' J'
    rw [Matrix.submatrix_map, det_map, hnext I' J', map_zero]
  have hz' : (((P.map φ) * (C.map φ) * (P.map φ)).submatrix I J).det = 0 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, Matrix.submatrix_map,
      det_map, hz, map_zero]
  have h := sandwich_minors_vanish_field (P.map φ) (C.map φ) I J hp' hnext' hz'
  intro I' J'
  apply hφ
  simpa only [map_zero, ← det_map, ← Matrix.submatrix_map,
    Matrix.map_mul] using h I' J'

end DomainCompression

end KoetheCounterexample.Mortality

end KoetheProofPart03

/- ## KoethePencilMortalityDegree -/

noncomputable section KoetheProofPart04

set_option autoImplicit false

/-
# The one-row parameter-degree bound

Multilinearity in the rows expands a minor of a product into row products
of the first factor and minors of the remaining factors.  Repeated rows
make the latter minors zero.  Thus a single parameter row contributes at
most one to the degree per factor, not the size of the minor.
-/


open scoped BigOperators
open Matrix Polynomial

namespace KoetheCounterexample.Mortality

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R] {d r : ℕ}

theorem lift_entry_natDegree_le (P : Pencil k d) (a : Fin 3 → R)
    (i j : Fin (d + 1)) : (P.lift a i j).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp only [Polynomial.natDegree_C, Nat.zero_le]
  · exact (Polynomial.natDegree_mul_C_le _ _).trans Polynomial.natDegree_X_le

theorem lift_entry_natDegree_off_root (P : Pencil k d) (a : Fin 3 → R)
    (i j : Fin (d + 1)) (hi : i ≠ 0) : (P.lift a i j).natDegree = 0 := by
  simp only [Pencil.lift, P.linear_off_root _ _ _ hi, map_zero, zero_mul,
    Finset.sum_const_zero, mul_zero, add_zero, Polynomial.natDegree_C]

/-- A product using distinct rows of one factor has parameter degree at most one. -/
theorem lift_row_prod_natDegree_le (P : Pencil k d) (a : Fin 3 → R)
    (I : Fin r → Fin (d + 1)) (f : Fin r → Fin (d + 1))
    (hI : Function.Injective I) :
    (∏ i : Fin r, P.lift a (I i) (f i)).natDegree ≤ 1 := by
  classical
  apply (Polynomial.natDegree_prod_le _ _).trans
  by_cases hroot : ∃ i, I i = 0
  · obtain ⟨i, hi⟩ := hroot
    rw [Finset.sum_eq_single i]
    · exact lift_entry_natDegree_le P a _ _
    · intro j _ hji
      exact lift_entry_natDegree_off_root P a _ _
        (fun hj => hji (hI (hj.trans hi.symm)))
    · simp
  · have hsum : (∑ i : Fin r, (P.lift a (I i) (f i)).natDegree) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact lift_entry_natDegree_off_root P a _ _ (fun hi => hroot ⟨i, hi⟩)
    omega

/-- Every minor of a forward word of lifted letters has degree at most the
word length.  The coefficient ring is an arbitrary commutative `k`-algebra. -/
theorem det_liftWord_natDegree_le (P : Pencil k d) (w : List (Fin 3 → R))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I) :
    ((((w.map P.lift).prod).submatrix I J).det).natDegree ≤ w.length := by
  classical
  induction w generalizing I J with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.length_nil]
    have hone : (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) R[X]) =
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) R).map Polynomial.C := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [hone, Matrix.submatrix_map, det_map]
    simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [submatrix_mul_outer, det_mul_expand_rows]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro f _
    simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix,
      Function.id_comp, Function.comp_id]
    by_cases hf : Function.Injective f
    · have h := Polynomial.natDegree_mul_le_of_le
        (lift_row_prod_natDegree_le P a I f hI) (ih f J hf)
      simpa only [Nat.add_comm] using h
    · rw [det_submatrix_zero_of_not_injective _ f J hf]
      simp

end KoetheCounterexample.Mortality

end KoetheProofPart04

/- ## KoethePencilMortalityHomogeneous -/

noncomputable section KoetheProofPart05

set_option autoImplicit false

/-
# Coefficientwise multihomogeneity for matrix words

The central parameter is a univariate polynomial variable.  Its coefficient
ring is a multivariate polynomial ring whose variables are grouped into
independent triples.  The zero polynomial is homogeneous of every degree.
-/


open scoped BigOperators
open KoetheMultiProjective

namespace KoetheCounterexample.Mortality

abbrev HoleRing (k : Type*) [CommSemiring k] (N : ℕ) :=
  MvPolynomial (Fin N × Fin 3) k

/-- The multidegree contributed by one occurrence of block `b`. -/
def blockUnit {N : ℕ} (b : Fin N) : Fin N → ℕ := fun c => if c = b then 1 else 0

section Homogeneity

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The coefficients in the central parameter are all multihomogeneous of
one and the same specified multidegree. -/
def CoeffHom (p : Polynomial (HoleRing k N)) (e : Fin N → ℕ) : Prop :=
  ∀ j, IsMultiHomogeneous (p.coeff j) e

theorem multiHom_sum {ι : Type*} (s : Finset ι) (f : ι → HoleRing k N)
    {e : Fin N → ℕ} (hf : ∀ i ∈ s, IsMultiHomogeneous (f i) e) :
    IsMultiHomogeneous (∑ i ∈ s, f i) e := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem multiHom_C (a : k) :
    IsMultiHomogeneous (MvPolynomial.C a : HoleRing k N) 0 := by
  exact isMultiHomogeneous_monomial (fun _ => blockDegree_zero _) a

theorem multiHom_X (b : Fin N) (j : Fin 3) :
    IsMultiHomogeneous (MvPolynomial.X (b, j) : HoleRing k N) (blockUnit b) := by
  apply isMultiHomogeneous_monomial
  intro c
  by_cases h : c = b
  · subst c
    simp [blockDegree, blockUnit, Finsupp.single_apply]
  · simp [blockDegree, blockUnit, h]

@[simp] theorem coeffHom_zero (e : Fin N → ℕ) :
    CoeffHom (0 : Polynomial (HoleRing k N)) e := by
  intro j
  simp

theorem coeffHom_C {a : HoleRing k N} {e : Fin N → ℕ}
    (ha : IsMultiHomogeneous a e) : CoeffHom (Polynomial.C a) e := by
  intro j
  by_cases h : j = 0
  · simpa only [Polynomial.coeff_C, if_pos h] using ha
  · simp only [Polynomial.coeff_C, if_neg h, isMultiHomogeneous_zero]

@[simp] theorem coeffHom_one : CoeffHom (1 : Polynomial (HoleRing k N)) 0 := by
  simpa only [map_one] using coeffHom_C (multiHom_C (N := N) (1 : k))

theorem coeffHom_intCast (z : ℤ) :
    CoeffHom (z : Polynomial (HoleRing k N)) 0 := by
  simpa only [map_intCast] using coeffHom_C (multiHom_C (N := N) (z : k))

theorem coeffHom_X : CoeffHom (Polynomial.X : Polynomial (HoleRing k N)) 0 := by
  intro j
  by_cases h : 1 = j
  · simpa only [Polynomial.coeff_X, if_pos h, map_one] using
      multiHom_C (N := N) (1 : k)
  · simp only [Polynomial.coeff_X, if_neg h, isMultiHomogeneous_zero]

theorem CoeffHom.add {p q : Polynomial (HoleRing k N)} {e : Fin N → ℕ}
    (hp : CoeffHom p e) (hq : CoeffHom q e) : CoeffHom (p + q) e := by
  intro j
  simpa only [Polynomial.coeff_add] using (hp j).add (hq j)

theorem CoeffHom.sum {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (HoleRing k N)) {e : Fin N → ℕ}
    (hf : ∀ i ∈ s, CoeffHom (f i) e) : CoeffHom (∑ i ∈ s, f i) e := by
  intro j
  rw [Polynomial.finset_sum_coeff]
  exact multiHom_sum s _ (fun i hi => hf i hi j)

theorem CoeffHom.mul {p q : Polynomial (HoleRing k N)} {e f : Fin N → ℕ}
    (hp : CoeffHom p e) (hq : CoeffHom q f) : CoeffHom (p * q) (e + f) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact multiHom_sum _ _ (fun i _ => (hp i.1).mul (hq i.2))

theorem CoeffHom.prod {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (HoleRing k N)) (e : ι → Fin N → ℕ)
    (hf : ∀ i ∈ s, CoeffHom (f i) (e i)) :
    CoeffHom (∏ i ∈ s, f i) (∑ i ∈ s, e i) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The common multidegree of every coefficient of every matrix entry. -/
def MatrixCoeffHom {m n : Type*} (A : Matrix m n (Polynomial (HoleRing k N)))
    (e : Fin N → ℕ) : Prop := ∀ i j, CoeffHom (A i j) e

theorem matrixCoeffHom_one {n : Type*} [DecidableEq n] :
    MatrixCoeffHom (1 : Matrix n n (Polynomial (HoleRing k N))) 0 := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, coeffHom_one, coeffHom_zero]

theorem MatrixCoeffHom.mul {m n o : Type*} [Fintype n]
    {A : Matrix m n (Polynomial (HoleRing k N))}
    {B : Matrix n o (Polynomial (HoleRing k N))} {e f : Fin N → ℕ}
    (hA : MatrixCoeffHom A e) (hB : MatrixCoeffHom B f) :
    MatrixCoeffHom (A * B) (e + f) := by
  intro i j
  rw [Matrix.mul_apply]
  exact CoeffHom.sum _ _ (fun x _ => (hA i x).mul (hB x j))

theorem MatrixCoeffHom.det {r : ℕ}
    {A : Matrix (Fin r) (Fin r) (Polynomial (HoleRing k N))} {e : Fin N → ℕ}
    (hA : MatrixCoeffHom A e) : CoeffHom A.det (fun b => r * e b) := by
  classical
  rw [Matrix.det_apply']
  apply CoeffHom.sum
  intro σ _
  have hp := CoeffHom.prod Finset.univ (fun i => A (σ i) i) (fun _ => e)
    (fun i _ => hA (σ i) i)
  convert (coeffHom_intCast (N := N) (k := k) (Equiv.Perm.sign σ : ℤ)).mul hp using 1
  ext b
  simp

theorem matrixCoeffHom_prod {n α : Type*} [Fintype n] [DecidableEq n]
    (w : List α) (L : α → Matrix n n (Polynomial (HoleRing k N)))
    (e : α → Fin N → ℕ) (hw : ∀ a ∈ w, MatrixCoeffHom (L a) (e a)) :
    MatrixCoeffHom (w.map L).prod (w.map e).sum := by
  revert hw
  induction w with
  | nil =>
    intro _
    simpa using (matrixCoeffHom_one (n := n) (N := N) (k := k))
  | cons a w ih =>
    intro hw
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (hw a (List.mem_cons_self ..)).mul
      (ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)))

end Homogeneity

section Lift

variable {k : Type*} [Field k] {N d : ℕ}

theorem lift_coeffHom (P : Pencil k d) (a : Fin 3 → HoleRing k N)
    (e : Fin N → ℕ) (ha : ∀ i, IsMultiHomogeneous (a i) e) :
    MatrixCoeffHom (P.lift a) e := by
  intro row col
  unfold Pencil.lift
  rw [MvPolynomial.algebraMap_eq]
  apply CoeffHom.add
  · apply coeffHom_C
    apply multiHom_sum
    intro i _
    simpa only [zero_add] using (multiHom_C (P.constant i row col)).mul (ha i)
  · have hlin : CoeffHom
        (Polynomial.C (∑ i : Fin 3, MvPolynomial.C (P.linear i row col) * a i)) e := by
      apply coeffHom_C
      apply multiHom_sum
      intro i _
      simpa only [zero_add] using (multiHom_C (P.linear i row col)).mul (ha i)
    simpa only [zero_add] using coeffHom_X.mul hlin

end Lift

end KoetheCounterexample.Mortality

end KoetheProofPart05

/- ## KoethePencilMortalityFormalWord -/

noncomputable section KoetheProofPart06

set_option autoImplicit false

/-
# Formal letters, specialization, and one scalar minor equation

A formal letter is either a fixed vector or an independently indexed hole.
The common-zero theorem is applied to the coefficients of a single pivot
minor.  Its equation count is the full word length plus one.
-/


open scoped BigOperators
open KoetheMultiProjective

namespace KoetheCounterexample.Mortality

abbrev FormalLetter (k : Type*) (N : ℕ) := Triple k ⊕ Fin N

section FormalLetters

variable {k : Type*} {N d r : ℕ}

def letterCoeffs [Field k] : FormalLetter k N → Fin 3 → HoleRing k N
  | .inl a => fun j => MvPolynomial.C (a j)
  | .inr b => fun j => MvPolynomial.X (b, j)

def letterDegree : FormalLetter k N → Fin N → ℕ
  | .inl _ => 0
  | .inr b => blockUnit b

def specializeLetter (x : (Fin N × Fin 3) → k) : FormalLetter k N → Triple k
  | .inl a => a
  | .inr b => fun j => x (b, j)

def formalProd [Field k] (P : Pencil k d) (w : List (FormalLetter k N)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial (HoleRing k N)) :=
  (w.map (fun a => P.lift (letterCoeffs a))).prod

@[simp] theorem specializeLetter_inl (x : (Fin N × Fin 3) → k) (a : Triple k) :
    specializeLetter x (.inl a) = a := rfl

@[simp] theorem letterDegree_inl (a : Triple k) :
    letterDegree (N := N) (.inl a) = 0 := rfl

@[simp] theorem letterDegree_inr (b : Fin N) :
    letterDegree (k := k) (.inr b) = blockUnit b := rfl

@[simp] theorem constantWord_degree (w : List (Triple k)) :
    ((w.map (Sum.inl : Triple k → FormalLetter k N)).map letterDegree).sum = 0 := by
  simp only [List.map_map, Function.comp_def, letterDegree_inl, List.sum_map_zero]

@[simp] theorem specialize_constantWord (x : (Fin N × Fin 3) → k)
    (w : List (Triple k)) :
    (w.map (Sum.inl : Triple k → FormalLetter k N)).map (specializeLetter x) = w := by
  simp [Function.comp_def]

variable [Field k]

theorem letterCoeffs_hom (a : FormalLetter k N) (j : Fin 3) :
    IsMultiHomogeneous (letterCoeffs a j) (letterDegree a) := by
  cases a with
  | inl a => exact multiHom_C (a j)
  | inr b => exact multiHom_X b j

theorem formalProd_hom (P : Pencil k d) (w : List (FormalLetter k N)) :
    MatrixCoeffHom (formalProd P w) (w.map letterDegree).sum :=
  matrixCoeffHom_prod w _ _
    (fun a _ => lift_coeffHom P (letterCoeffs a) (letterDegree a) (letterCoeffs_hom a))

theorem formalMinor_natDegree_le (P : Pencil k d) (w : List (FormalLetter k N))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I) :
    (((formalProd P w).submatrix I J).det).natDegree ≤ w.length := by
  simpa only [formalProd, List.map_map, Function.comp_def, List.length_map] using
    det_liftWord_natDegree_le P (w.map letterCoeffs) I J hI

theorem specialize_lift (P : Pencil k d) (a : FormalLetter k N)
    (x : (Fin N × Fin 3) → k) :
    (P.lift (letterCoeffs a)).map (Polynomial.mapRingHom (MvPolynomial.eval x)) =
      P.eval (specializeLetter x a) := by
  apply Matrix.ext
  intro i j
  change Polynomial.map (MvPolynomial.eval x) (P.lift (letterCoeffs a) i j) = _
  cases a <;>
    simp only [Pencil.lift, Pencil.eval, letterCoeffs, specializeLetter,
      MvPolynomial.algebraMap_eq, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_sum, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]

theorem specialize_formalProd (P : Pencil k d) (w : List (FormalLetter k N))
    (x : (Fin N × Fin 3) → k) :
    (formalProd P w).map (Polynomial.mapRingHom (MvPolynomial.eval x)) =
      P.wordProd (w.map (specializeLetter x)) := by
  classical
  induction w with
  | nil =>
    simp only [formalProd, List.map_nil, List.prod_nil, Pencil.wordProd_nil]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons a w ih =>
    simp only [formalProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [Matrix.map_mul, specialize_lift, ih]
    rfl

/-- A formal word in which every hole block occurs once has a specialization
with no zero block that kills any specified minor, provided the number of
coefficient equations is at most twice the number of blocks. -/
theorem exists_specialization_minor_zero [IsAlgClosed k]
    (P : Pencil k d) (w : List (FormalLetter k N))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I)
    (hN : 0 < N) (hr : 0 < r) (hsize : w.length + 1 ≤ 2 * N)
    (hdegree : (w.map letterDegree).sum = fun _ => 1) :
    ∃ x : (Fin N × Fin 3) → k,
      (∀ b : Fin N, (fun j : Fin 3 => x (b, j)) ≠ 0) ∧
      ((P.wordProd (w.map (specializeLetter x))).submatrix I J).det = 0 := by
  classical
  let F := ((formalProd P w).submatrix I J).det
  have hFdegree : F.natDegree ≤ w.length := formalMinor_natDegree_le P w I J hI
  have hFhom : CoeffHom F (fun _ => r) := by
    have h := formalProd_hom P w
    rw [hdegree] at h
    have hminor : MatrixCoeffHom ((formalProd P w).submatrix I J) (fun _ => 1) :=
      fun i j => h (I i) (J j)
    simpa only [Nat.mul_one] using hminor.det
  obtain ⟨x, hx, hzero⟩ := exists_common_zero_of_coeff
    (fun i : Fin (w.length + 1) => F.coeff i.val) hN hr hsize
    (fun i e he b => hFhom i.val e he b)
  refine ⟨x, hx, ?_⟩
  have hmap : Polynomial.map (MvPolynomial.eval x) F = 0 := by
    ext j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hj : j < w.length + 1
    · exact hzero ⟨j, hj⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  rw [← specialize_formalProd P w x, Matrix.submatrix_map, det_map]
  exact hmap

end FormalLetters

end KoetheCounterexample.Mortality

end KoetheProofPart06

/- ## KoethePencilMortalityMask -/

noncomputable section KoetheProofPart07

set_option autoImplicit false

/-
# Periodic masks and independent connector holes

Free positions are enumerated as a finite subtype of *occurrences*, not as
residue classes.  In particular a connector of length `m * period` has
`m * holes` distinct projective blocks.
-/


open scoped BigOperators

namespace KoetheCounterexample.Mortality

variable {k : Type*} [Field k]

theorem lookup_add_of_dvd (M : PeriodicMask k) (a b : ℕ) (ha : M.period ∣ a) :
    M.lookup (a + b) = M.lookup b := by
  unfold PeriodicMask.lookup
  congr 1
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd ha]

theorem compatible_append (M : PeriodicMask k) {u v : List (Triple k)}
    (hu : M.Compatible u) (hv : M.Compatible v) (hlen : M.period ∣ u.length) :
    M.Compatible (u ++ v) := by
  intro i z hz
  rw [List.get_eq_getElem]
  by_cases hi : i.val < u.length
  · rw [List.getElem_append_left hi]
    exact hu ⟨i.val, hi⟩ z hz
  · have hle : u.length ≤ i.val := Nat.le_of_not_gt hi
    have hiv : i.val - u.length < v.length := by
      have h := i.isLt
      simp only [List.length_append] at h
      omega
    rw [List.getElem_append_right hle]
    apply hv ⟨i.val - u.length, hiv⟩ z
    rw [← lookup_add_of_dvd M u.length (i.val - u.length) hlen,
      Nat.add_sub_of_le hle]
    exact hz

theorem compatible_ofFn (M : PeriodicMask k) {L : ℕ} (f : Fin L → Triple k)
    (hf : ∀ i z, M.lookup i.val = some z → f i = z) :
    M.Compatible (List.ofFn f) := by
  intro i z hz
  rw [List.get_ofFn]
  exact hf (Fin.cast (by simp) i) z hz

/-- Actual unassigned occurrences in a finite interval. -/
def FreePos (M : PeriodicMask k) (L : ℕ) :=
  {i : Fin L // M.lookup i.val = none}

instance freePosFintype (M : PeriodicMask k) (L : ℕ) : Fintype (FreePos M L) := by
  classical
  unfold FreePos
  infer_instance

def freeCount (M : PeriodicMask k) (L : ℕ) : ℕ := Fintype.card (FreePos M L)

def freeIndex (M : PeriodicMask k) (L : ℕ) : FreePos M L ≃ Fin (freeCount M L) :=
  Fintype.equivFin _

theorem lookup_finProd (M : PeriodicMask k) {m : ℕ}
    (a : Fin m) (b : Fin M.period) :
    M.lookup (finProdFinEquiv (a, b)).val = M.value b := by
  unfold PeriodicMask.lookup
  congr 1
  apply Fin.ext
  change (b.val + M.period * a.val) % M.period = b.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]

/-- Exact independent-hole count, including zero repetitions. -/
theorem freeCount_mul_period (M : PeriodicMask k) (m : ℕ) :
    freeCount M (m * M.period) = m * M.holes := by
  classical
  unfold freeCount FreePos
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin M.period ≃ Fin (m * M.period))]
  simp only [Fintype.sum_prod_type, lookup_finProd]
  simp only [← Finset.card_filter]
  change (∑ _ : Fin m, M.holes) = m * M.holes
  simp

/-- A fixed letter at assigned positions; a distinct variable block at each hole. -/
def connectorLetter (M : PeriodicMask k) (L : ℕ) (i : Fin L) :
    FormalLetter k (freeCount M L) :=
  match h : M.lookup i.val with
  | none => .inr (freeIndex M L ⟨i, h⟩)
  | some z => .inl z

def formalConnector (M : PeriodicMask k) (L : ℕ) :
    List (FormalLetter k (freeCount M L)) := List.ofFn (connectorLetter M L)

@[simp] theorem formalConnector_length (M : PeriodicMask k) (L : ℕ) :
    (formalConnector M L).length = L := by simp [formalConnector]

theorem connectorLetter_of_none (M : PeriodicMask k) (L : ℕ) (i : Fin L)
    (h : M.lookup i.val = none) :
    connectorLetter M L i = .inr (freeIndex M L ⟨i, h⟩) := by
  unfold connectorLetter
  split <;> simp_all

theorem connectorLetter_of_some (M : PeriodicMask k) (L : ℕ) (i : Fin L)
    (z : Triple k) (h : M.lookup i.val = some z) :
    connectorLetter M L i = .inl z := by
  unfold connectorLetter
  split <;> simp_all

/-- Each enumerated hole contributes exactly one copy of its block degree. -/
theorem formalConnector_degree (M : PeriodicMask k) (L : ℕ) :
    ((formalConnector M L).map letterDegree).sum = fun _ => 1 := by
  classical
  ext b
  simp only [formalConnector, List.map_ofFn, List.sum_ofFn, Finset.sum_apply,
    Function.comp_apply]
  let t : FreePos M L := (freeIndex M L).symm b
  rw [Finset.sum_eq_single t.val]
  · rw [connectorLetter_of_none M L t.val t.property, letterDegree_inr]
    simp [blockUnit, t]
  · intro i _ hi
    cases h : M.lookup i.val with
    | some z => simp [connectorLetter_of_some M L i z h]
    | none =>
      rw [connectorLetter_of_none M L i h, letterDegree_inr]
      have hne : b ≠ freeIndex M L ⟨i, h⟩ := by
        intro heq
        apply hi
        have ht : (⟨i, h⟩ : FreePos M L) = t := by
          apply (freeIndex M L).injective
          exact heq.symm.trans ((freeIndex M L).apply_symm_apply b).symm
        exact congrArg Subtype.val ht
      simp [blockUnit, hne]
  · simp

theorem specialized_connector_nonzero (M : PeriodicMask k) (L : ℕ)
    (x : (Fin (freeCount M L) × Fin 3) → k)
    (hx : ∀ b : Fin (freeCount M L), (fun j : Fin 3 => x (b, j)) ≠ 0) :
    ∀ z ∈ (formalConnector M L).map (specializeLetter x), z ≠ 0 := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  cases h : M.lookup i.val with
  | none =>
    rw [connectorLetter_of_none M L i h]
    exact hx _
  | some a =>
    rw [connectorLetter_of_some M L i a h]
    exact M.nonzero _ a h

theorem specialized_connector_compatible (M : PeriodicMask k) (L : ℕ)
    (x : (Fin (freeCount M L) × Fin 3) → k) :
    M.Compatible ((formalConnector M L).map (specializeLetter x)) := by
  simp only [formalConnector, List.map_ofFn]
  apply compatible_ofFn
  intro i z hz
  rw [Function.comp_apply, connectorLetter_of_some M L i z hz]
  rfl

/-- There is an initial compatible, nonzero word of exactly one mask period. -/
theorem exists_compatible_block (M : PeriodicMask k) :
    ∃ w : List (Triple k), w.length = M.period ∧
      (∀ z ∈ w, z ≠ 0) ∧ M.Compatible w := by
  let x : (Fin (freeCount M M.period) × Fin 3) → k := fun _ => 1
  have hx : ∀ b : Fin (freeCount M M.period), (fun j : Fin 3 => x (b, j)) ≠ 0 := by
    intro b h
    have h0 := congrFun h 0
    exact one_ne_zero h0
  refine ⟨(formalConnector M M.period).map (specializeLetter x), ?_,
    specialized_connector_nonzero M M.period x hx,
    specialized_connector_compatible M M.period x⟩
  simp

end KoetheCounterexample.Mortality

end KoetheProofPart07

/- ## KoethePencilMortality -/

noncomputable section KoetheProofPart08

set_option autoImplicit false

/-
# Mask mortality for one-row pencils over an algebraically closed field

The proof uses determinantal rank: vanishing `(r+1)`-minors is the rank
bound, and one nonzero `r`-minor is a pivot.  A long connector kills that
pivot in `P_W P_C P_W`, so all `r`-minors vanish.  Induction finishes in at
most the matrix size many strict rank reductions.

Every connector hole is independently enumerated, all chosen vectors lie
in the constant field, and all products are in the forward word convention
of `KoethePencilDefs`.  No nilness or countability hypothesis is used.
-/


open scoped BigOperators

namespace KoetheCounterexample

namespace Mortality

variable {k : Type*} [Field k] [IsAlgClosed k] {d r : ℕ}

/-- A sufficiently long, mask-compatible connector strictly reduces a
positive determinantal rank. -/
theorem exists_rank_reducing_connector (P : Pencil k d) (M : PeriodicMask k)
    (hM : M.period < 2 * M.holes) (w : List (Triple k))
    (hr : 0 < r) (I J : Fin r → Fin (d + 1))
    (hp : ((P.wordProd w).submatrix I J).det ≠ 0)
    (hnext : MinorsVanish (P.wordProd w) (r + 1)) :
    ∃ c : List (Triple k), M.period ≤ c.length ∧ M.period ∣ c.length ∧
      (∀ z ∈ c, z ≠ 0) ∧ M.Compatible c ∧
      MinorsVanish (P.wordProd ((w ++ c) ++ w)) r := by
  classical
  -- Since `2*H-Q ≥ 1`, this deliberately simple choice suffices.
  let m := 2 * w.length + 1
  let L := m * M.period
  let N := freeCount M L
  let W : List (FormalLetter k N) :=
    ((w.map Sum.inl) ++ formalConnector M L) ++ (w.map Sum.inl)
  have hm : 0 < m := by dsimp [m]; omega
  have hH : 0 < M.holes := by omega
  have hN : 0 < N := by
    dsimp only [N, L]
    rw [freeCount_mul_period]
    exact Nat.mul_pos hm hH
  have hsize : W.length + 1 ≤ 2 * N := by
    calc
      W.length + 1 = m * (M.period + 1) := by
        simp only [W, List.length_append, List.length_map, formalConnector,
          List.length_ofFn, L, m]
        ring
      _ ≤ m * (2 * M.holes) := Nat.mul_le_mul_left m (Nat.succ_le_of_lt hM)
      _ = 2 * N := by
        dsimp only [N, L]
        rw [freeCount_mul_period]
        ring
  have hdegree : (W.map letterDegree).sum = fun _ => 1 := by
    simp only [W, List.map_append, List.sum_append, constantWord_degree,
      zero_add, add_zero]
    exact formalConnector_degree M L
  have hI : Function.Injective I :=
    injective_of_det_submatrix_ne_zero (P.wordProd w) I J hp
  obtain ⟨x, hx, hz⟩ :=
    exists_specialization_minor_zero P W I J hI hN hr hsize hdegree
  let c := (formalConnector M L).map (specializeLetter x)
  have hclen : c.length = L := by
    simp only [c, List.length_map]
    exact formalConnector_length M L
  have hz' : ((P.wordProd ((w ++ c) ++ w)).submatrix I J).det = 0 := by
    simpa only [W, List.map_append, specialize_constantWord] using hz
  refine ⟨c, ?_, ?_, specialized_connector_nonzero M L x hx,
    specialized_connector_compatible M L x, ?_⟩
  · rw [hclen]
    change M.period ≤ m * M.period
    simpa using Nat.mul_le_mul_right M.period (Nat.succ_le_of_lt hm)
  · rw [hclen]
    exact dvd_mul_left M.period m
  · have h := sandwich_minors_vanish (P.wordProd w) (P.wordProd c) I J hp hnext
      (by simpa only [Pencil.wordProd_append] using hz')
    simpa only [Pencil.wordProd_append] using h

/-- Induction on a determinantal rank bound, retaining a positive, aligned,
mask-compatible nonzero word throughout. -/
theorem mortality_of_vanishing_minors (P : Pencil k d) (M : PeriodicMask k)
    (hM : M.period < 2 * M.holes) (r : ℕ) :
    ∀ w : List (Triple k), M.period ≤ w.length → M.period ∣ w.length →
      (∀ z ∈ w, z ≠ 0) → M.Compatible w →
      MinorsVanish (P.wordProd w) (r + 1) →
      ∃ u : List (Triple k), M.period ≤ u.length ∧ M.period ∣ u.length ∧
        (∀ z ∈ u, z ≠ 0) ∧ M.Compatible u ∧ P.wordProd u = 0 := by
  induction r with
  | zero =>
    intro w hlen hdiv hnz hcomp hminor
    exact ⟨w, hlen, hdiv, hnz, hcomp, eq_zero_of_minorsVanish_one _ hminor⟩
  | succ r ih =>
    intro w hlen hdiv hnz hcomp hminor
    by_cases hsmall : MinorsVanish (P.wordProd w) (r + 1)
    · exact ih w hlen hdiv hnz hcomp hsmall
    · obtain ⟨I, J, hp⟩ : ∃ I J : Fin (r + 1) → Fin (d + 1),
          ((P.wordProd w).submatrix I J).det ≠ 0 := by
        simpa only [MinorsVanish, not_forall] using hsmall
      obtain ⟨c, _, hcdiv, hcnz, hccomp, hdrop⟩ :=
        exists_rank_reducing_connector P M hM w (Nat.succ_pos r) I J hp hminor
      apply ih ((w ++ c) ++ w) ?_ ?_ ?_ ?_ hdrop
      · simp only [List.length_append]
        omega
      · simpa only [List.length_append] using dvd_add (dvd_add hdiv hcdiv) hdiv
      · intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · rcases List.mem_append.mp hz with hz | hz
          · exact hnz z hz
          · exact hcnz z hz
        · exact hnz z hz
      · apply compatible_append M (compatible_append M hcomp hccomp hdiv) hcomp
        simpa only [List.length_append] using dvd_add hdiv hcdiv

end Mortality

/-- **Mask mortality.** A periodic mask with more than half of its residues
free admits a compatible nonzero mortal word for every one-row pencil over
an algebraically closed field. -/
theorem maskMortality (k : Type*) [Field k] [IsAlgClosed k] : MaskMortality k := by
  intro d P M hM
  obtain ⟨w, hlen, hnz, hcomp⟩ := Mortality.exists_compatible_block M
  apply Mortality.mortality_of_vanishing_minors P M hM (d + 1) w
    (by omega) (by rw [hlen]) hnz hcomp
  apply Mortality.minorsVanish_above
  simp

end KoetheCounterexample

end KoetheProofPart08

/- ## KoetheMaskSequenceBasic -/

noncomputable section KoetheProofPart09

/-
# Sparse periodic masks

The bookkeeping in this file is purely combinatorial.  In particular it does
not use a matrix-mortality theorem: that theorem will be a hypothesis of the
sequence construction.

We use the integral invariant `4 * assigned < period`.  If a compatible word
has length `l`, repeating the old mask `4*l+1` times before installing the word
preserves this invariant.  Thus no limiting density or geometric-series
calculation is needed.
-/

set_option autoImplicit false


namespace KoetheCounterexample
namespace MaskSequence

variable {k : Type*} [Field k]

/-- All assignments, at all sites, of `M` persist in `N`. -/
def Extends (N M : PeriodicMask k) : Prop :=
  ∀ n z, M.lookup n = some z → N.lookup n = some z

@[refl] theorem Extends.refl (M : PeriodicMask k) : Extends M M :=
  fun _ _ h => h

theorem Extends.trans {L M N : PeriodicMask k}
    (hNM : Extends N M) (hML : Extends M L) : Extends N L :=
  fun n z h => hNM n z (hML n z h)

theorem lookup_nonzero (M : PeriodicMask k) {n : ℕ} {z : Triple k}
    (h : M.lookup n = some z) : z ≠ 0 :=
  M.nonzero _ z h

@[simp] theorem lookup_fin (M : PeriodicMask k) (i : Fin M.period) :
    M.lookup i.val = M.value i := by
  simp [PeriodicMask.lookup, Nat.mod_eq_of_lt i.is_lt]

theorem lookup_mod_of_dvd (M : PeriodicMask k) {p : ℕ}
    (hp : M.period ∣ p) (n : ℕ) : M.lookup (n % p) = M.lookup n := by
  simp only [PeriodicMask.lookup, Nat.mod_mod_of_dvd n hp]

theorem lookup_add_of_mod_eq_zero (M : PeriodicMask k) {b : ℕ}
    (hb : b % M.period = 0) (i : ℕ) : M.lookup (b + i) = M.lookup i := by
  simp [PeriodicMask.lookup, Nat.add_mod, hb]

theorem holes_add_assigned (M : PeriodicMask k) :
    M.holes + M.assigned = M.period := by
  classical
  simpa [PeriodicMask.holes, PeriodicMask.assigned] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin M.period => M.value i = none))

theorem enough_holes (M : PeriodicMask k)
    (h : 4 * M.assigned < M.period) : M.period < 2 * M.holes := by
  have := holes_add_assigned M
  omega

/-- The unassigned mask of period one. -/
def emptyMask : PeriodicMask k where
  period := 1
  period_pos := by decide
  value := fun _ => none
  nonzero := by simp

@[simp] theorem emptyMask_assigned : (emptyMask (k := k)).assigned = 0 := by
  classical
  simp [PeriodicMask.assigned, emptyMask]

/-- Exact cardinal count for lifting *all* old assignments to `c` periods. -/
theorem lifted_assigned_card (M : PeriodicMask k) (c : ℕ) :
    (Finset.univ.filter fun i : Fin (c * M.period) => M.lookup i.val ≠ none).card =
      c * M.assigned := by
  classical
  let e : {i : Fin (c * M.period) // M.lookup i.val ≠ none} ≃
      Fin c × {i : Fin M.period // M.value i ≠ none} :=
    { toFun := fun i =>
        ((finProdFinEquiv.symm i.val).1,
          ⟨(finProdFinEquiv.symm i.val).2, i.property⟩)
      invFun := fun i =>
        ⟨finProdFinEquiv (i.1, i.2.val), by
          simpa [PeriodicMask.lookup, finProdFinEquiv, Nat.mod_eq_of_lt i.2.val.is_lt]
            using i.2.property⟩
      left_inv := by
        intro i
        apply Subtype.ext
        exact finProdFinEquiv.apply_symm_apply i.val
      right_inv := by
        intro i
        apply Prod.ext
        · change (finProdFinEquiv.symm (finProdFinEquiv (i.1, i.2.val))).1 = i.1
          exact congrArg (fun p : Fin c × Fin M.period => p.1)
            (finProdFinEquiv.symm_apply_apply (i.1, i.2.val))
        · apply Subtype.ext
          change (finProdFinEquiv.symm (finProdFinEquiv (i.1, i.2.val))).2 = i.2.val
          exact congrArg (fun p : Fin c × Fin M.period => p.2)
            (finProdFinEquiv.symm_apply_apply (i.1, i.2.val)) }
  simpa [Fintype.card_subtype, PeriodicMask.assigned] using Fintype.card_congr e

/-- Refine a mask by installing a nonzero compatible word in its first block.
Outside that block every previous assignment is retained. -/
def install (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) : PeriodicMask k where
  period := (4 * w.length + 1) * M.period
  period_pos := Nat.mul_pos (by omega) M.period_pos
  value := fun i => if h : i.val < w.length then some (w.get ⟨i.val, h⟩)
    else M.lookup i.val
  nonzero := by
    intro i z hz
    split_ifs at hz with hi
    · have heq : w.get ⟨i.val, hi⟩ = z := Option.some.inj hz
      subst z
      exact hw _ (List.get_mem w _)
    · exact lookup_nonzero M hz

@[simp] theorem install_period (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) :
    (install M w hw).period = (4 * w.length + 1) * M.period := rfl

theorem period_dvd_install (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) : M.period ∣ (install M w hw).period :=
  dvd_mul_left _ _

theorem length_le_install_period (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) : w.length ≤ (install M w hw).period := by
  have hQ : 1 ≤ M.period := M.period_pos
  change w.length ≤ (4 * w.length + 1) * M.period
  nlinarith

theorem install_extends (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) (hc : M.Compatible w) : Extends (install M w hw) M := by
  intro n z hz
  let N := install M w hw
  have hlookup : M.lookup (n % N.period) = some z := by
    rw [lookup_mod_of_dvd M (period_dvd_install M w hw), hz]
  change (if h : n % N.period < w.length then
      some (w.get ⟨n % N.period, h⟩) else M.lookup (n % N.period)) = some z
  split_ifs with hn
  · rw [hc ⟨n % N.period, hn⟩ z hlookup]
  · exact hlookup

theorem install_word (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) (i : Fin w.length) :
    (install M w hw).lookup i.val = some (w.get i) := by
  have hi : i.val < (install M w hw).period :=
    lt_of_lt_of_le i.is_lt (length_le_install_period M w hw)
  change (install M w hw).lookup (⟨i.val, hi⟩ : Fin (install M w hw).period).val = _
  rw [lookup_fin]
  exact dif_pos i.is_lt

/-- Installing the word adds at most its length to the lifted assigned set. -/
theorem install_assigned_le (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) :
    (install M w hw).assigned ≤
      (4 * w.length + 1) * M.assigned + w.length := by
  classical
  let N := install M w hw
  let old : Finset (Fin N.period) := Finset.univ.filter fun i => M.lookup i.val ≠ none
  let block : Finset (Fin N.period) := Finset.univ.filter fun i => i.val < w.length
  have hsub : (Finset.univ.filter fun i => N.value i ≠ none) ⊆ old ∪ block := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_union, old, block, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : i.val < w.length
    · exact Or.inr h
    · exact Or.inl (by simpa [N, install, h] using hi)
  have hold : old.card = (4 * w.length + 1) * M.assigned :=
    lifted_assigned_card M _
  have hblock : block.card = w.length := by
    rw [show block.card = Fintype.card {i : Fin N.period // i.val < w.length} by
      simp [block, Fintype.card_subtype]]
    exact Fintype.card_fin_lt_of_le (length_le_install_period M w hw)
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le old block).trans_eq (by rw [hold, hblock]))

/-- An adaptive integral density budget: the positive old slack is amplified
by `4 * length + 1`, whereas the cost of the new block is at most `4 * length`.
The new slack is therefore still at least one. -/
theorem install_sparse (M : PeriodicMask k) (w : List (Triple k))
    (hw : ∀ z ∈ w, z ≠ 0) (hM : 4 * M.assigned < M.period) :
    4 * (install M w hw).assigned < (install M w hw).period := by
  have hcard := install_assigned_le M w hw
  have hslack : 4 * M.assigned + 1 ≤ M.period := hM
  have hmul := Nat.mul_le_mul_left (4 * w.length + 1) hslack
  rw [install_period]
  nlinarith

end MaskSequence
end KoetheCounterexample

end KoetheProofPart09

/- ## KoetheMaskSequenceChain -/

noncomputable section KoetheProofPart10

/-
# A coherent chain of mortal periodic masks

An arbitrary sequence of pencils can be handled under the abstract
`MaskMortality` hypothesis.  The masks are refined at every stage and the
integral sparsity bound is retained.  A pointwise choice then produces a
nonzero sequence respecting every assignment at every stage.
-/

set_option autoImplicit false


namespace KoetheCounterexample
namespace MaskSequence

variable {k : Type*} [Field k]

/-- The word is installed at the beginning of a period, and fits in that period. -/
def Carries (M : PeriodicMask k) (w : List (Triple k)) : Prop :=
  w.length ≤ M.period ∧ ∀ i : Fin w.length, M.lookup i.val = some (w.get i)

/-- A mask contains a periodically recurring mortal word for this pencil. -/
def Kills {d : ℕ} (M : PeriodicMask k) (P : Pencil k d) : Prop :=
  ∃ w : List (Triple k), Carries M w ∧ P.wordProd w = 0

/-- Finite masks whose assigned density is strictly less than one quarter. -/
abbrev SparseMask (k : Type*) [Field k] :=
  {M : PeriodicMask k // 4 * M.assigned < M.period}

/-- Apply mortality only to a mask with more than half its positions free,
then preserve every old assignment while installing the resulting word. -/
theorem exists_mortal_extension (hm : MaskMortality k) (M : SparseMask k)
    {d : ℕ} (P : Pencil k d) :
    ∃ N : SparseMask k, Extends N.val M.val ∧ M.val.period ∣ N.val.period ∧
      Kills N.val P := by
  obtain ⟨w, _, _, hw, hc, hz⟩ := hm d P M.val (enough_holes M.val M.property)
  refine ⟨⟨install M.val w hw, install_sparse M.val w hw M.property⟩,
    install_extends M.val w hw hc, period_dvd_install M.val w hw, w, ?_, hz⟩
  exact ⟨length_le_install_period M.val w hw, install_word M.val w hw⟩

/-- Stage zero has no assignments.  Stage `j+1` additionally kills pencil `e j`. -/
def masks (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d) : ℕ → SparseMask k
  | 0 => ⟨emptyMask, by simpa only [emptyMask_assigned, mul_zero] using
      (emptyMask (k := k)).period_pos⟩
  | j + 1 => (exists_mortal_extension hm (masks hm e j) (e j).2).choose

theorem masks_succ (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d) (j : ℕ) :
    Extends (masks hm e (j + 1)).val (masks hm e j).val ∧
      (masks hm e j).val.period ∣ (masks hm e (j + 1)).val.period ∧
      Kills (masks hm e (j + 1)).val (e j).2 :=
  (exists_mortal_extension hm (masks hm e j) (e j).2).choose_spec

theorem masks_extends (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d)
    {i j : ℕ} (hij : i ≤ j) : Extends (masks hm e j).val (masks hm e i).val := by
  induction j, hij using Nat.le_induction with
  | base => exact Extends.refl _
  | succ j _ ih => exact (masks_succ hm e j).1.trans ih

theorem masks_period_dvd (hm : MaskMortality k) (e : ℕ → Σ d : ℕ, Pencil k d)
    {i j : ℕ} (hij : i ≤ j) :
    (masks hm e i).val.period ∣ (masks hm e j).val.period := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_refl _
  | succ j _ ih => exact dvd_trans ih (masks_succ hm e j).2.1

/-- Any increasing chain of nonzero partial masks has a simultaneous nonzero
completion.  A site assigned at any stage retains that exact vector forever.
Sites that are never assigned can harmlessly be filled with a fixed nonzero
vector; consequently no assertion about the density of the infinite union
is required. -/
theorem exists_compatible_sequence (M : ℕ → PeriodicMask k)
    (hM : ∀ i j, i ≤ j → Extends (M j) (M i)) :
    ∃ v : ℕ → Triple k, (∀ n, v n ≠ 0) ∧ ∀ j, (M j).SeqCompatible v := by
  classical
  have hpoint : ∀ n, ∃ z : Triple k, z ≠ 0 ∧
      ∀ j t, (M j).lookup n = some t → z = t := by
    intro n
    by_cases hn : ∃ j z, (M j).lookup n = some z
    · obtain ⟨j, z, hz⟩ := hn
      refine ⟨z, lookup_nonzero (M j) hz, ?_⟩
      intro i t ht
      rcases le_total j i with hji | hij
      · exact Option.some.inj ((hM j i hji n z hz).symm.trans ht)
      · exact Option.some.inj (hz.symm.trans (hM i j hij n t ht))
    · refine ⟨fun _ => 1, ?_, ?_⟩
      · intro hz
        exact one_ne_zero (congrFun hz 0)
      · intro j t ht
        exact (hn ⟨j, t, ht⟩).elim
  choose v hvzero hv using hpoint
  exact ⟨v, hvzero, fun j n z hz => hv n j z hz⟩

/-- A nonzero sequence respecting all the periodic mortal words in the chain. -/
theorem exists_sequence_for_enumeration (hm : MaskMortality k)
    (e : ℕ → Σ d : ℕ, Pencil k d) :
    ∃ v : ℕ → Triple k, (∀ n, v n ≠ 0) ∧
      ∀ j, (masks hm e j).val.SeqCompatible v :=
  exists_compatible_sequence (fun j => (masks hm e j).val)
    (fun _ _ h => masks_extends hm e h)

end MaskSequence
end KoetheCounterexample

end KoetheProofPart10

/- ## KoetheMaskSequence -/

noncomputable section KoetheProofPart11

/-
# Universal mortal sequences from abstract mask mortality

This file supplies the combinatorial implication from `MaskMortality k` to a
single nonzero sequence with uniformly vanishing windows for every pencil.
The only matrix facts used are the forward concatenation law for `wordProd`
and absorption by zero.  There are no algebraic-geometric hypotheses beyond
the abstract mortality assumption, and no assertion about the density of an
infinite union of masks.
-/

set_option autoImplicit false


namespace KoetheCounterexample
namespace MaskSequence

variable {k : Type*} [Field k] {d : ℕ}

/-- Split a forward window at a specified length. -/
theorem window_add (P : Pencil k d) (v : ℕ → Triple k) (start a b : ℕ) :
    P.window v start (a + b) = P.window v start a * P.window v (start + a) b := by
  simp [Pencil.window, List.ofFn_add, Nat.add_assoc]

/-- A window containing a zero contiguous subwindow is itself zero.
No commutation or rearrangement of the matrix factors is used. -/
theorem window_eq_zero_of_subwindow (P : Pencil k d) (v : ℕ → Triple k)
    (start N offset len : ℕ) (hfit : offset + len ≤ N)
    (hz : P.window v (start + offset) len = 0) : P.window v start N = 0 := by
  have hN : N = (offset + len) + (N - (offset + len)) := by omega
  rw [hN, window_add, window_add, hz, mul_zero, zero_mul]

/-- An installed word occurs at every nonnegative multiple of the mask period
in every compatible sequence. -/
theorem carries_window (P : Pencil k d) (M : PeriodicMask k)
    {w : List (Triple k)} (hw : Carries M w) {v : ℕ → Triple k}
    (hv : M.SeqCompatible v) {b : ℕ} (hb : b % M.period = 0) :
    P.window v b w.length = P.wordProd w := by
  have hword : (List.ofFn fun i : Fin w.length => v (b + i.val)) = w := by
    calc
      _ = List.ofFn w.get := by
        apply congrArg List.ofFn
        funext i
        apply hv (b + i.val) (w.get i)
        rw [lookup_add_of_mod_eq_zero M hb]
        exact hw.2 i
      _ = w := List.ofFn_get w
  rw [Pencil.window, hword]

/-- Twice the mask period is one bound that works at *every* starting site. -/
theorem kills_windows (P : Pencil k d) (M : PeriodicMask k)
    {v : ℕ → Triple k} (hv : M.SeqCompatible v) (hkill : Kills M P) :
    ∀ start, P.window v start (2 * M.period) = 0 := by
  obtain ⟨w, hw, hz⟩ := hkill
  intro start
  let offset := M.period - start % M.period
  have hoffset : offset ≤ M.period := Nat.sub_le _ _
  have hfit : offset + w.length ≤ 2 * M.period := by
    have := hw.1
    omega
  have hrem : start % M.period ≤ M.period := (Nat.mod_lt start M.period_pos).le
  have hb : (start + offset) % M.period = 0 := by
    calc
      _ = (start % M.period + offset) % M.period :=
        (Nat.mod_add_mod start M.period offset).symm
      _ = 0 := by rw [show start % M.period + offset = M.period from
        Nat.add_sub_of_le hrem, Nat.mod_self]
  exact window_eq_zero_of_subwindow P v start (2 * M.period) offset w.length hfit
    ((carries_window P M hw hv hb).trans hz)

end MaskSequence

/-- The complete combinatorial construction, independent of any proof of
matrix mortality.  Countability is used only to enumerate all pencils. -/
theorem exists_universalMortalSequence (k : Type*) [Field k] [Countable k]
    (hm : MaskMortality k) : ∃ v : ℕ → Triple k, UniversalMortalSequence k v := by
  classical
  letI : Nonempty (Σ d : ℕ, Pencil k d) :=
    ⟨⟨0, { constant := 0, linear := 0, linear_off_root := by simp }⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (Σ d : ℕ, Pencil k d)
  obtain ⟨v, hv, hcompat⟩ := MaskSequence.exists_sequence_for_enumeration hm e
  refine ⟨v, hv, ?_⟩
  intro d P
  obtain ⟨j, hj⟩ := he ⟨d, P⟩
  have hkill : MaskSequence.Kills (MaskSequence.masks hm e (j + 1)).val P :=
    (congrArg (fun a : Σ d : ℕ, Pencil k d =>
      MaskSequence.Kills (MaskSequence.masks hm e (j + 1)).val a.2) hj).mp
        (MaskSequence.masks_succ hm e j).2.2
  refine ⟨2 * (MaskSequence.masks hm e (j + 1)).val.period, ?_, ?_⟩
  · exact Nat.mul_pos (by decide) (MaskSequence.masks hm e (j + 1)).val.period_pos
  · exact MaskSequence.kills_windows P _ (hcompat (j + 1)) hkill

end KoetheCounterexample

end KoetheProofPart11

/- ## KoetheLinearizationBasic -/

noncomputable section KoetheProofPart12

/-
# Finite homogeneous-linear systems

A system has a distinguished input, finitely many internal states, and an output
row. Its coefficients are linear combinations of the three generators, with no
scalar/identity edges. `Represents` is the elimination property of the internal
system. We construct this property directly, without needing a matrix inverse
or a nilpotence assumption on the ambient algebra.
-/

set_option autoImplicit false


open scoped BigOperators

namespace KoetheCounterexample
namespace Linearization

universe u v

variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

/-- Evaluate one homogeneous-linear edge, as a constant polynomial. -/
def edge (a : Fin 3 → R) (c : Triple k) : Polynomial R :=
  Polynomial.C (∑ i : Fin 3, algebraMap k R (c i) * a i)

@[simp] theorem edge_zero (a : Fin 3 → R) : edge a (0 : Triple k) = 0 := by
  simp [edge]

@[simp] theorem edge_add (a : Fin 3 → R) (c d : Triple k) :
    edge a (c + d) = edge a c + edge a d := by
  simp [edge, add_mul, Finset.sum_add_distrib]

@[simp] theorem edge_smul (a : Fin 3 → R) (r : k) (c : Triple k) :
    edge a (r • c) = Polynomial.C (algebraMap k R r) * edge a c := by
  simp [edge, map_mul, mul_assoc, Finset.mul_sum]

/-- Coefficients selecting just one letter. -/
def letter (i : Fin 3) : Triple k := fun j => if j = i then 1 else 0

@[simp] theorem edge_letter (a : Fin 3 → R) (i : Fin 3) :
    edge a (letter (k := k) i) = Polynomial.C (a i) := by
  simp [edge, letter]

/-- A finite homogeneous-linear system. The root is not among `State`. -/
structure System (k : Type u) [Field k] where
  State : Type
  fintype : Fintype State
  decEq : DecidableEq State
  head : Triple k
  out : State → Triple k
  input : State → Triple k
  step : State → State → Triple k

attribute [instance] System.fintype System.decEq

/-- Every solution of the internal equations gives the specified output.
All equations take place in the polynomial ring over the possibly
noncommutative algebra `R`. -/
def Represents (S : System k) (a : Fin 3 → R) (x : R) : Prop :=
  ∀ (q₀ : Polynomial R) (q : S.State → Polynomial R),
    (∀ i, q i = edge a (S.input i) * q₀ +
      ∑ j, edge a (S.step i j) * q j) →
    edge a S.head * q₀ + ∑ j, edge a (S.out j) * q j =
      Polynomial.C x * q₀

/-- The elements admitting one of these finite linearizations. -/
def Linearizable (a : Fin 3 → R) (x : R) : Prop :=
  ∃ S : System k, Represents S a x

namespace System

/-- A single homogeneous-linear output, with no internal states. -/
def atom (c : Triple k) : System k where
  State := Empty
  fintype := inferInstance
  decEq := inferInstance
  head := c
  out := Empty.elim
  input := Empty.elim
  step := Empty.elim

/-- Disjoint union of systems, adding their output rows. -/
def add (S T : System k) : System k where
  State := S.State ⊕ T.State
  fintype := inferInstance
  decEq := inferInstance
  head := S.head + T.head
  out := Sum.elim S.out T.out
  input := Sum.elim S.input T.input
  step := fun i j => match i, j with
    | .inl i, .inl j => S.step i j
    | .inr i, .inr j => T.step i j
    | _, _ => 0

/-- Only the output row is scaled. -/
def smul (r : k) (S : System k) : System k where
  State := S.State
  fintype := S.fintype
  decEq := S.decEq
  head := r • S.head
  out := fun i => r • S.out i
  input := S.input
  step := S.step

/-- Prepend a generator: a new internal state computes the old output, and
one generator edge joins the new output to that state. -/
def prepend (i : Fin 3) (S : System k) : System k where
  State := Option S.State
  fintype := inferInstance
  decEq := inferInstance
  head := 0
  out := fun j => match j with
    | none => letter i
    | some _ => 0
  input := fun j => match j with
    | none => S.head
    | some j => S.input j
  step := fun j l => match j, l with
    | none, some l => S.out l
    | some j, some l => S.step j l
    | _, none => 0

end System

@[simp] theorem represents_atom (a : Fin 3 → R) (c : Triple k) :
    Represents (System.atom c) a (∑ i, algebraMap k R (c i) * a i) := by
  intro q₀ q hq
  simp [System.atom, edge]

theorem linearizable_zero (a : Fin 3 → R) : Linearizable (k := k) a 0 := by
  refine ⟨System.atom 0, ?_⟩
  simpa using represents_atom a (0 : Triple k)

theorem linearizable_letter (a : Fin 3 → R) (i : Fin 3) :
    Linearizable (k := k) a (a i) := by
  refine ⟨System.atom (letter i), ?_⟩
  simpa [letter] using represents_atom a (letter (k := k) i)

theorem Represents.add {S T : System k} {a : Fin 3 → R} {x y : R}
    (hS : Represents S a x) (hT : Represents T a y) :
    Represents (S.add T) a (x + y) := by
  intro q₀ q hq
  have hS' := hS q₀ (fun i => q (.inl i)) (fun i => by
    simpa [System.add, Fintype.sum_sum_type] using hq (.inl i))
  have hT' := hT q₀ (fun i => q (.inr i)) (fun i => by
    simpa [System.add, Fintype.sum_sum_type] using hq (.inr i))
  simp only [System.add, edge_add, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  calc
    (edge a S.head + edge a T.head) * q₀ +
        ((∑ j, edge a (S.out j) * q (.inl j)) +
          ∑ j, edge a (T.out j) * q (.inr j)) =
        (edge a S.head * q₀ + ∑ j, edge a (S.out j) * q (.inl j)) +
          (edge a T.head * q₀ + ∑ j, edge a (T.out j) * q (.inr j)) := by
      noncomm_ring
    _ = Polynomial.C x * q₀ + Polynomial.C y * q₀ := by rw [hS', hT']
    _ = Polynomial.C (x + y) * q₀ := by rw [map_add, add_mul]

theorem Represents.smul {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (r : k) :
    Represents (S.smul r) a (r • x) := by
  intro q₀ q hq
  have hS' := hS q₀ q hq
  change edge a (r • S.head) * q₀ +
      ∑ j, edge a (r • S.out j) * q j = _
  simp only [edge_smul, mul_assoc, ← Finset.mul_sum, ← mul_add]
  rw [hS', ← mul_assoc, ← map_mul, Algebra.smul_def]

theorem Represents.prepend {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (i : Fin 3) :
    Represents (S.prepend i) a (a i * x) := by
  intro q₀ q hq
  have hS' := hS q₀ (fun j => q (some j)) (fun j => by
    simpa [System.prepend, Fintype.sum_option] using hq (some j))
  have hn : q none = Polynomial.C x * q₀ := by
    have h := hq none
    simp only [System.prepend, Fintype.sum_option, edge_zero, zero_mul, zero_add] at h
    exact h.trans hS'
  simp [System.prepend, Fintype.sum_option, hn, mul_assoc, map_mul]

theorem linearizable_add {a : Fin 3 → R} {x y : R}
    (hx : Linearizable (k := k) a x) (hy : Linearizable (k := k) a y) :
    Linearizable (k := k) a (x + y) := by
  obtain ⟨S, hS⟩ := hx
  obtain ⟨T, hT⟩ := hy
  exact ⟨S.add T, hS.add hT⟩

theorem linearizable_smul {a : Fin 3 → R} {x : R}
    (hx : Linearizable (k := k) a x) (r : k) : Linearizable (k := k) a (r • x) := by
  obtain ⟨S, hS⟩ := hx
  exact ⟨S.smul r, hS.smul r⟩

theorem linearizable_prepend {a : Fin 3 → R} {x : R}
    (hx : Linearizable (k := k) a x) (i : Fin 3) :
    Linearizable (k := k) a (a i * x) := by
  obtain ⟨S, hS⟩ := hx
  exact ⟨S.prepend i, hS.prepend i⟩

end Linearization
end KoetheCounterexample

end KoetheProofPart12

/- ## KoetheLinearizationPencil -/

noncomputable section KoetheProofPart13

/-
# Root-row pencils and the polynomial root-column argument

A finite homogeneous-linear system becomes a shared `Pencil` by multiplying its
output row by the central polynomial variable. If that matrix is nilpotent,
`1 - T` has a polynomial right inverse. Eliminating the internal entries of its
root column gives `q = 1 + X * C(x) * q`. The coefficients of this polynomial
are `x^n`, and their eventual vanishing proves nilpotence of `x`.
-/

set_option autoImplicit false


open scoped BigOperators

namespace KoetheCounterexample
namespace Linearization

universe u v

/-- A polynomial right resolvent forces nilpotence, also in a noncommutative
ring and without assuming that the ring is nontrivial. -/
theorem nilpotent_of_polynomial_resolvent {R : Type v} [Ring R]
    (x : R) (q : Polynomial R)
    (hq : q = 1 + Polynomial.X * (Polynomial.C x * q)) : IsNilpotent x := by
  have hc : ∀ n : ℕ, q.coeff n = x ^ n := by
    intro n
    induction n with
    | zero =>
        have h := congrArg (fun p : Polynomial R => p.coeff 0) hq
        simpa using h
    | succ n ih =>
        have h := congrArg (fun p : Polynomial R => p.coeff (n + 1)) hq
        simpa [Polynomial.coeff_add, Polynomial.coeff_X_mul,
          Polynomial.coeff_C_mul, Polynomial.coeff_one, ih, pow_succ'] using h
  refine ⟨q.natDegree + 1, ?_⟩
  rw [← hc]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)

/-- Reindexing square matrices preserves products, zero, and one. -/
def submatrixHom {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Semiring A] (e : ι ≃ κ) :
    Matrix κ κ A →*₀ Matrix ι ι A where
  toFun M := M.submatrix e e
  map_zero' := rfl
  map_one' := Matrix.submatrix_one_equiv e
  map_mul' M N := (Matrix.submatrix_mul_equiv M N e e e).symm

variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

namespace System

/-- The root is `none`; only its row contains `X`. -/
def matrix (S : System k) (a : Fin 3 → R) :
    Matrix (Option S.State) (Option S.State) (Polynomial R) :=
  fun i j => match i, j with
    | none, none => Polynomial.X * edge a S.head
    | none, some j => Polynomial.X * edge a (S.out j)
    | some i, none => edge a (S.input i)
    | some i, some j => edge a (S.step i j)

/-- Enumeration of the states with the shared root index `0`. -/
def indexEquiv (S : System k) : Fin (Fintype.card S.State + 1) ≃ Option S.State :=
  (finSuccEquiv _).trans (Equiv.optionCongr (Fintype.equivFin S.State).symm)

@[simp] theorem indexEquiv_zero (S : System k) : S.indexEquiv 0 = none := by
  simp [indexEquiv]

/-- Exactly the shared pencil API, with no scalar/identity edges. -/
def pencil (S : System k) : Pencil k (Fintype.card S.State) where
  constant := fun i row col => match S.indexEquiv row, S.indexEquiv col with
    | none, _ => 0
    | some row, none => S.input row i
    | some row, some col => S.step row col i
  linear := fun i row col => match S.indexEquiv row, S.indexEquiv col with
    | none, none => S.head i
    | none, some col => S.out col i
    | some _, _ => 0
  linear_off_root := by
    intro i row col hrow
    have hr : S.indexEquiv row ≠ none := by
      intro h
      apply hrow
      apply S.indexEquiv.injective
      simpa using h
    cases he : S.indexEquiv row with
    | none => exact (hr he).elim
    | some r => rfl

/-- Evaluation agrees with the system matrix, including the exact order of
scalar coefficients, generator factors, and the central variable. -/
theorem lift_pencil (S : System k) (a : Fin 3 → R) :
    S.pencil.lift a = (S.matrix a).submatrix S.indexEquiv S.indexEquiv := by
  ext row col
  cases hr : S.indexEquiv row <;> cases hc : S.indexEquiv col <;>
    simp [Pencil.lift, pencil, Matrix.submatrix_apply, matrix, hr, hc, edge]

/-- Nilpotence transfers from the shared, finitely indexed pencil to the
same matrix indexed by the root and internal states. -/
theorem matrix_nil_of_pencil_nil (S : System k) (a : Fin 3 → R)
    (h : IsNilpotent (S.pencil.lift a)) : IsNilpotent (S.matrix a) := by
  rw [S.lift_pencil a] at h
  have hm := h.map (submatrixHom (A := Polynomial R) S.indexEquiv.symm)
  change IsNilpotent (((S.matrix a).submatrix S.indexEquiv S.indexEquiv).submatrix
    S.indexEquiv.symm S.indexEquiv.symm) at hm
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] using hm

end System

/-- Eliminate the internal entries of the root column of a polynomial right
inverse. Nilpotence is only used to obtain this right inverse. -/
theorem Represents.nil_of_matrix_nil {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (hT : IsNilpotent (S.matrix a)) : IsNilpotent x := by
  obtain ⟨Q, hQ⟩ := hT.isUnit_one_sub.exists_right_inv
  have hQ' : Q - S.matrix a * Q = 1 := by
    simpa only [sub_mul, one_mul] using hQ
  have hi : ∀ i, Q (some i) none = edge a (S.input i) * Q none none +
      ∑ j, edge a (S.step i j) * Q (some j) none := by
    intro i
    have h := congrArg (fun M => M (some i) none) hQ'
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
      Fintype.sum_option, System.matrix, sub_eq_zero] using h
  have he := hS (Q none none) (fun j => Q (some j) none) hi
  have hr : Q none none = 1 + Polynomial.X * (Polynomial.C x * Q none none) := by
    have h := congrArg (fun M => M none none) hQ'
    have h' : Q none none - Polynomial.X * (Polynomial.C x * Q none none) = 1 := by
      simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply,
        Fintype.sum_option, System.matrix, mul_assoc, ← Finset.mul_sum,
        ← mul_add, he] using h
    exact sub_eq_iff_eq_add.mp h'
  exact nilpotent_of_polynomial_resolvent x (Q none none) hr

/-- Each finite linearization gives a single-row pencil whose nilpotence
implies nilpotence of the represented element. -/
theorem Represents.nil_of_pencil_nil {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (hT : IsNilpotent (S.pencil.lift a)) : IsNilpotent x :=
  hS.nil_of_matrix_nil (S.matrix_nil_of_pencil_nil a hT)

end Linearization
end KoetheCounterexample

end KoetheProofPart13

/- ## KoetheLinearization -/

noncomputable section KoetheProofPart14

/-
# Nilness of the positive algebra from nilness of all root-row pencils

Every element of the nonunital algebra generated by three elements admits a
finite homogeneous-linear system. Its root-row pencil belongs to the exact
shared `Pencil` type, and nilpotence of that pencil implies nilpotence of the
element.

The strengthened adjoin induction below proves multiplication closure without
adding scalar/identity edges: besides linearizing `x`, it proves that left
multiplication by `x` preserves linearizability. At a generator this is the
`prepend` construction; the multiplication step is then composition.
-/

set_option autoImplicit false


namespace KoetheCounterexample

universe u v

variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

namespace Linearization

/-- Every positive algebra expression admits a finite homogeneous-linear
system. No dimension, cardinality, commutativity, or nilness hypothesis on the
ambient algebra is needed. -/
theorem linearizable_of_mem_adjoin (a : Fin 3 → R) {x : R}
    (hx : x ∈ NonUnitalAlgebra.adjoin k (Set.range a)) :
    Linearizable (k := k) a x := by
  have h : ∀ z, z ∈ NonUnitalAlgebra.adjoin k (Set.range a) →
      Linearizable (k := k) a z ∧
        ∀ y, Linearizable (k := k) a y → Linearizable (k := k) a (z * y) := by
    intro z hz
    induction hz using NonUnitalAlgebra.adjoin_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact ⟨linearizable_letter a i, fun y hy => linearizable_prepend hy i⟩
    | zero =>
        exact ⟨linearizable_zero a, fun y _ => by simpa using linearizable_zero (k := k) a⟩
    | add z w _ _ ihz ihw =>
        refine ⟨linearizable_add ihz.1 ihw.1, ?_⟩
        intro y hy
        rw [add_mul]
        exact linearizable_add (ihz.2 y hy) (ihw.2 y hy)
    | mul z w _ _ ihz ihw =>
        refine ⟨ihz.2 w ihw.1, ?_⟩
        intro y hy
        rw [mul_assoc]
        exact ihz.2 (w * y) (ihw.2 y hy)
    | smul r z _ ihz =>
        refine ⟨linearizable_smul ihz.1 r, ?_⟩
        intro y hy
        rw [smul_mul_assoc]
        exact linearizable_smul (ihz.2 y hy) r
  exact (h x hx).1

end Linearization

/-- A per-element root-row pencil certificate for any element of the generated
positive algebra. Its entries are homogeneous-linear in the generators, and
its parameter occurs solely in the distinguished row. -/
theorem exists_pencil_nil_imp_of_mem_adjoin (a : Fin 3 → R) {x : R}
    (hx : x ∈ NonUnitalAlgebra.adjoin k (Set.range a)) :
    ∃ (d : ℕ) (P : Pencil k d), IsNilpotent (P.lift a) → IsNilpotent x := by
  obtain ⟨S, hS⟩ := Linearization.linearizable_of_mem_adjoin a hx
  exact ⟨Fintype.card S.State, S.pencil, hS.nil_of_pencil_nil⟩

/-- If all homogeneous-linear, single-root-row pencils in the three generators
are nilpotent, then their generated nonunital algebra is nil. -/
theorem nil_of_all_pencils_nil (a : Fin 3 → R)
    (hall : ∀ (d : ℕ) (P : Pencil k d), IsNilpotent (P.lift a)) :
    ∀ x ∈ NonUnitalAlgebra.adjoin k (Set.range a), IsNilpotent x := by
  intro x hx
  obtain ⟨d, P, hP⟩ := exists_pencil_nil_imp_of_mem_adjoin a hx
  exact hP (hall d P)

end KoetheCounterexample

end KoetheProofPart14

/- ## KoetheShiftWitnessBand -/

noncomputable section KoetheProofPart15

/-
# Backward shifts and exact polynomial mortality

The coefficientwise band identity below retains the pencil's independent formal
variable. It does not deduce polynomial nilpotence from one specialization.
-/

set_option autoImplicit false

namespace KoetheCounterexample
namespace ShiftWitness

universe u v

abbrev Space (K : Type v) := ℕ → K
abbrev End (K : Type v) [Field K] := Module.End K (Space K)

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Backward weighted shifts: composition follows the forward chronological
order of the shared `Pencil.wordProd`. -/
def backShift (v : ℕ → Triple k) (i : Fin 3) : End K where
  toFun u n := algebraMap k K (v n i) * u (n + 1)
  map_add' u w := by ext n; simp [mul_add]
  map_smul' c u := by ext n; simp [mul_left_comm]

@[simp] theorem backShift_apply (v : ℕ → Triple k) (i : Fin 3)
    (u : Space K) (n : ℕ) :
    backShift (K := K) v i u n = algebraMap k K (v n i) * u (n + 1) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact coefficient action of a polynomial matrix supported on one shift band. -/
def HasBand (m : ℕ) (Q : Matrix ι ι (Polynomial (End K)))
    (C : ℕ → Matrix ι ι (Polynomial k)) : Prop :=
  ∀ r c q (u : Space K) n,
    ((Q r c).coeff q) u n = algebraMap k K ((C n r c).coeff q) * u (n + m)

omit [Fintype ι] in
theorem hasBand_one :
    HasBand (k := k) (K := K) (ι := ι) 0 1 (fun _ => 1) := by
  intro r c q u n
  by_cases hrc : r = c
  · subst c
    by_cases hq : q = 0
    · subst q; simp
    · simp [Polynomial.coeff_one, hq]
  · simp [hrc]

omit [DecidableEq ι] in
/-- Multiplication of bands keeps the chronological order and shifts the second
kernel by the width of the first band. -/
theorem HasBand.mul {m l : ℕ}
    {Q T : Matrix ι ι (Polynomial (End K))}
    {C D : ℕ → Matrix ι ι (Polynomial k)}
    (hQ : HasBand m Q C) (hT : HasBand l T D) :
    HasBand (m + l) (Q * T) (fun n => C n * D (n + m)) := by
  unfold HasBand at hQ hT
  intro r c q u n
  simp only [Matrix.mul_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_mul,
    LinearMap.sum_apply, Finset.sum_apply, Module.End.mul_apply, hQ, hT,
    map_sum, map_mul, Finset.sum_mul, Nat.add_assoc, mul_assoc]

theorem linear_combination_apply (v : ℕ → Triple k) (b : Fin 3 → k)
    (u : Space K) (n : ℕ) :
    (∑ i : Fin 3, algebraMap k (End K) (b i) * backShift v i : End K) u n =
      algebraMap k K (∑ i : Fin 3, v n i * b i) * u (n + 1) := by
  simp [LinearMap.sum_apply, Finset.sum_apply, Module.algebraMap_end_apply,
    Algebra.smul_def, Finset.mul_sum, mul_comm, mul_left_comm]

/-- The band kernel of a lifted pencil is its scalar polynomial evaluation at
the edge vector. -/
theorem pencil_hasBand {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) :
    HasBand 1 (P.lift (backShift (K := K) v)) (fun n => P.eval (v n)) := by
  intro r c q u n
  cases q with
  | zero =>
      simpa [Pencil.lift, Pencil.eval] using
        linear_combination_apply v (fun i => P.constant i r c) u n
  | succ q =>
      cases q with
      | zero =>
          simpa [Pencil.lift, Pencil.eval] using
            linear_combination_apply v (fun i => P.linear i r c) u n
      | succ q =>
          simp [Pencil.lift, Pencil.eval, Polynomial.coeff_X_mul]

@[simp] theorem window_zero {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) (n : ℕ) :
    P.window v n 0 = 1 := by simp [Pencil.window]

theorem window_succ {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) (n N : ℕ) :
    P.window v n (N + 1) = P.eval (v n) * P.window v (n + 1) N := by
  simp [Pencil.window, Pencil.wordProd, List.ofFn_succ, Nat.add_comm, Nat.add_left_comm]

/-- All coefficients of every power have the window kernel, not just its value
at a chosen rational function. -/
theorem pencil_pow_hasBand {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k) (N : ℕ) :
    HasBand N ((P.lift (backShift (K := K) v)) ^ N) (fun n => P.window v n N) := by
  induction N with
  | zero => simpa using (hasBand_one (k := k) (K := K) (ι := Fin (d + 1)))
  | succ N ih =>
      simpa only [pow_succ', window_succ, Nat.add_comm 1 N] using (pencil_hasBand P v).mul ih

/-- Uniformly zero windows imply actual nilpotence in the polynomial matrix
ring over the endomorphisms. -/
theorem pencil_nil_of_windows {d : ℕ} (P : Pencil k d) (v : ℕ → Triple k)
    (N : ℕ) (hN : ∀ n, P.window v n N = 0) :
    (P.lift (backShift (K := K) v)) ^ N = 0 := by
  ext r c q u n
  have h := pencil_pow_hasBand (K := K) P v N r c q u n
  simpa [hN] using h

theorem all_pencils_nil (v : ℕ → Triple k) (hv : UniversalMortalSequence k v) :
    ∀ (d : ℕ) (P : Pencil k d), IsNilpotent (P.lift (backShift (K := K) v)) := by
  intro d P
  obtain ⟨N, _, hN⟩ := hv.2 d P
  exact ⟨N, pencil_nil_of_windows P v N hN⟩

end ShiftWitness
end KoetheCounterexample

end KoetheProofPart15

/- ## KoetheShiftWitnessEigen -/

noncomputable section KoetheProofPart16

/-
# The rational-function eigenvector of the backward shifts

Nonzero edge triples give nonzero degree-at-most-two polynomials. Their images
in `RatFunc k` are invertible. Reciprocal prefix products produce a genuine
(non-finitely-supported) eigenvector on the full function space.
-/

set_option autoImplicit false

namespace KoetheCounterexample
namespace ShiftWitness

universe u
variable {k : Type u} [Field k]

/-- A triple encoded as a polynomial of degree at most two. -/
def edgePolynomial (z : Triple k) : Polynomial k :=
  Polynomial.C (z 0) + Polynomial.X * Polynomial.C (z 1) +
    Polynomial.X ^ 2 * Polynomial.C (z 2)

theorem edgePolynomial_ne_zero (z : Triple k) (hz : z ≠ 0) :
    edgePolynomial z ≠ 0 := by
  intro h
  apply hz
  funext i
  fin_cases i
  · have hc := congrArg (fun p : Polynomial k => p.coeff 0) h
    simpa [edgePolynomial] using hc
  · have hc := congrArg (fun p : Polynomial k => p.coeff 1) h
    simpa [edgePolynomial, Polynomial.coeff_mul_C] using hc
  · have hc := congrArg (fun p : Polynomial k => p.coeff 2) h
    simpa [edgePolynomial, Polynomial.coeff_mul_C] using hc

/-- The polynomial edge weight embedded faithfully in the rational-function field. -/
def edge (z : Triple k) : RatFunc k :=
  algebraMap (Polynomial k) (RatFunc k) (edgePolynomial z)

theorem edge_eq (z : Triple k) :
    edge z = algebraMap k (RatFunc k) (z 0) +
      RatFunc.X * algebraMap k (RatFunc k) (z 1) +
      RatFunc.X ^ 2 * algebraMap k (RatFunc k) (z 2) := by
  simp only [edge, edgePolynomial, map_add, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]

theorem edge_ne_zero (z : Triple k) (hz : z ≠ 0) : edge z ≠ 0 :=
  RatFunc.algebraMap_ne_zero (edgePolynomial_ne_zero z hz)

/-- Reciprocal prefix products, defined on the full sequence module. -/
def eigenvector (v : ℕ → Triple k) : Space (RatFunc k) :=
  fun n => (∏ i ∈ Finset.range n, edge (v i))⁻¹

@[simp] theorem eigenvector_zero (v : ℕ → Triple k) : eigenvector v 0 = 1 := by
  simp [eigenvector]

theorem eigenvector_ne_zero (v : ℕ → Triple k) : eigenvector v ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

theorem edge_mul_eigenvector_succ (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0) (n : ℕ) :
    edge (v n) * eigenvector v (n + 1) = eigenvector v n := by
  rw [eigenvector, Finset.prod_range_succ, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (edge_ne_zero (v n) (hv n)), one_mul]
  rfl

/-- The combined shift with transcendental scalar coefficients fixes a nonzero
vector. This is not a scalar combination over the ground field `k`. -/
theorem combined_shift_eigenvector (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0) :
    (backShift v 0 + (RatFunc.X : RatFunc k) • backShift v 1 +
      (RatFunc.X : RatFunc k) ^ 2 • backShift v 2 : End (RatFunc k)) (eigenvector v) = eigenvector v := by
  ext n
  change algebraMap k (RatFunc k) (v n 0) * eigenvector v (n + 1) +
      RatFunc.X * (algebraMap k (RatFunc k) (v n 1) * eigenvector v (n + 1)) +
      RatFunc.X ^ 2 * (algebraMap k (RatFunc k) (v n 2) * eigenvector v (n + 1)) = _
  calc
    _ = edge (v n) * eigenvector v (n + 1) := by rw [edge_eq]; ring
    _ = eigenvector v n := edge_mul_eigenvector_succ v hv n

end ShiftWitness
end KoetheCounterexample

end KoetheProofPart16

/- ## KoetheShiftWitnessEndpoint -/

noncomputable section KoetheProofPart17

/-
# A nil ideal with a nonnilpotent two-by-two matrix

A fixed vector for `a₀ + t a₁ + t² a₂` yields a companion matrix with a
nonzero eigenvalue after inverting `1 - a₀`. Squaring puts every entry in the
nil ideal. No matrix-nilness principle is used.
-/

set_option autoImplicit false

namespace KoetheCounterexample
namespace ShiftWitness

universe u v w

section Companion

variable {K : Type u} [Field K] {M : Type v} [AddCommGroup M] [Module K M]
variable {R : Type w} [Ring R]

/-- The action of a matrix of represented ring elements on two copies of the
representation space. -/
def matrixAction (φ : R →+* Module.End K M) :
    Matrix (Fin 2) (Fin 2) R →+* Module.End K (Fin 2 → M) :=
  (endVecRingEquivMatrixEnd (Fin 2) K M).symm.toRingHom.comp φ.mapMatrix

@[simp] theorem matrixAction_apply (φ : R →+* Module.End K M)
    (H : Matrix (Fin 2) (Fin 2) R) (z : Fin 2 → M) (i : Fin 2) :
    matrixAction φ H z i = ∑ j, φ (H i j) (z j) := rfl

/-- A nonzero eigenvalue on a nonzero vector excludes nilpotence, without
finite-dimensionality assumptions. -/
theorem not_nilpotent_of_eigenvector (f : Module.End K M) (t : K) (z : M)
    (ht : t ≠ 0) (hz : z ≠ 0) (he : f z = t • z) : ¬ IsNilpotent f := by
  have hp : ∀ n : ℕ, (f ^ n) z = t ^ n • z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [pow_succ', Module.End.mul_apply, ih, map_smul, he, smul_smul]
        rw [mul_comm]
  rintro ⟨n, hn⟩
  have hz' : t ^ n • z = 0 := by rw [← hp n, hn]; rfl
  exact (smul_ne_zero (pow_ne_zero n ht) hz) hz'

/-- General companion-matrix endpoint. The scalar `t` lives in the
representation field, not necessarily in the ground field of the nil ideal. -/
theorem nonnil_matrix_of_fixed_vector
    (I : TwoSidedIdeal R) (hI : ∀ x ∈ I, IsNilpotent x)
    (φ : R →+* Module.End K M) (a : Fin 3 → R) (ha : ∀ i, a i ∈ I)
    (t : K) (ht : t ≠ 0) (z : M) (hz : z ≠ 0)
    (he : (φ (a 0) + t • φ (a 1) + t ^ 2 • φ (a 2)) z = z) :
    ∃ W : Matrix (Fin 2) (Fin 2) R,
      W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  obtain ⟨g, hg⟩ := (hI (a 0) (ha 0)).isUnit_one_sub.exists_left_inv
  let b : R := g * a 1
  let c : R := g * a 2
  have hb : b ∈ I := I.mul_mem_left g (a 1) (ha 1)
  have hc : c ∈ I := I.mul_mem_left g (a 2) (ha 2)
  have hleft : φ g * (1 - φ (a 0)) = 1 := by
    rw [← map_one φ, ← map_sub, ← map_mul, hg, map_one]
  have hrel : (1 - φ (a 0)) z = t • φ (a 1) z + t ^ 2 • φ (a 2) z := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply] at he
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    exact (sub_eq_iff_eq_add).mpr (by
      simpa [add_comm, add_left_comm, add_assoc] using he.symm)
  have hzrel : z = t • φ b z + t ^ 2 • φ c z := by
    calc
      z = (φ g * (1 - φ (a 0))) z := by rw [hleft]; rfl
      _ = φ g ((1 - φ (a 0)) z) := rfl
      _ = t • φ b z + t ^ 2 • φ c z := by
        rw [hrel, map_add, map_smul, map_smul]
        simp only [b, c, map_mul, Module.End.mul_apply]
  have hcomp : φ b z + t • φ c z = t⁻¹ • z := by
    conv_rhs => rw [hzrel]
    simp [smul_add, smul_smul, pow_two, ht]
  let H : Matrix (Fin 2) (Fin 2) R := !![b, c; 1, 0]
  let zz : Fin 2 → M := ![z, t • z]
  have hzz : zz ≠ 0 := by
    intro h
    apply hz
    exact congrFun h 0
  have heH : matrixAction φ H zz = t⁻¹ • zz := by
    ext i
    fin_cases i
    · simpa [H, zz, Fin.sum_univ_two, map_smul] using hcomp
    · simp [H, zz, Fin.sum_univ_two, smul_smul, ht]
  refine ⟨H ^ 2, ?_, ?_⟩
  · rw [TwoSidedIdeal.mem_matrix]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [H, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    · exact I.add_mem (I.mul_mem_right b b hb) hc
    · exact I.mul_mem_right b c hb
    · exact hb
    · exact hc
  · intro hnil
    exact not_nilpotent_of_eigenvector (matrixAction φ H) t⁻¹ zz
      (inv_ne_zero ht) hzz heH (hnil.of_pow.map (matrixAction φ))

end Companion

section Unitization

variable {k : Type u} [Field k] {B : Type v} [Ring B] [Nontrivial B] [Algebra k B]

/-- The canonical augmentation ideal in the unitization of a positive algebra. -/
def augmentationIdeal (A : NonUnitalSubalgebra k B) : TwoSidedIdeal (Unitization k A) :=
  TwoSidedIdeal.ker (Unitization.fstHom k A)

omit [Nontrivial B] in
@[simp] theorem mem_augmentationIdeal (A : NonUnitalSubalgebra k B) (x : Unitization k A) :
    x ∈ augmentationIdeal A ↔ x.fst = 0 := by
  rw [augmentationIdeal, TwoSidedIdeal.mem_ker]
  rfl

/-- A nil positive algebra omits the ambient identity. -/
theorem one_not_mem_of_nil (A : NonUnitalSubalgebra k B)
    (hA : ∀ x ∈ A, IsNilpotent x) : (1 : B) ∉ A := by
  intro h
  exact not_isNilpotent_one (hA 1 h)

/-- The augmentation ideal is nil. We reflect nilpotence along the faithful
unitization map instead of treating a nonunital algebra as if it had a unit. -/
theorem augmentationIdeal_nil (A : NonUnitalSubalgebra k B)
    (hA : ∀ x ∈ A, IsNilpotent x) :
    ∀ x ∈ augmentationIdeal A, IsNilpotent x := by
  intro x hx
  have hinj := NonUnitalSubalgebra.unitization_injective A (one_not_mem_of_nil A hA)
  apply (IsNilpotent.map_iff hinj).mp
  have hfst : x.fst = 0 := (mem_augmentationIdeal A x).mp hx
  simpa [NonUnitalSubalgebra.unitization_apply, hfst] using hA (x.snd : B) x.snd.property

/-- A nil nonunital subalgebra with a transcendental-scalar fixed vector gives
an actual nil ideal in a unital ring. The ring is its unitization; its action
need not be faithful, although nilness is reflected using the faithful natural
unitization map into the ambient algebra. -/
theorem exists_witness_of_nil_subalgebra
    {K : Type w} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    (A : NonUnitalSubalgebra k B) (hA : ∀ x ∈ A, IsNilpotent x)
    (φ : B →+* Module.End K M) (a : Fin 3 → B) (ha : ∀ i, a i ∈ A)
    (t : K) (ht : t ≠ 0) (z : M) (hz : z ≠ 0)
    (he : (φ (a 0) + t • φ (a 1) + t ^ 2 • φ (a 2)) z = z) :
    ∃ (R : Type (max u v)) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  let ψ : Unitization k A →+* Module.End K M :=
    φ.comp (NonUnitalSubalgebra.unitization A).toRingHom
  let a' : Fin 3 → Unitization k A := fun i => Unitization.inr ⟨a i, ha i⟩
  have ha' : ∀ i, a' i ∈ augmentationIdeal A := by
    intro i
    simp [a']
  have hψ : ∀ i, ψ (a' i) = φ (a i) := by
    intro i
    simp [ψ, a', NonUnitalSubalgebra.unitization_apply]
  have hI := augmentationIdeal_nil A hA
  refine ⟨Unitization k A, inferInstance, augmentationIdeal A, hI, ?_⟩
  apply nonnil_matrix_of_fixed_vector (augmentationIdeal A) hI ψ a' ha' t ht z hz
  simpa only [hψ] using he

end Unitization

end ShiftWitness
end KoetheCounterexample

end KoetheProofPart17

/- ## KoetheShiftWitness -/

noncomputable section KoetheProofPart18

/-
# Downstream witness from a universal mortal sequence

The only theorem hypothesis in the final construction is scalar linearization,
stated at the concrete backward-shift operator algebra. The unrestricted
`nil_of_all_pencils_nil` theorem can be supplied directly to this hypothesis.
All window-to-polynomial and nonnilpotent-matrix bridges are proved here.

The witness ring is the unitization over `k` of the positive shift algebra,
and its nil ideal is the kernel of the scalar projection. The universe of the
existential witness is exactly the universe of the ground field.
-/

set_option autoImplicit false

namespace KoetheCounterexample
namespace ShiftWitness

universe u
variable {k : Type u} [Field k]

-- Keep the scalar module structure definitionally aligned with the algebra API.
local instance : Module k (End (RatFunc k)) := Algebra.toModule

/-- The positive algebra is generated over `k`, NOT over `RatFunc k`. -/
def positiveAlgebra (v : ℕ → Triple k) : NonUnitalSubalgebra k (End (RatFunc k)) :=
  NonUnitalAlgebra.adjoin k (Set.range (backShift (K := RatFunc k) v))

/-- Once the positive shift algebra is nil, the rational-function eigenvector
gives a nil ideal and nonnilpotent matrix in its actual unitization. -/
theorem witness_from_nil_positive (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0)
    (hA : ∀ x ∈ positiveAlgebra v, IsNilpotent x) :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  refine exists_witness_of_nil_subalgebra (positiveAlgebra v) hA
    (RingHom.id (End (RatFunc k))) (backShift (K := RatFunc k) v) ?_
    (RatFunc.X : RatFunc k) RatFunc.X_ne_zero (eigenvector v) (eigenvector_ne_zero v) ?_
  · intro i
    exact NonUnitalAlgebra.subset_adjoin k (Set.mem_range_self i)
  · simpa only [RingHom.id_apply] using combined_shift_eigenvector v hv

/-- Universe-preserving existential form of the requested nil-ideal plus
nonnilpotent `Fin 2` matrix witness. Scalar linearization is an explicit theorem
argument, not an axiom. Only its specialization to the concrete operator algebra
is needed, so a universe-polymorphic linearization theorem plugs in directly. -/
theorem exists_nilideal_nonnil_matrix
    (v : ℕ → Triple k) (hv : UniversalMortalSequence k v)
    (hlinear : ∀ (a : Fin 3 → End (RatFunc k)),
      (∀ (d : ℕ) (P : Pencil k d), IsNilpotent (P.lift a)) →
        ∀ x ∈ NonUnitalAlgebra.adjoin k (Set.range a), IsNilpotent x) :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  apply witness_from_nil_positive v hv.1
  exact hlinear (backShift v) (all_pencils_nil (K := RatFunc k) v hv)

end ShiftWitness
end KoetheCounterexample

end KoetheProofPart18

/- ## KoetheShiftWitnessComplete -/

noncomputable section KoetheProofPart19

/-
# Plugging the completed scalar-linearization theorem into the shift witness

The main shift-witness file is independent of the linearization implementation.
This integration file discharges its explicit theorem hypothesis using
`KoetheCounterexample.nil_of_all_pencils_nil`.
-/

set_option autoImplicit false

namespace KoetheCounterexample

universe u

/-- A universal mortal sequence over any field produces a nil two-sided ideal
in a unital ring, with a nonnilpotent two-by-two matrix over that ideal. -/
theorem exists_nilideal_nonnil_matrix_of_universal_mortal
    {k : Type u} [Field k] (v : ℕ → Triple k) (hv : UniversalMortalSequence k v) :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  exact ShiftWitness.exists_nilideal_nonnil_matrix v hv nil_of_all_pencils_nil

end KoetheCounterexample

end KoetheProofPart19

/- ## KoetheEndToEnd -/

noncomputable section KoetheProofPart20

set_option autoImplicit false


universe u

namespace KoetheCounterexample

abbrev GroundField : Type u := AlgebraicClosure (ULift.{u} (ZMod 2))

instance : Countable (GroundField.{u}) := by
  apply Set.countable_univ_iff.mp
  have halg : ∀ x : GroundField.{u}, IsAlgebraic (ULift.{u} (ZMod 2)) x :=
    Algebra.IsAlgebraic.isAlgebraic
  simpa only [halg, Set.setOf_true] using
    Algebraic.countable (ULift.{u} (ZMod 2)) (GroundField.{u})

/-- A counterexample to nilness of finite matrix ideals. -/
theorem counterexample :
    ∃ (R : Type u) (_ : Ring R) (I : TwoSidedIdeal R),
      (∀ x ∈ I, IsNilpotent x) ∧
        ∃ W : Matrix (Fin 2) (Fin 2) R,
          W ∈ TwoSidedIdeal.matrix (Fin 2) I ∧ ¬ IsNilpotent W := by
  obtain ⟨v, hv⟩ := exists_universalMortalSequence (GroundField.{u})
    (maskMortality (GroundField.{u}))
  exact exists_nilideal_nonnil_matrix_of_universal_mortal v hv


end KoetheCounterexample

end KoetheProofPart20



open Ideal TwoSidedIdeal Polynomial

open Matrix

variable {R : Type*}

variable [Ring R]

namespace Koethe

/-- Say a subset `I` of a ring `R` is nilpotent if all its elements are nilpotent. -/
def IsNil {S : Type*} [SetLike S R] (I : S) := ∀ i ∈ I, IsNilpotent i

-- TODO(lezeau): add some basic API and already known results for nil ideals

variable (R) in
/-- The *Kothe Radical* of a ring `R` is the sum of all (two-sided) nil ideals of `R`.
Tags: Kothe Radical, upper nilradical-/
def KotheRadical : TwoSidedIdeal R := sSup {I : TwoSidedIdeal R | IsNil I}

-- This is often denoted `Nil*(R)`
local notation "Nil* " R => KotheRadical R

/-
TODO(lezeau): The two last statements I want to formalize use the (two-sided) Jacobson ideal.
Sanity check that the current mathlib definition is what I want.
-/

end Koethe

open scoped Classical in
/--
**Disproof of the Köthe conjecture in Krempa's matrix form** (the `KotherConjecture.variants.general_matrix`
statement of the benchmark file): it is not the case that for every ring `R`, every nil two-sided ideal `I`
and every finite index type `n`, the matrix ideal `M_n(I)` is nil.
-/
theorem Koethe.KotherConjecture.variants.general_matrix.disproof : ¬ (∀ {R : Type*} [Ring R] {I : TwoSidedIdeal R},
    IsNil I → ∀ (n : Type*) [Fintype n], IsNil (matrix n I)) := by
  classical
  intro h
  obtain ⟨S, hS, I, hI, W, hW, hn⟩ := KoetheCounterexample.counterexample
  letI : Ring S := hS
  have ht := @h S hS I hI (ULift (Fin 2)) inferInstance
  letI : DecidableEq (ULift (Fin 2)) := Classical.decEq _
  let e := Matrix.reindexAlgEquiv ℕ S (Equiv.ulift.symm : Fin 2 ≃ ULift (Fin 2))
  apply hn
  apply (IsNilpotent.map_iff e.injective).mp
  apply ht (e W)
  rw [TwoSidedIdeal.mem_matrix] at hW ⊢
  intro i j
  exact hW i.down j.down
