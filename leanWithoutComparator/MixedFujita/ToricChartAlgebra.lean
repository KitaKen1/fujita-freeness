/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BirationalBaseChange
public import MixedFujita.ToricSubstitutionBirational
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.RingHom.Etale

/-!
The ring of the toric chart over an étale algebra (step 12, section 6.1 of the manuscript). Let R
be an étale algebra over the polynomial ring K[x] and M a matrix of natural numbers with an
integer inverse. The ring of the toric chart is B = K[u] ⊗_{K[x]} R, where K[u] is an algebra over
K[x] through the monomial substitution x_i ↦ u^(M_i). It is étale over K[u], and, the substitution
being birational and R flat over K[x], it is a domain containing R with the same fraction field
when R is a domain. If the coordinates x_i, i ∈ S₀, vanish at a prime 𝔭 of R, the rows of M outside
S₀ are unit rows and the diagonal of M is positive, then the ring map B → R/𝔭 sending u_l to 0 for
l ∈ S₀ and to x_l otherwise gives a prime of B over 𝔭 containing the u_l, l ∈ S₀.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

section Target

variable (K : Type u) [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)

/-- The target polynomial ring of the monomial substitution with matrix M, as an algebra over
the source polynomial ring through the substitution. -/
def ToricTarget (K : Type u) [Field K] {n : ℕ} (_M : Matrix (Fin n) (Fin n) ℕ) : Type u :=
  MvPolynomial (Fin n) K

noncomputable instance toricTargetCommRing : CommRing (ToricTarget K M) :=
  inferInstanceAs (CommRing (MvPolynomial (Fin n) K))

instance toricTargetIsDomain : IsDomain (ToricTarget K M) :=
  inferInstanceAs (IsDomain (MvPolynomial (Fin n) K))

noncomputable instance toricTargetAlgebra : Algebra K (ToricTarget K M) :=
  inferInstanceAs (Algebra K (MvPolynomial (Fin n) K))

noncomputable instance toricTargetSubstAlgebra :
    Algebra (MvPolynomial (Fin n) K) (ToricTarget K M) :=
  (toricSubst (K := K) M).toRingHom.toAlgebra

instance toricTargetIsScalarTower :
    IsScalarTower K (MvPolynomial (Fin n) K) (ToricTarget K M) :=
  IsScalarTower.of_algebraMap_eq fun k => ((toricSubst (K := K) M).commutes k).symm

/-- A polynomial, as an element of the target of the substitution. -/
def toricTargetOf (p : MvPolynomial (Fin n) K) : ToricTarget K M := p

variable {K M}

theorem toricTarget_algebraMap (p : MvPolynomial (Fin n) K) :
    algebraMap (MvPolynomial (Fin n) K) (ToricTarget K M) p = toricSubst M p :=
  rfl

/-- The fraction field of the target of a unimodular monomial substitution is a fraction field of
the source: the substitution is birational. -/
theorem toricTarget_isFractionRing (N : Matrix (Fin n) (Fin n) ℤ)
    (hMN : M.map (Nat.cast : ℕ → ℤ) * N = 1) (hNM : N * M.map (Nat.cast : ℕ → ℤ) = 1) :
    IsFractionRing (MvPolynomial (Fin n) K) (FractionRing (ToricTarget K M)) := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n) K) (FractionRing (ToricTarget K M))) := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin n) K) (ToricTarget K M)
      (FractionRing (ToricTarget K M))]
    exact (IsFractionRing.injective (ToricTarget K M) (FractionRing (ToricTarget K M))).comp
      (toricSubst_injective M N hMN)
  have : FaithfulSMul (MvPolynomial (Fin n) K) (FractionRing (ToricTarget K M)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  apply IsFractionRing.of_field
  intro z
  obtain ⟨p, q, -, hz⟩ := @toricSubst_exists_div (Fin n) K _ _ _ M N hMN hNM
    (FractionRing (ToricTarget K M)) _
    (inferInstance : Algebra (ToricTarget K M) (FractionRing (ToricTarget K M)))
    (inferInstance : IsFractionRing (ToricTarget K M) (FractionRing (ToricTarget K M))) z
  refine ⟨p, q, ?_⟩
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K) (ToricTarget K M)
    (FractionRing (ToricTarget K M)) p, IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) K)
    (ToricTarget K M) (FractionRing (ToricTarget K M)) q]
  exact hz

end Target

section Algebra

variable (K : Type u) [Field K] {n : ℕ} (M : Matrix (Fin n) (Fin n) ℕ)
  (R : Type u) [CommRing R] [Algebra K R] [Algebra (MvPolynomial (Fin n) K) R]
  [IsScalarTower K (MvPolynomial (Fin n) K) R]

/-- The ring of the toric chart with matrix M over an algebra R over the polynomial ring. -/
abbrev ToricChartAlgebra : Type u := ToricTarget K M ⊗[MvPolynomial (Fin n) K] R

/-- The inclusion of R in the ring of the toric chart. -/
noncomputable def toricChartInclusion : R →ₐ[K] ToricChartAlgebra K M R :=
  (Algebra.TensorProduct.includeRight :
    R →ₐ[MvPolynomial (Fin n) K] ToricChartAlgebra K M R).restrictScalars K

/-- The coordinates u of the toric chart. -/
noncomputable def toricChartCoords : MvPolynomial (Fin n) K →ₐ[K] ToricChartAlgebra K M R where
  toRingHom := (algebraMap (ToricTarget K M) (ToricChartAlgebra K M R) :
    ToricTarget K M →+* ToricChartAlgebra K M R)
  commutes' k := by
    change algebraMap (ToricTarget K M) (ToricChartAlgebra K M R)
      (algebraMap K (ToricTarget K M) k) = algebraMap K (ToricChartAlgebra K M R) k
    rw [← IsScalarTower.algebraMap_apply]

theorem toricChartInclusion_apply (r : R) :
    toricChartInclusion K M R r = (1 : ToricTarget K M) ⊗ₜ[MvPolynomial (Fin n) K] r :=
  rfl

omit [Algebra K R] [IsScalarTower K (MvPolynomial (Fin n) K) R] in
theorem toricChartCoords_apply (p : MvPolynomial (Fin n) K) :
    toricChartCoords K M R p = toricTargetOf K M p ⊗ₜ[MvPolynomial (Fin n) K] (1 : R) :=
  rfl

/-- The inclusion sends the coordinates x of R to the monomials in the coordinates u. -/
theorem toricChartInclusion_algebraMap (p : MvPolynomial (Fin n) K) :
    toricChartInclusion K M R (algebraMap (MvPolynomial (Fin n) K) R p) =
      toricChartCoords K M R (toricSubst M p) := by
  rw [toricChartInclusion_apply, toricChartCoords_apply, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  rfl

variable [Algebra.Etale (MvPolynomial (Fin n) K) R]

omit [Algebra K R] [IsScalarTower K (MvPolynomial (Fin n) K) R] in
/-- The ring of the toric chart is étale over its coordinates. -/
theorem toricChartCoords_etale : (toricChartCoords K M R).toRingHom.Etale := by
  have h : Algebra.Etale (ToricTarget K M) (ToricChartAlgebra K M R) := inferInstance
  have hT : (algebraMap (ToricTarget K M) (ToricChartAlgebra K M R)).Etale :=
    RingHom.etale_algebraMap.mpr h
  exact hT

section Prime

omit [Algebra.Etale (MvPolynomial (Fin n) K) R] in
/-- A prime of the ring of the toric chart over a prime of R at which the coordinates in S₀
vanish, containing the coordinates u_k, k ∈ S₀: the rows of M outside S₀ are unit rows and the
diagonal of M is positive. -/
theorem exists_toricChart_prime (S₀ : Set (Fin n))
    (hrow : ∀ i, i ∉ S₀ → ∀ l, M i l = if i = l then 1 else 0) (hdiag : ∀ i, 1 ≤ M i i)
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (h𝔭 : ∀ i ∈ S₀, algebraMap (MvPolynomial (Fin n) K) R (MvPolynomial.X i) ∈ 𝔭) :
    ∃ 𝔓 : Ideal (ToricChartAlgebra K M R), 𝔓.IsPrime ∧
      𝔓.comap (toricChartInclusion K M R) = 𝔭 ∧
      ∀ k ∈ S₀, toricChartCoords K M R (MvPolynomial.X k) ∈ 𝔓 := by
  classical
  let ρ : R →+* R ⧸ 𝔭 := Ideal.Quotient.mk 𝔭
  let τ' : MvPolynomial (Fin n) K →ₐ[K] R ⧸ 𝔭 := MvPolynomial.aeval fun l =>
    if l ∈ S₀ then (0 : R ⧸ 𝔭) else ρ (algebraMap (MvPolynomial (Fin n) K) R (MvPolynomial.X l))
  have hτX : ∀ l, τ' (MvPolynomial.X l) = if l ∈ S₀ then (0 : R ⧸ 𝔭) else
      ρ (algebraMap (MvPolynomial (Fin n) K) R (MvPolynomial.X l)) := fun l =>
    MvPolynomial.aeval_X _ l
  have hcomp : τ'.comp (toricSubst M) =
      (Ideal.Quotient.mkₐ K 𝔭).comp (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) R) := by
    apply MvPolynomial.algHom_ext
    intro i
    change τ' (toricSubst M (MvPolynomial.X i)) =
      ρ (algebraMap (MvPolynomial (Fin n) K) R (MvPolynomial.X i))
    by_cases hi : i ∈ S₀
    · rw [ringHom_toricSubst_X τ' M i, Finset.prod_eq_zero (Finset.mem_univ i)
        (by rw [hτX i, ite_eq_left hi, zero_pow (by have := hdiag i; omega)])]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (h𝔭 i hi)).symm
    · rw [toricSubst_X_of_row M i (hrow i hi), hτX i, ite_eq_right hi]
  have h : ∀ a : MvPolynomial (Fin n) K,
      (τ'.toRingHom : MvPolynomial (Fin n) K →+* R ⧸ 𝔭) (algebraMap (MvPolynomial (Fin n) K) (ToricTarget K M) a) =
        ρ (algebraMap (MvPolynomial (Fin n) K) R a) := fun a =>
    congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] R ⧸ 𝔭 => f a) hcomp
  obtain ⟨π, hπ⟩ := baseChange_exists_ringHom (A := MvPolynomial (Fin n) K)
    (A' := ToricTarget K M) (R := R) (τ'.toRingHom : MvPolynomial (Fin n) K →+* R ⧸ 𝔭) ρ h
  refine ⟨RingHom.ker π, RingHom.ker_isPrime π, ?_, fun k hk => ?_⟩
  · ext r
    rw [Ideal.mem_comap, RingHom.mem_ker, toricChartInclusion_apply, hπ]
    change τ' 1 * ρ r = 0 ↔ r ∈ 𝔭
    rw [map_one, one_mul]
    exact Ideal.Quotient.eq_zero_iff_mem
  · rw [RingHom.mem_ker, toricChartCoords_apply, hπ]
    change τ' (MvPolynomial.X k) * ρ 1 = 0
    rw [hτX k, ite_eq_left hk, zero_mul]

end Prime

variable [IsDomain R]

section Birational

variable (N : Matrix (Fin n) (Fin n) ℤ) (hMN : M.map (Nat.cast : ℕ → ℤ) * N = 1)
  (hNM : N * M.map (Nat.cast : ℕ → ℤ) = 1)

include hMN hNM

omit [Algebra K R] [IsScalarTower K (MvPolynomial (Fin n) K) R] in
/-- The ring of the toric chart of a unimodular matrix over an étale domain is a domain. -/
theorem toricChartAlgebra_isDomain : IsDomain (ToricChartAlgebra K M R) := by
  have := toricTarget_isFractionRing (K := K) (M := M) N hMN hNM
  exact birationalBaseChange_isDomain (A := MvPolynomial (Fin n) K) (A' := ToricTarget K M)
    (R := R) (F := FractionRing (ToricTarget K M))
    (IsFractionRing.injective (ToricTarget K M) (FractionRing (ToricTarget K M)))

/-- The étale domain embeds in the ring of the toric chart. -/
theorem toricChartInclusion_injective : Function.Injective (toricChartInclusion K M R) := by
  have := toricTarget_isFractionRing (K := K) (M := M) N hMN hNM
  exact birationalBaseChange_includeRight_injective (A := MvPolynomial (Fin n) K)
    (A' := ToricTarget K M) (R := R) (FractionRing (ToricTarget K M))

/-- Every element of the ring of the toric chart is a quotient of two elements of the étale
domain: the toric chart is birational. -/
theorem toricChartInclusion_exists_fraction (b : ToricChartAlgebra K M R) :
    ∃ r s : R, s ≠ 0 ∧ toricChartInclusion K M R s * b = toricChartInclusion K M R r := by
  have := toricTarget_isFractionRing (K := K) (M := M) N hMN hNM
  exact birationalBaseChange_exists_fraction (A := MvPolynomial (Fin n) K)
    (A' := ToricTarget K M) (R := R) (F := FractionRing (ToricTarget K M))
    (IsFractionRing.injective (ToricTarget K M) (FractionRing (ToricTarget K M))) b

omit [Algebra K R] [IsScalarTower K (MvPolynomial (Fin n) K) R] in
/-- The coordinates of the toric chart are nonzero. -/
theorem toricChartCoords_X_ne_zero (k : Fin n) :
    toricChartCoords K M R (MvPolynomial.X k) ≠ 0 := by
  have := toricChartAlgebra_isDomain K M R N hMN hNM
  have hinj : Function.Injective (algebraMap (ToricTarget K M) (ToricChartAlgebra K M R)) :=
    FaithfulSMul.algebraMap_injective (ToricTarget K M) (ToricChartAlgebra K M R)
  intro h
  exact MvPolynomial.X_ne_zero (R := K) k (hinj (h.trans (map_zero _).symm))

end Birational

end Algebra

end MixedFujita
