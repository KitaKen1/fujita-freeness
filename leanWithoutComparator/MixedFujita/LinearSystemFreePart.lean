/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LinearSystemCommonDenominator
public import MixedFujita.LinearSystemRelationBound
public import MixedFujita.PolynomialRingDimension

/-!
The free part over the parameters sandwiches the coordinate ring. For the independent low
monomials B and the common denominator δ, the degree-m part of K[X]/P contains the free
combinations Σ_b q_b(y) X^b with deg q_b = m - |b| and, after multiplying by δ, is contained
in the free combinations of degree m + deg δ. Hence, with r = |B|,
r · dim R_(m-t) ≤ dim (K[X]/P)_m ≤ r · dim R_(m+deg δ), where R is the polynomial ring in
the d + 1 parameters. No Hilbert polynomial is constructed.
-/

@[expose] public section

open MvPolynomial Finset

namespace MixedFujita

variable {K : Type*} [Field K] {σ : Type*} [Fintype σ] {P : Ideal (MvPolynomial σ K)} {d : ℕ}
  (y : Fin (d + 1) → MvPolynomial σ K)

/-- The free combinations over B with admissible coefficients, into the quotient. -/
noncomputable def linearSystemFreeMap (B : Finset (σ →₀ ℕ)) (m : ℕ) :
    (∀ b : B, linearSystemCoeffSpace (K := K) d m b.1) →ₗ[K] MvPolynomial σ K ⧸ P :=
  ∑ b : B, (Ideal.Quotient.mkₐ K P).toLinearMap ∘ₗ (LinearMap.mulRight K (monomial b.1 (1 : K))) ∘ₗ
    (aeval y).toLinearMap ∘ₗ (linearSystemCoeffSpace (K := K) d m b.1).subtype ∘ₗ LinearMap.proj b

omit [Fintype σ] in
theorem linearSystemFreeMap_apply (B : Finset (σ →₀ ℕ)) (m : ℕ)
    (c : ∀ b : B, linearSystemCoeffSpace (K := K) d m b.1) :
    linearSystemFreeMap (P := P) y B m c =
      Ideal.Quotient.mk P (∑ b : B, aeval y (c b : MvPolynomial (Fin (d + 1)) K) *
        monomial b.1 (1 : K)) := by
  simp [linearSystemFreeMap, map_sum]

open Classical in
/-- The coefficient function of a dependent family, extended by zero. -/
noncomputable def linearSystemExtend {B : Finset (σ →₀ ℕ)} {m : ℕ}
    (c : ∀ b : B, linearSystemCoeffSpace (K := K) d m b.1) : (σ →₀ ℕ) → MvPolynomial (Fin (d + 1)) K :=
  fun b => if h : b ∈ B then (c ⟨b, h⟩ : MvPolynomial (Fin (d + 1)) K) else 0

omit [Fintype σ] in
theorem linearSystemExtend_mem {B : Finset (σ →₀ ℕ)} {m : ℕ}
    (c : ∀ b : B, linearSystemCoeffSpace (K := K) d m b.1) :
    ∀ b ∈ B, linearSystemExtend c b ∈ linearSystemCoeffSpace (K := K) d m b := by
  intro b hb
  simp only [linearSystemExtend, hb, ↓reduceDIte]
  exact (c ⟨b, hb⟩).2

omit [Fintype σ] in
theorem linearSystemExtend_sum {B : Finset (σ →₀ ℕ)} {m : ℕ}
    (c : ∀ b : B, linearSystemCoeffSpace (K := K) d m b.1) :
    ∑ b ∈ B, aeval y (linearSystemExtend c b) * monomial b (1 : K) =
      ∑ b : B, aeval y (c b : MvPolynomial (Fin (d + 1)) K) * monomial b.1 (1 : K) := by
  rw [← Finset.sum_attach B, ← Finset.univ_eq_attach]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [linearSystemExtend, b.2, ↓reduceDIte]

omit [Fintype σ] in
/-- Independence makes the free map injective. -/
theorem linearSystemFreeMap_injective {B : Finset (σ →₀ ℕ)} (hB : LinearSystemIndependent y P B)
    (m : ℕ) : Function.Injective (linearSystemFreeMap (P := P) y B m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  rw [linearSystemFreeMap_apply, Ideal.Quotient.eq_zero_iff_mem, ← linearSystemExtend_sum] at hc
  have h0 := hB m (linearSystemExtend c) (linearSystemExtend_mem c) hc
  funext b
  apply Subtype.ext
  have := h0 b.1 b.2
  simp only [linearSystemExtend, b.2, ↓reduceDIte] at this
  simpa using this

omit [Fintype σ] in
instance linearSystemCoeffSpace_finiteDimensional (m : ℕ) (b : σ →₀ ℕ) :
    FiniteDimensional K (linearSystemCoeffSpace (K := K) d m b) := by
  unfold linearSystemCoeffSpace
  by_cases hb : b.degree ≤ m
  · rw [ite_eq_left hb]
    infer_instance
  · rw [ite_eq_right hb]
    infer_instance

omit [Fintype σ] in
theorem finrank_linearSystemCoeffSpace (m : ℕ) (b : σ →₀ ℕ) :
    Module.finrank K (linearSystemCoeffSpace (K := K) d m b) =
      if b.degree ≤ m then (m - b.degree + d).choose d else 0 := by
  unfold linearSystemCoeffSpace
  by_cases hb : b.degree ≤ m
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact finrank_homogeneousSubmodule_fin K d (m - b.degree)
  · rw [ite_eq_right hb, ite_eq_right hb]
    exact finrank_bot K _

omit [Fintype σ] in
theorem finrank_linearSystemFreeDomain (B : Finset (σ →₀ ℕ)) (m : ℕ) :
    Module.finrank K (∀ b : B, linearSystemCoeffSpace (K := K) d m b.1) =
      ∑ b ∈ B, if b.degree ≤ m then (m - b.degree + d).choose d else 0 := by
  rw [Module.finrank_pi_fintype]
  simp only [finrank_linearSystemCoeffSpace]
  rw [← Finset.sum_attach B, ← Finset.univ_eq_attach]

omit [Fintype σ] in
/-- The free combinations of degree m lie in the degree-m image. -/
theorem linearSystemFreeMap_le_formImage (hy : ∀ i, (y i).IsHomogeneous 1) (B : Finset (σ →₀ ℕ))
    (m : ℕ) : LinearMap.range (linearSystemFreeMap (P := P) y B m) ≤
      linearSystemFormImage (P := P) m := by
  rintro _ ⟨c, rfl⟩
  rw [linearSystemFreeMap_apply, ← linearSystemExtend_sum]
  exact ⟨_, linearSystemSum_isHomogeneous y hy (linearSystemExtend_mem c), rfl⟩

/-- Lower bound by the free part. -/
theorem linearSystem_freePart_le (hy : ∀ i, (y i).IsHomogeneous 1) {B : Finset (σ →₀ ℕ)}
    (hB : LinearSystemIndependent y P B) (m : ℕ) :
    ∑ b ∈ B, (if b.degree ≤ m then (m - b.degree + d).choose d else 0) ≤
      Module.finrank K (linearSystemFormImage (P := P) m) := by
  rw [← finrank_linearSystemFreeDomain (K := K) (d := d) B m]
  let f := (linearSystemFreeMap (P := P) y B m).codRestrict (linearSystemFormImage (P := P) m)
    (fun c => linearSystemFreeMap_le_formImage y hy B m ⟨c, rfl⟩)
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  intro c c' h
  exact linearSystemFreeMap_injective y hB m (congrArg Subtype.val h)

omit [Fintype σ] in
/-- Upper bound through the common denominator. -/
theorem linearSystem_formImage_le_freePart [P.IsPrime] {B : Finset (σ →₀ ℕ)}
    {δ : MvPolynomial (Fin (d + 1)) K} {k₀ : ℕ} (hδP : aeval y δ ∉ P)
    (hspan : ∀ e, ∀ f ∈ homogeneousSubmodule σ K e,
      LinearSystemSpanned y P B (e + k₀) (aeval y δ * f)) (m : ℕ) :
    Module.finrank K (linearSystemFormImage (P := P) m) ≤
      ∑ b ∈ B, (if b.degree ≤ m + k₀ then (m + k₀ - b.degree + d).choose d else 0) := by
  rw [← finrank_linearSystemFreeDomain (K := K) (d := d) B (m + k₀)]
  have hne : Ideal.Quotient.mk P (aeval y δ) ≠ 0 := fun h =>
    hδP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  let μ := LinearMap.mulLeft K (Ideal.Quotient.mk P (aeval y δ))
  have hμ : Function.Injective μ := mul_right_injective₀ hne
  have hle : (linearSystemFormImage (P := P) m).map μ ≤
      LinearMap.range (linearSystemFreeMap (P := P) y B (m + k₀)) := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    obtain ⟨c, hc, hcP⟩ := hspan m f hf
    refine ⟨fun b => ⟨c b.1, hc b.1 b.2⟩, ?_⟩
    rw [linearSystemFreeMap_apply]
    change _ = Ideal.Quotient.mk P (aeval y δ) * Ideal.Quotient.mk P f
    rw [← map_mul, eq_comm, Ideal.Quotient.eq]
    rw [← Finset.sum_attach B, ← Finset.univ_eq_attach] at hcP
    exact hcP
  calc Module.finrank K (linearSystemFormImage (P := P) m)
      = Module.finrank K ((linearSystemFormImage (P := P) m).map μ) :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective μ hμ _))
    _ ≤ Module.finrank K (LinearMap.range (linearSystemFreeMap (P := P) y B (m + k₀))) :=
        Submodule.finrank_mono hle
    _ ≤ _ := LinearMap.finrank_range_le _

end MixedFujita
