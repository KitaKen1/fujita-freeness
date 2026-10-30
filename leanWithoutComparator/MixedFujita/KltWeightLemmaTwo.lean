/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltModelCoefficientBound
public import MixedFujita.SNCWeightLemmaTwo

/-!
Lemma 2 and the subspace form of (8) for projective klt pairs (section 3.1, step 15).

Multiplication by a section of a A nonvanishing at x preserves the valuation at every test prime
whose centre contains x. Lemma 1 therefore bounds the product subspace by C q A_(Y,B)(E),
independently of a. The existing extraction and subspace-counting theorem then gives (8) for
all nonnegative real weights on every SNC model. The source need not be smooth.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]

/-- Lemma 2 at actual test primes: the constant is multiplied by q, the degree of the second
factor, rather than the total degree a + q. -/
theorem klt_prime_coefficient_le_of_product (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (x : Y) (a q : ℕ), 1 ≤ q → ∀ σ₀ : Γ((a • A).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ →
      ∀ (U : Scheme.{u}) [IsIntegral U] [IsLocallyNoetherian U]
        [U.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
        (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
        (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
        (cU : EtaleChart K U n) (e : CodimensionOnePoint U),
        x ∈ closure ({σ (e : U)} : Set Y) →
        ∀ s ∈ LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀), ∀ hs : s ≠ 0,
          (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor ((a + q) • A) s hs))
            (e : U) : ℝ) ≤ ((C * q : ℕ) : ℝ) *
              (((d : ℝ) + cartierCoefficient
                (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) := by
  obtain ⟨C, hC, hc⟩ := klt_model_coefficient_le hn cY fY d hd D₀ A hklt hA
  refine ⟨C, hC, fun x a q hq σ₀ hx U _ _ _ _ σ _ _ hσ cU e hcl s hsU hs => ?_⟩
  obtain ⟨t, rfl⟩ := hsU
  have ht : t ≠ 0 := by
    rintro rfl
    exact hs (map_zero _)
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) e
  have hσ₀ : σ (e : U) ∈ cartierSectionNonvanishingOpen (a • A) σ₀ :=
    (specializes_iff_mem_closure.mpr hcl).mem_open
      (cartierSectionNonvanishingOpen (a • A) σ₀).isOpen hx
  have heq := cartierPullback_nsmulProduct_coefficient_eq σ A a q σ₀ t ht hs e hσ₀
  apply (congrArg (fun z : ℤ => (z : ℝ)) heq).le.trans
  simpa only [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg,
    Int.cast_neg, sub_neg_eq_add, Nat.cast_mul] using (hc U σ hσ cU e q hq t ht).2

/-- The klt form of (8) before choosing q: the objective is at least
h⁰(q A) exp(A(w) (1/t − C q/j)). -/
theorem klt_weightExponentialObjective_ge (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ A : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀) (hA : CartierIsAmpleProj K A) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ (x : Y) (a q : ℕ), 1 ≤ q → ∀ σ₀ : Γ((a • A).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ →
      ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
        [X.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
        (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
        (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
        (cX : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X),
        Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K n ξ →
        (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
            (z : X) = 0) →
        ∀ {N : ℕ} (B : Module.Basis (Fin N) K Γ(((a + q) • A).sheaf, ⊤)),
        (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor ((a + q) • A) (B i) (B.ne_zero i))) (z : X) = 0) →
        ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
        (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        ∀ {t j : ℝ}, 0 < j →
          (Module.finrank K Γ((q • A).sheaf, ⊤) : ℝ) *
            Real.exp ((∑ k, w k * (((d : ℝ) - cartierCoefficient
              (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)) *
              (1 / t - ((C * q : ℕ) : ℝ) / j)) ≤
            weightExponentialObjective
              (fun k => ((d : ℝ) - cartierCoefficient
                (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
              (fun i k => (cartierCoefficient (cartierPullback π
                (cartierSectionZeroDivisor ((a + q) • A) (B i) (B.ne_zero i))) (ξ k) : ℝ)) t j w := by
  obtain ⟨C, hC, hc⟩ := klt_prime_coefficient_le_of_product hn cY fY d hd D₀ A hklt hA
  refine ⟨C, hC, fun x a q hq σ₀ hx X _ _ _ _ π _ _ hπ cX r ξ hinj hξ hsnc hBsupp N B hGsupp
    w hw0 hwΦ t j hj => ?_⟩
  have hσ₀0 : σ₀ ≠ 0 := by
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen (a • A) 0 x).mp hx
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  have hrank : Module.finrank K (LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀)) =
      Module.finrank K Γ((q • A).sheaf, ⊤) :=
    LinearMap.finrank_range_of_inj (cartierNsmulProduct_injective A a q σ₀ hσ₀0)
  rw [← hrank]
  exact weightExponentialObjective_ge_of_low_subspace π hπ cY fY d hd D₀ cX ξ hinj hξ hsnc
    hBsupp ((a + q) • A) B hGsupp x
    (LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀))
    (fun U _ _ _ _ σ _ _ hσ cU e hcl s hsU hs => hc x a q hq σ₀ hx U σ hσ cU e hcl s hsU hs)
    w hw0 hwΦ hj

end MixedFujita
