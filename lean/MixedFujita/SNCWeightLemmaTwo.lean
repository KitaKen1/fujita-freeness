/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightLowSubspace
public import MixedFujita.SNCWeightLemmaOne
public import MixedFujita.CartierGradedSections
public import MixedFujita.CartierSectionNonvanishingOpen

/-!
Lemma 2 for prime divisors and the bound (8) for the weights of simple normal crossing models
(step 11, sections 1.2 and 3.1 of the manuscript), for a smooth variety with zero boundary and an
ample divisor A.

* Products. Along a prime divisor e of the source of a dominant morphism σ, multiplying a section
  t of q A by a section σ₀ of a A which does not vanish at σ(e) does not change the coefficient of
  the pullback of the zero divisor.
* Lemma 2 for prime divisors. With the constant c of Lemma 1: if σ₀ does not vanish at a point x,
  every nonzero section s = σ₀ t of (a + q) A satisfies ord_e(σ* div s) ≤ c q (1 + ord_e(K_{U/Y}))
  for every prime divisor e of every smooth birational model whose centre contains x. The bound
  is c q, not c (a + q): this is the subspace U = σ₀ Γ(q A) of Lemma 2, of dimension h⁰(q A). The
  closed point at which Lemma 1 measures the multiplicity is not x, so the factor σ₀ is removed
  along e itself, where it is a unit.
* The bound (8). Hence for every basis of the sections of (a + q) A, every simple normal crossing
  model of the variety with zero boundary and of the zero divisors of the basis, all t, j > 0 and
  every weight w ≥ 0 over the fibre of x,

    F(w) ≥ h⁰(q A) · exp(A(w) (1/t − c q/j)).
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

section Product

variable {Y U : Scheme.{u}} [IsIntegral Y] [IsIntegral U] [IsLocallyNoetherian U]
  (σ : U ⟶ Y) [IsDominant σ]

/-- Multiplying by a section which does not vanish at the image of a prime divisor does not change
the coefficient along the prime divisor of the pullback of the zero divisor. -/
theorem cartierPullback_nsmulProduct_coefficient_eq (A : CartierDivisor Y) (a q : ℕ)
    (σ₀ : Γ((a • A).sheaf, ⊤)) (t : Γ((q • A).sheaf, ⊤)) (ht : t ≠ 0)
    (hst : cartierNsmulProduct A a q σ₀ t ≠ 0) (e : CodimensionOnePoint U)
    [IsDiscreteValuationRing (U.presheaf.stalk (e : U))]
    (hσ₀ : σ (e : U) ∈ cartierSectionNonvanishingOpen (a • A) σ₀) :
    cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor ((a + q) • A)
        (cartierNsmulProduct A a q σ₀ t) hst)) (e : U) =
      cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor (q • A) t ht)) (e : U) := by
  obtain ⟨f, hf⟩ := A.exists_isLocalEquationAt (σ (e : U))
  have hu : IsUnit (cartierLocalCoefficient (a • A) (σ (e : U)) (f ^ a)
      (cartierLocalEquation_pow A (σ (e : U)) f hf a) σ₀) :=
    (mem_cartierSectionNonvanishingOpen_iff_localCoefficient (a • A) σ₀ (σ (e : U)) (f ^ a)
      (cartierLocalEquation_pow A (σ (e : U)) f hf a)).mp hσ₀
  obtain ⟨k₁, hk₁, hc₁⟩ := cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder σ
    ((a + q) • A) (cartierNsmulProduct A a q σ₀ t) hst e
  obtain ⟨k₂, hk₂, hc₂⟩ := cartierPullback_sectionZeroDivisor_coefficient_eq_stalkPullbackOrder σ
    (q • A) t ht e
  have hord : cartierStalkPullbackOrder ((a + q) • A) σ (e : U) (cartierNsmulProduct A a q σ₀ t) =
      cartierStalkPullbackOrder (q • A) σ (e : U) t := by
    rw [cartierStalkPullbackOrder_eq_localCoefficient ((a + q) • A) σ (e : U) (f ^ (a + q))
        (cartierLocalEquation_pow A (σ (e : U)) f hf (a + q)),
      cartierStalkPullbackOrder_eq_localCoefficient (q • A) σ (e : U) (f ^ q)
        (cartierLocalEquation_pow A (σ (e : U)) f hf q),
      cartierStalkPullbackCoefficient_apply, cartierStalkPullbackCoefficient_apply,
      cartierNsmulProduct_localCoefficient A a q (σ (e : U)) f hf σ₀ t, map_mul]
    exact localAdicOrder_unit_mul (hu.map (σ.stalkMap (e : U)).hom).unit _
  rw [hc₁, hc₂]
  have h : (k₁ : ℕ∞) = (k₂ : ℕ∞) := by rw [← hk₁, ← hk₂, hord]
  exact_mod_cast h

end Product

section LemmaTwo

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- Lemma 2 for prime divisors: with the constant of Lemma 1, the products σ₀ t of a section σ₀ of
a A not vanishing at x with the sections t of q A have ord_e(σ* div(σ₀ t)) ≤ c q (1 + ord_e K_{U/Y})
along every prime divisor e of a smooth birational model whose centre contains x. -/
theorem cartierIsAmpleProj_prime_coefficient_le_of_product {d : ℕ}
    (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {A : CartierDivisor Y}
    (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (x : Y) (a q : ℕ), 1 ≤ q → ∀ σ₀ : Γ((a • A).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ →
      ∀ (U : Scheme.{u}) [IsIntegral U] [IsLocallyNoetherian U]
        [U.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K))]
        (σ : U ⟶ Y) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
        (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
        (c₀ : EtaleChart K Y n) (cU₀ : EtaleChart K U n) (e : CodimensionOnePoint U),
        x ∈ closure ({σ (e : U)} : Set Y) →
        ∀ s ∈ LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀), ∀ hs : s ≠ 0,
          cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor ((a + q) • A) s hs))
              (e : U) ≤
            ((c * q : ℕ) : ℤ) * (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ
              c₀ etaleCharts_cover cU₀ etaleCharts_cover) (e : U)) := by
  obtain ⟨c, hc1, hc⟩ := cartierIsAmpleProj_prime_coefficient_le (K := K) (n := n) hn hd hA
  refine ⟨c, hc1, fun x a q hq σ₀ hx U _ _ _ _ σ _ _ hσ c₀ cU₀ e hcl s hsU hs => ?_⟩
  obtain ⟨t, rfl⟩ := hsU
  have ht : t ≠ 0 := by
    rintro rfl
    exact hs (map_zero _)
  have hsm : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hdvr := smoothOverField_codimensionOne_stalk_DVR (K := K) e
  have hσ₀ : σ (e : U) ∈ cartierSectionNonvanishingOpen (a • A) σ₀ :=
    (specializes_iff_mem_closure.mpr hcl).mem_open
      (cartierSectionNonvanishingOpen (a • A) σ₀).isOpen hx
  have heq := cartierPullback_nsmulProduct_coefficient_eq σ A a q σ₀ t ht hs e hσ₀
  exact heq.le.trans (hc U σ hσ c₀ cU₀ e q hq t ht)

/-- The bound (8) for the weights: with the constant of Lemma 1, for a section σ₀ of a A not
vanishing at x, every basis of the sections of (a + q) A, every simple normal crossing model of the
smooth variety with zero boundary and of the zero divisors of the basis, all t, j > 0 and every
weight w ≥ 0 over the fibre of x: F(w) ≥ h⁰(q A) exp(A(w) (1/t − c q/j)). -/
theorem cartierIsAmpleProj_weightExponentialObjective_ge {d : ℕ}
    (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {A : CartierDivisor Y}
    (hA : CartierIsAmpleProj K A) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ (x : Y) (a q : ℕ), 1 ≤ q → ∀ σ₀ : Γ((a • A).sheaf, ⊤),
      x ∈ cartierSectionNonvanishingOpen (a • A) σ₀ →
      ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
        [X.Over (Spec (CommRingCat.of K))]
        [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
        (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
        (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
        (cY : EtaleChart K Y n) (cX : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X),
        Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) → IsSNCFamily K n ξ →
        (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            cX etaleCharts_cover) (z : X) = 0) →
        ∀ {N : ℕ} (B : Module.Basis (Fin N) K Γ(((a + q) • A).sheaf, ⊤)),
        (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
          cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor ((a + q) • A) (B i) (B.ne_zero i))) (z : X) = 0) →
        ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
        (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        ∀ {t j : ℝ}, 0 < j →
          (Module.finrank K Γ((q • A).sheaf, ⊤) : ℝ) *
              Real.exp ((∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient
                (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
                  (1 • (smoothCanonicalDivisor cY +
                    principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover)
                  (ξ k)) / ((1 : ℕ) : ℝ))) * (1 / t - ((c * q : ℕ) : ℝ) / j)) ≤
            weightExponentialObjective
              (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
                (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
                  principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover)
                (ξ k)) / ((1 : ℕ) : ℝ))
              (fun i k => (cartierCoefficient (cartierPullback π
                (cartierSectionZeroDivisor ((a + q) • A) (B i) (B.ne_zero i))) (ξ k) : ℝ))
              t j w := by
  obtain ⟨c, hc1, hc⟩ := cartierIsAmpleProj_prime_coefficient_le_of_product (K := K) (n := n) hn
    hd hA
  refine ⟨c, hc1, fun x a q hq σ₀ hx X _ _ _ _ π _ _ hπ cY cX r ξ hinj hξ hsnc hBsupp N B hGsupp
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
  refine weightExponentialObjective_ge_of_low_subspace π hπ cY (1 : Y.functionFieldˣ) 1 le_rfl
    (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX ξ hinj
    hξ hsnc hBsupp ((a + q) • A) B hGsupp x
    (LinearMap.range (cartierNsmulProductLinear (K := K) A a q σ₀)) (θ := ((c * q : ℕ) : ℝ))
    (fun U' _ _ _ _ σ _ _ hσ cU e hcl s hsU hs => ?_) w hw0 hwΦ hj
  have hle := hc x a q hq σ₀ hx U' σ hσ cY cU e hcl s hsU hs
  have hle' : (cartierCoefficient (cartierPullback σ
      (cartierSectionZeroDivisor ((a + q) • A) s hs)) (e : U') : ℝ) ≤
      ((c * q : ℕ) : ℝ) * (1 + (cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ cY
        etaleCharts_cover cU etaleCharts_cover) (e : U') : ℝ)) := by
    exact_mod_cast hle
  rw [logDiscrepancyDivisor_boundary_zero σ hσ cY (1 : Y.functionFieldˣ) 1 cU, one_nsmul]
  simpa using hle'

end LemmaTwo

end MixedFujita
