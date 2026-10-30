/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RoundupIntegerThresholdArithmetic
public import MixedFujita.NormalCartierEffectivity
public import MixedFujita.CrepantSNCLocalDescent
public import MixedFujita.CrepantBertiniPerturbationDescent
public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.NormalEffectiveCartierPrime

/-!
On a supplied actual SNC crepant model, effectivity of E-p*rho*G for the
actual round-up E=ceil(-B/d) is equivalent to all-model klt of D+d*p*G.
No joint SNC support of the perturbing divisor G is assumed. In the forward
direction effectivity itself forces p*rho*G to vanish outside the original
SNC boundary support. The distinguished rational section 1 gives the same
criterion in the actual Cartier section lattice.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- Actual effectivity of the round-up minus an integral pulled divisor is
exactly the all-model klt condition for the integral perturbation. -/
theorem snc_roundup_sub_integer_pullback_isEffective_iff_klt
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hG : G.IsEffective) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) (p : ℕ) :
    (E - p • cartierPullback ρ G).IsEffective ↔
      LogPairIsKlt c f d (D + (d * p) • G) := by
  have hcoef (t : CodimensionOnePoint T) :
      0 ≤ cartierCoefficient (E - p • cartierPullback ρ G) (t : T) ↔
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d
        (D + (d * p) • G) cT etaleCharts_cover) (t : T) < (d : ℤ) := by
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, hE t,
      crepantBoundaryCartier_add_source, cartierPullback_nsmul,
      cartierCoefficient_add, cartierCoefficient_nsmul]
    simpa only [Nat.cast_mul, mul_assoc] using boundary_roundup_sub_integer_nonneg_iff
      (cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T))
      ((p : ℤ) * cartierCoefficient (cartierPullback ρ G) (t : T)) d hd
  constructor
  · intro heff
    have hupper (t : CodimensionOnePoint T) :=
      (hcoef t).mp (cartierCoefficient_nonneg_of_isEffective _ heff (t : T))
    apply logPairIsKlt_of_crepant_snc_model ρ hρ c f d hd (D + (d * p) • G)
      cT ξ hinj hξ hsnc ?_ (fun i => hupper ⟨ξ i, hξ i⟩)
    intro t ht
    have hnon := cartierCoefficient_nonneg_of_isEffective _ heff (t : T)
    rw [cartierCoefficient_sub, cartierCoefficient_nsmul, hE t, hsupport t ht] at hnon
    simp only [Int.cast_zero, zero_div, neg_zero, Int.ceil_zero, zero_sub] at hnon
    have hGnon := cartierCoefficient_nonneg_of_isEffective _
      (cartierPullback_effective_of_effective ρ G hG) (t : T)
    have hz : (p : ℤ) * cartierCoefficient (cartierPullback ρ G) (t : T) = 0 :=
      le_antisymm (by omega) (mul_nonneg (Nat.cast_nonneg p) hGnon)
    rw [crepantBoundaryCartier_add_source, cartierPullback_nsmul,
      cartierCoefficient_add, cartierCoefficient_nsmul, hsupport t ht, zero_add,
      Nat.cast_mul, mul_assoc, hz, mul_zero]
  · intro hklt
    apply (normal_cartier_isEffective_iff_coefficients_nonneg hnormT _).mpr
    intro t
    exact (hcoef t).mpr (logPairIsKlt_crepantBoundary_coefficient_lt ρ hρ c f d
      (D + (d * p) • G) hklt cT t)

/-- The actual distinguished rational section 1 belongs to the twisted
round-up lattice exactly for the same integral klt perturbations. -/
theorem snc_roundup_integer_unit_section_iff_klt
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D G : CartierDivisor X) (hG : G.IsEffective) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover) (t : T) = 0)
    (E : CartierDivisor T)
    (hE : ∀ t : CodimensionOnePoint T, cartierCoefficient E (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉) (p : ℕ) :
    Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ⊤
      (1 : Γ(T, (⊤ : T.Opens))) ∈ (E - p • cartierPullback ρ G).sections ⊤ ↔
      LogPairIsKlt c f d (D + (d * p) • G) :=
  CartierDivisor.isEffective_iff_one_mem_sections.symm.trans
    (snc_roundup_sub_integer_pullback_isEffective_iff_klt ρ hρ hnormT c f d hd D G hG cT
      ξ hinj hξ hsnc hsupport E hE p)

end MixedFujita
