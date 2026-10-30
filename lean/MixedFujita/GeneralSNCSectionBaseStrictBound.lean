/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupSNCFormalRestrictionData
public import MixedFujita.SNCFixedPartCompletedBound
public import MixedFujita.FormalDivisorThresholdBound
public import MixedFujita.ExceptionalCentreClassification

/-! Strict adjunction for every other SNC member meeting the marked
point-blow-up divisor, in arbitrary dimension. All formal-map, Jacobian
and fixed-part order data are constructed from the actual model and its
Cartier stalk ideals. The only threshold input is the original supplied
leading-form condition. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K] {n : ℕ}
  {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [IsLocallyNoetherian X] [IsLocallyNoetherian T]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

set_option maxHeartbeats 2200000 in
theorem pointBlowup_snc_fixedPart_strict_coefficient {J : Type*} [Finite J]
    (hn : topologicalKrullDim X = n) (x : X) (hx : IsClosed ({x} : Set X))
    (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (c₀ : EtaleChart K X n) (cT₀ : EtaleChart K T n)
    (g : T ⟶ (pointClosureIdeal x).blowUp) (hg : g ≫ (pointClosureIdeal x).blowUpπ = ρ)
    {r : ℕ} (ξ : Fin r → T) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (e : Fin r) (hρe : ρ (ξ e) = x)
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hEI : effectiveCartierIdealSheaf E hE = (pointClosureIdeal x).comap ρ)
    (hE0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient E (t : T) = 0)
    (hEe : cartierCoefficient E (ξ e) = 1)
    (hD0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
      cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
        cT₀ etaleCharts_cover) (t : T) = 0)
    (hDe : cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
      cT₀ etaleCharts_cover) (ξ e) = (n : ℤ) - 1)
    (D : CartierDivisor X) (s : J → Γ(D.sheaf, ⊤)) (hs : ∀ j, s j ≠ 0)
    (G : CartierDivisor T) (hG : G.IsEffective)
    (hGI : effectiveCartierIdealSheaf G hG = (cartierSectionBaseIdeal D s hs).comap ρ)
    (hG0 : ∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ → cartierCoefficient G (t : T) = 0)
    (h : ℕ) (hGe : cartierCoefficient G (ξ e) = ((n * h : ℕ) : ℤ))
    (fD : X.functionFieldˣ) (hfD : D.IsLocalEquationAt x fD)
    (sourceCompletion : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (horders : ∀ j, ((n * h : ℕ) : ℕ∞) ≤ cartierSectionVanishingOrder D x (s j))
    (hthreshold : ProjectiveThresholdCondition (fun j => homogeneousTaylorForm (n * h)
      (cartierTaylorCoordinates D x fD hfD sourceCompletion (s j))) h)
    (t : Fin r) (hte : t ≠ e)
    (hmeet : (closure ({ξ t} : Set T) ∩ closure ({ξ e} : Set T)).Nonempty) :
    cartierCoefficient G (ξ t) < (h : ℤ) *
      (1 + cartierCoefficient (birationalRelativeCanonicalDivisor n ρ hρ c₀ etaleCharts_cover
        cT₀ etaleCharts_cover) (ξ t)) := by
  classical
  let : Smooth (T ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  subst ρ
  let I := pointClosureIdeal x
  let π := I.blowUpπ
  let : I.blowUp.Over (Spec (.of K)) := ⟨π ≫ (X ↘ Spec (.of K))⟩
  have : π.IsOver (Spec (.of K)) := ⟨rfl⟩
  have : g.IsOver (Spec (.of K)) := ⟨by
    change g ≫ (π ≫ (X ↘ Spec (.of K))) = T ↘ Spec (.of K)
    rw [← Category.assoc]
    exact HomIsOver.comp_over (f := g ≫ π) (S := Spec (.of K))⟩
  obtain ⟨P, hP, heP, htP⟩ := exists_closed_common_specialization (K := K)
    (by simpa only [Set.inter_comm] using hmeet)
  obtain ⟨cX, hxcX, k, τ, β, c, σ, hPc, completion, hτ, hβ, hI, hcoord,
      hc, he, hmem, hTaylor, horder, hJ, hcoef, hJ0, hJord, v, hv, hψv, hv0, hvord, hsections⟩ :=
    exists_pointBlowup_snc_formal_map_with_jacobian_orders hn x hx (g ≫ π) hρ c₀ cT₀ g rfl ξ hinj hξ hsnc
      e hρe E hE hEI hE0 hEe hD0 hDe P hP (specializes_iff_mem_closure.mp heP) sourceCompletion
  obtain ⟨l, hl⟩ := (hmem t).mp (specializes_iff_mem_closure.mp htP)
  have hlk : l ≠ k := by
    intro hlk
    exact hte (hc.1 t e k (by rw [← hlk]; exact hl) he)
  have hq : π (g P) = x := by
    have hm := specializes_iff_mem_closure.mp (heP.map (g ≫ π).continuous)
    rw [hρe, hx.closure_eq] at hm
    exact hm
  let Taylor := stalkTaylorExpansion P completion
  let ψ := centeredPolynomialFormalMap (Taylor.comp (β.comp τ))
  let m := n * h
  let w : {i : Fin n // i ≠ k} → ℕ := Pi.single ⟨l, hlk⟩ 1
  let b := (cartierCoefficient E (ξ t)).toNat
  let d := (cartierCoefficient (birationalRelativeCanonicalDivisor n (g ≫ π) hρ c₀ etaleCharts_cover
    cT₀ etaleCharts_cover) (ξ t) - ((n - 1 : ℕ) : ℤ) * cartierCoefficient E (ξ t)).toNat
  let μ := (cartierCoefficient G (ξ t)).toNat
  choose z hfactor hres using (fun j => hsections hq D fD hfD (s j) m (horders j))
  let f : J → MvPowerSeries (Fin n) K := fun j => Taylor (β (z j))
  obtain ⟨UG, hPUG, hne, aG, haG, hEqG⟩ := exists_affineOpen_regularEquation_of_isEffective G hG P
  let fG := regularEquationRationalUnit T UG.1 aG haG
  have hfG : G.IsLocalEquationAt P fG := CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hEqG hPUG
  let a := T.presheaf.germ UG.1 P hPUG aG
  have ha : algebraMap (T.presheaf.stalk P) T.functionField a = (fG : T.functionField) := by
    rw [regularEquationRationalUnit_val]
    exact T.algebraMap_germ_eq_germToFunctionField hPUG aG
  have hfP : D.IsLocalEquationAt ((g ≫ π) P) fD := hq.symm ▸ hfD
  have hfixed (j : J) : (μ : ℕ∞) ≤ ((n * h * b : ℕ) : ℕ∞) +
      (powerSeriesDivisorRestriction k (f j)).weightedOrder w := by
    have hcoeff : cartierStalkPullbackCoefficient D (g ≫ π) P fD hfP (s j) =
        β (stalkMapAtEq π (g P) x hq (cartierLocalCoefficient D x fD hfD (s j))) := by
      rw [actual_stalkMap_comp_at_eq π g P β hβ x hq,
        stalkMapAtEq_cartier_coefficient (g ≫ π) P x hq D fD hfD]
    have hfact : Taylor (cartierStalkPullbackCoefficient D (g ≫ π) P fD hfP (s j)) =
        (MvPowerSeries.X k * v) ^ m * f j := by
      rw [hcoeff, hfactor j]
      simp only [map_mul, map_pow]
      rw [hv]
    have hbound := snc_fixedPart_completed_section_order_bound G hG c ξ hinj hξ σ hc hG0 P hPc
      fG hfG a ha _ (cartierStalkPullbackCoefficient_mem_fixedPart (g ≫ π) D s hs G hG hGI P fD hfP j)
        Taylor hTaylor e k he m hGe v (f j) hfact t l hlk hl
    rw [hvord t l hlk hl] at hbound
    simpa only [μ, m, b, Nat.cast_mul] using hbound
  have hnat : μ < h * (1 + d + (n - 1) * b) :=
    projectiveThreshold_divisor_fixed_coefficient_lt ψ k v hψv hJ0
      (fun i => MvPowerSeries.constantCoeff (Taylor (β (τ (MvPolynomial.X i.val))))) f
      (fun j => homogeneousTaylorForm m (cartierTaylorCoordinates D x fD hfD sourceCompletion (s j)))
        h hthreshold hres w (by simp [w]) b d μ (hvord t l hlk hl) (hJord t l hlk hl) hfixed
  have hEn : 0 ≤ cartierCoefficient E (ξ t) := cartierCoefficient_nonneg_of_isEffective E hE _
  have hGn : 0 ≤ cartierCoefficient G (ξ t) := cartierCoefficient_nonneg_of_isEffective G hG _
  have hdiff : 0 ≤ cartierCoefficient (birationalRelativeCanonicalDivisor n (g ≫ π) hρ c₀ etaleCharts_cover
      cT₀ etaleCharts_cover) (ξ t) - ((n - 1 : ℕ) : ℤ) * cartierCoefficient E (ξ t) :=
    sub_nonneg.mpr (hcoef t l hl)
  have hz := Int.ofNat_lt.mpr hnat
  dsimp only [μ, d, b] at hz
  push_cast at hz
  rw [Int.toNat_of_nonneg hGn, Int.toNat_of_nonneg hdiff, Int.toNat_of_nonneg hEn] at hz
  convert hz using 1 <;> ring

end MixedFujita
