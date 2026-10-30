/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CrepantRoundupExceptionalDifference
public import MixedFujita.ExceptionalCartierProjectionFormula
public import MixedFujita.CartierNefPullback
public import MixedFujita.SNCRoundupRefinementLattice

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem effectiveCartier_unit_global_section_ne_zero
    {X : Scheme.{u}} [IsIntegral X] (E : CartierDivisor X) (hE : E.IsEffective) :
    Scheme.Modules.Hom.app (E.unitToSheaf hE) ⊤ (1 : Γ(X, ⊤)) ≠ 0 := by
  intro h
  have hr := effectiveCartierUnitToSheaf_rational E hE ⊤ (1 : Γ(X, ⊤))
  rw [h, map_zero, map_zero, map_one] at hr
  exact zero_ne_one hr

section Normalized
variable {K : Type u} [Field K] {n : ℕ} {X T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D E₀ : CartierDivisor X) (hE₀ : E₀.IsEffective)
  (heff : LogPairBoundaryEffective c f d (D + d • E₀))
  (hklt : LogPairIsKlt c f d (D + d • E₀))
  (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
  (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
    ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
      (t : T) : ℝ) / (d : ℝ))⌉)

/-- A genuine sheaf isomorphism across the actual proper crepant refinement;
source projectivity and a new SNC family are unnecessary. -/
noncomputable def normalizedCrepantRoundupPushforwardIso :
    E₀.sheaf ≅ (Scheme.Modules.pushforward ρ).obj E₁.sheaf := by
  let h := crepant_roundup_difference_effective_exceptional_unit_iso
    ρ hρ hnormX hnormT hcov c f d hd D E₀ heff hklt cT E₁ hE₁
  let hC := Classical.choose h
  have hEx := (Classical.choose_spec h).1
  let a := Classical.choice (cartierPullback_sheaf_iso_modulePullback ρ E₀
    (Scheme.Modules.Hom.app (E₀.unitToSheaf hE₀) ⊤ (1 : Γ(X, ⊤)))
    (effectiveCartier_unit_global_section_ne_zero E₀ hE₀))
  exact effectiveExceptionalCartierTwistedPushforwardIso hnormX hnormT ρ hρ
    (E₁ - cartierPullback ρ E₀) hC hEx E₀ ≪≫
    (Scheme.Modules.pushforward ρ).mapIso
      (tensorIso a (Iso.refl _) ≪≫
        cartierTensorSheafIso (cartierPullback ρ E₀) (E₁ - cartierPullback ρ E₀) ≪≫
        eqToIso (congrArg CartierDivisor.sheaf
          (show cartierPullback ρ E₀ + (E₁ - cartierPullback ρ E₀) = E₁ by abel)))

/-- Every module Cartier twist uses the same actual higher roundup. -/
noncomputable def normalizedCrepantRoundupTwistedPushforwardIso (A : CartierDivisor X) :
    A.sheaf ⊗ E₀.sheaf ≅ (Scheme.Modules.pushforward ρ).obj
      ((Scheme.Modules.pullback ρ).obj A.sheaf ⊗ E₁.sheaf) :=
  tensorIso (Iso.refl A.sheaf)
    (normalizedCrepantRoundupPushforwardIso ρ hρ hnormX hnormT hcov c f d hd D E₀ hE₀
      heff hklt cT E₁ hE₁) ≪≫ cartierProjectionFormulaIso A ρ E₁.sheaf

/-- Pushing the actual refinement isomorphism to an arbitrary base. -/
noncomputable def normalizedCrepantRoundupCompositePushforwardIso
    {B : Scheme.{u}} (q : X ⟶ B) :
    (Scheme.Modules.pushforward q).obj E₀.sheaf ≅
      (Scheme.Modules.pushforward (ρ ≫ q)).obj E₁.sheaf :=
  (Scheme.Modules.pushforward q).mapIso
    (normalizedCrepantRoundupPushforwardIso ρ hρ hnormX hnormT hcov c f d hd D E₀ hE₀
      heff hklt cT E₁ hE₁) ≪≫ (Scheme.Modules.pushforwardComp ρ q).app E₁.sheaf

/-- The commuting base square gives an actual pushforward comparison. This
does not assert that a pullback of the old direct image is the new direct image. -/
noncomputable def normalizedCrepantRoundupBaseSquarePushforwardIso
    {B B' : Scheme.{u}} (q : X ⟶ B) (q' : T ⟶ B') (β : B' ⟶ B)
    (hsquare : ρ ≫ q = q' ≫ β) :
    (Scheme.Modules.pushforward q).obj E₀.sheaf ≅
      (Scheme.Modules.pushforward β).obj ((Scheme.Modules.pushforward q').obj E₁.sheaf) :=
  normalizedCrepantRoundupCompositePushforwardIso ρ hρ hnormX hnormT hcov c f d hd D E₀ hE₀
    heff hklt cT E₁ hE₁ q ≪≫
    (Scheme.Modules.pushforwardCongr hsquare).app E₁.sheaf ≪≫
    ((Scheme.Modules.pushforwardComp q' β).app E₁.sheaf).symm

end Normalized

section TowerIso

variable {K : Type u} [Field K] {n : ℕ} {X S T : Scheme.{u}}
  [IsIntegral X] [IsIntegral S] [IsIntegral T] [IsNoetherian S] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [S.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (S ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (π : S ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
  (ρ : T ⟶ S) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

/-- The fixed SNC source gives the actual higher-roundup direct-image
isomorphism, with normalization supplied internally. -/
noncomputable def sncCrepantTowerRoundupPushforwardIso
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (cS : EtaleChart K S n) (cT : EtaleChart K T n)
    {r : ℕ} (ξ : Fin r → S) (hinj : Function.Injective ξ)
    (hξ : ∀ i, Order.coheight (ξ i) = 1) (hsnc : IsSNCFamily K n ξ)
    (hsupport : ∀ s : CodimensionOnePoint S, (s : S) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover) (s : S) = 0)
    (E₀ : CartierDivisor S) (heff : E₀.IsEffective)
    (hE₀ : ∀ s : CodimensionOnePoint S, cartierCoefficient E₀ (s : S) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier π hπ c f d D cS etaleCharts_cover)
        (s : S) : ℝ) / (d : ℝ))⌉)
    (E₁ : CartierDivisor T)
    (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier (ρ ≫ π)
        (dominantFunctionFieldAlgHom_comp_bijective π ρ hπ hρ) c f d D cT etaleCharts_cover)
        (t : T) : ℝ) / (d : ℝ))⌉)
    :
    E₀.sheaf ≅ (Scheme.Modules.pushforward ρ).obj E₁.sheaf := by
  letI : Smooth (S ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  letI : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormS : ∀ s : S, IsIntegrallyClosed (S.presheaf.stalk s) :=
    fun s => smooth_stalk_isIntegrallyClosed (K := K) s
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  have hcovS : CodimOneChartCovered n K S := by
    intro s _
    exact Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := S) (n := n)).symm ▸ Opens.mem_top s)
  obtain ⟨hEffN, hKltN⟩ := crepant_source_roundup_normalized_pair_effective_klt
    π hπ hnormS c f d hd D cS ξ hinj hξ hsnc hsupport E₀ heff hE₀
  have hE₁' : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
      ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ cS
        (crepantPullbackFormUnit π hπ c f cS) d (cartierPullback π D)
        cT etaleCharts_cover) (t : T) : ℝ) / (d : ℝ))⌉ := by
    intro t
    rw [hE₁ t, crepantBoundaryCartier_comp π ρ hπ hρ]
  exact normalizedCrepantRoundupPushforwardIso ρ hρ hnormS hnormT hcovS cS
    (crepantPullbackFormUnit π hπ c f cS) d hd (cartierPullback π D) E₀ heff
    hEffN hKltN cT E₁ hE₁'

end TowerIso

end MixedFujita

