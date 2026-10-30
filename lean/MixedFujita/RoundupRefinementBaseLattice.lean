/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCRoundupRefinementLattice
public import MixedFujita.CartierRationalUnitSections

/-!
Transport actual nearby base Cartier-unit and nonzero rational-function
sections through the normalized roundup comparison, retaining the actual
pullback square, rational multiplication and Cartier twists.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual distinguished rational unit is the function-field unit on a
nonempty open, under the actual rational-section equivalence. -/
theorem rationalFunctionsEquiv_symm_one_eq_toRationalFunctions
    {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) [Nonempty U] :
    (rationalFunctionsEquiv (X := X) U).symm (1 : X.functionField) =
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) U (1 : Γ(X, U)) := by
  apply (rationalFunctionsEquiv (X := X) U).injective
  rw [LinearEquiv.apply_symm_apply, Scheme.rationalFunctionsEquiv_toRationalFunctions_app,
    map_one]

variable {K : Type u} [Field K] {n : ℕ} {X T B : Scheme.{u}}
  [IsIntegral X] [IsIntegral T] [IsIntegral B]
  [IsLocallyNoetherian X] [IsNoetherian T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))] [hproper : IsProper ρ]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
  (hcov : CodimOneChartCovered n K X)
  (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
  (D E₀ : CartierDivisor X)
  (heff : LogPairBoundaryEffective c f d (D + d • E₀))
  (hklt : LogPairIsKlt c f d (D + d • E₀))
  (cT : EtaleChart K T n) (E₁ : CartierDivisor T)
  (hE₁ : ∀ t : CodimensionOnePoint T, cartierCoefficient E₁ (t : T) =
    ⌈-((cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
      (t : T) : ℝ) / (d : ℝ))⌉)
  (g : X ⟶ B) [IsDominant g] (η : B)

include hd hnormX hnormT hcov heff hklt hE₁ hproper

/-- Every actual nearby unit section with an arbitrary base Cartier twist
is preserved by the same normalized proper crepant refinement. -/
theorem normalized_roundup_base_neighborhood_unit_lattice_iff
    (L : CartierDivisor B) :
    (∃ U : B.Opens, η ∈ U ∧
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
        (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U)) ∈
          (E₁ + cartierPullback (ρ ≫ g) L).sections ((ρ ≫ g) ⁻¹ᵁ U)) ↔
    (∃ U : B.Opens, η ∈ U ∧
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) (g ⁻¹ᵁ U)
        (1 : Γ(X, g ⁻¹ᵁ U)) ∈ (E₀ + cartierPullback g L).sections (g ⁻¹ᵁ U)) := by
  apply exists_congr
  intro U
  apply and_congr_right
  intro hηU
  letI : Nonempty U := ⟨⟨η, hηU⟩⟩
  letI := dominant_preimage_nonempty g U
  letI := dominant_preimage_nonempty ρ (g ⁻¹ᵁ U)
  letI := dominant_preimage_nonempty (ρ ≫ g) U
  have h := normalized_roundup_cartier_twisted_mem_sections_iff ρ hρ hnormX hnormT hcov
    c f d hd D E₀ heff hklt cT E₁ hE₁ (cartierPullback g L) (g ⁻¹ᵁ U) 1
  simpa only [map_one, Scheme.Hom.comp_preimage, cartierPullback_comp,
    rationalFunctionsEquiv_symm_one_eq_toRationalFunctions] using h

/-- Actual nearby pulled rational-unit sections are preserved, with no sign
condition on the rational function's base order. -/
theorem normalized_roundup_base_neighborhood_rational_lattice_iff
    (u : B.functionFieldˣ) :
    (∃ U : B.Opens, η ∈ U ∧
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul T
        ((dominantFunctionFieldMap (ρ ≫ g)).hom (u : B.functionField))) ((ρ ≫ g) ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
          (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U))) ∈ E₁.sections ((ρ ≫ g) ⁻¹ᵁ U)) ↔
    (∃ U : B.Opens, η ∈ U ∧
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X
        ((dominantFunctionFieldMap g).hom (u : B.functionField))) (g ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) (g ⁻¹ᵁ U)
          (1 : Γ(X, g ⁻¹ᵁ U))) ∈ E₀.sections (g ⁻¹ᵁ U)) := by
  have hHigh (U : B.Opens) :
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul T
        ((dominantFunctionFieldMap (ρ ≫ g)).hom (u : B.functionField))) ((ρ ≫ g) ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
          (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U))) ∈ E₁.sections ((ρ ≫ g) ⁻¹ᵁ U) ↔
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions T) ((ρ ≫ g) ⁻¹ᵁ U)
        (1 : Γ(T, (ρ ≫ g) ⁻¹ᵁ U)) ∈
          (E₁ + cartierPullback (ρ ≫ g) (principalCartierDivisor B u)).sections
            ((ρ ≫ g) ⁻¹ᵁ U) := by
    rw [cartierPullback_principal]
    exact cartier_rational_unit_mem_sections_iff_unit_of_add_principal E₁
      (Units.map (dominantFunctionFieldMap (ρ ≫ g)).hom.toMonoidHom u) _
  have hLow (U : B.Opens) :
      Scheme.Modules.Hom.app (Scheme.rationalFunctionsMul X
        ((dominantFunctionFieldMap g).hom (u : B.functionField))) (g ⁻¹ᵁ U)
        (Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) (g ⁻¹ᵁ U)
          (1 : Γ(X, g ⁻¹ᵁ U))) ∈ E₀.sections (g ⁻¹ᵁ U) ↔
      Scheme.Modules.Hom.app (Scheme.toRationalFunctions X) (g ⁻¹ᵁ U)
        (1 : Γ(X, g ⁻¹ᵁ U)) ∈
          (E₀ + cartierPullback g (principalCartierDivisor B u)).sections (g ⁻¹ᵁ U) := by
    rw [cartierPullback_principal]
    exact cartier_rational_unit_mem_sections_iff_unit_of_add_principal E₀
      (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom u) _
  refine Iff.trans ?_
    ((normalized_roundup_base_neighborhood_unit_lattice_iff ρ hρ hnormX hnormT hcov c f d hd
      D E₀ heff hklt cT E₁ hE₁ g η (principalCartierDivisor B u)).trans ?_)
  · exact exists_congr (fun U => and_congr_right (fun _ => hHigh U))
  · symm
    exact exists_congr (fun U => and_congr_right (fun _ => hLow U))

end MixedFujita
