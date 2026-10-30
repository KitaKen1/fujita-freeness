/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierPulledMixedEulerProjection
public import SGA.Foundations.Cohomology.Devissage

/-! SGA支持帰納法による実混合Euler消滅の整閉支持への帰着。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Apply the proved SGA coherent-support devissage to the actual mixed
Euler vanishing property. Only its genuinely geometric integral-support
step remains an input; zero support and extensions are discharged here. -/
theorem cartierPulledModuleMixedEulerDifference_vanish_of_integral_step
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hint : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
      (∀ G : Z.Modules, G.IsCoherent → ∀ T : Set Z, IsClosed T → T ≠ Set.univ →
        CohomologyAux.VanishesOff G T →
          cartierPulledModuleMixedEulerDifference K p ((Scheme.Modules.pushforward i).obj G) D E = 0) →
      ∀ G : Z.Modules, G.IsCoherent →
        cartierPulledModuleMixedEulerDifference K p ((Scheme.Modules.pushforward i).obj G) D E = 0)
    (M : Y.Modules) [M.IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  refine CohomologyAux.prop_of_integral_step
    (fun N : Y.Modules => cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (fun N _ hN => cartierPulledModuleMixedEulerDifference_zero_sections K p N hN D E)
    ?_ hint M
  intro S hS h₁ h₂ h₃ hP₁ hP₃
  let := h₁
  let := h₂
  let := h₃
  have h := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E hS
  simpa only [hP₁, hP₃, add_zero] using h


/-- The geometric integral step can be stated on the actual integral
support itself, with the original ambient directions pulled there. -/
theorem cartierPulledModuleMixedEulerDifference_vanish_of_pulled_integral_step
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hint : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
      [IsProper (Z ↘ Spec (CommRingCat.of K))]
      (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))],
      (∀ G : Z.Modules, G.IsCoherent → ∀ T : Set Z, IsClosed T → T ≠ Set.univ →
        CohomologyAux.VanishesOff G T →
          cartierPulledModuleMixedEulerDifference K (i ≫ p) G D E = 0) →
      ∀ G : Z.Modules, G.IsCoherent →
        cartierPulledModuleMixedEulerDifference K (i ≫ p) G D E = 0)
    (M : Y.Modules) [M.IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  apply cartierPulledModuleMixedEulerDifference_vanish_of_integral_step K p D E ?_ M
  intro Z i _ _ hsmall G hG
  let : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := hG
  rw [cartierPulledModuleMixedEulerDifference_closed_pushforward K p i G D E]
  apply hint Z i ?_ G hG
  intro N hN T hT hTne hNT
  let := hN
  rw [← cartierPulledModuleMixedEulerDifference_closed_pushforward K p i N D E]
  exact hsmall N hN T hT hTne hNT

end MixedFujita
