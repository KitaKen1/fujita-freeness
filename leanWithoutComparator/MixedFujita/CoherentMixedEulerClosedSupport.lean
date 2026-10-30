/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerDevissage

/-! 実イデアル冪フィルトレーションによる閉支持Euler消滅の移送。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual SGA ideal-power filtration transfers mixed Euler vanishing from
all coherent modules on a closed source to all modules supported there. -/
theorem cartierPulledModuleMixedEulerDifference_vanish_of_closed_support
    (K : Type u) [Field K] {X Y Z : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (hZ : ∀ N : Z.Modules, N.IsCoherent →
      cartierPulledModuleMixedEulerDifference K (i ≫ p) N D E = 0)
    (M : Y.Modules) [M.IsCoherent] (hM : CohomologyAux.VanishesOff M (Set.range i)) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  refine CohomologyAux.prop_of_vanishesOff_range
    (fun N : Y.Modules => cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (fun N _ hN => cartierPulledModuleMixedEulerDifference_zero_sections K p N hN D E)
    ?_ i ?_ M hM
  · intro S hS h₁ h₂ h₃ hP₁ hP₃
    let := h₁
    let := h₂
    let := h₃
    have h := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E hS
    simpa only [hP₁, hP₃, add_zero] using h
  · intro N hN
    let := hN
    let : N.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    let : N.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
    let : ((Scheme.Modules.pullback i).obj N).IsCoherent := ⟨inferInstance, inferInstance⟩
    rw [cartierPulledModuleMixedEulerDifference_closed_pushforward]
    exact hZ _ inferInstance

end MixedFujita
