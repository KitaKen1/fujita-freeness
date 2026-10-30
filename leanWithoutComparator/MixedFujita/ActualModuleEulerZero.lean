/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ActualModuleEulerCharacteristic

/-! 零恒等射から実コホモロジーと完全Euler標数の消滅。 See reports/check-220-coherent-mixed-euler-devissage.json for the verified scope. Positive-dimensional general mixed Euler nilpotence remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A zero identity implies genuinely zero cohomology and full Euler
characteristic, without a finrank junk-value argument. -/
theorem moduleEulerChar_eq_zero_of_id_eq_zero
    (K : Type u) [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
    (M : Y.Modules) (h : 𝟙 M = 0) :
    Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K)) M = 0 := by
  have hcoh (q : ℕ) : Subsingleton (M.H q) := ⟨fun x y => by
    have hz (z : M.H q) : z = 0 := by
      have he := congrArg (fun a => Scheme.Modules.H'.map a q ⊤ z) h
      simp only [Scheme.Modules.H'.map_id, Scheme.Modules.H'.map_zero] at he
      exact he
    rw [hz x, hz y]⟩
  have hrank (q : ℕ) : Scheme.Modules.finrankH (Y ↘ Spec (CommRingCat.of K)) M q = 0 :=
    Scheme.Modules.finrankH_eq_zero_of_subsingleton _ M q (hcoh q)
  simp only [Scheme.Modules.eulerChar_def, hrank, Int.natCast_zero, mul_zero, finsum_zero]

end MixedFujita
