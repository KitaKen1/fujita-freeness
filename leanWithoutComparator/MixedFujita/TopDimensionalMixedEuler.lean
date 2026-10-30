/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperMixedEulerNilpotence

/-! 元Cartier最高次Euler係数の基底捻り非依存性と全因子加法性。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The original Cartier mixed Euler characteristic vanishes above the
ordinary geometric dimension, without a supplied nilpotence premise. -/
theorem proper_cartierMixedEulerDifference_vanish_of_length
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X) :
    cartierMixedEulerDifference K D E = 0 := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsCoherent := invertible_module_isCoherent (X := X) O
  rw [← cartierPulledModuleMixedEulerDifference_id_unit]
  exact proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hdim (𝟙 X)
    (SheafOfModules.unit X.ringCatSheaf) D hlen E


/-- Top-dimensional mixed Euler coefficients are independent of the base
twist, for arbitrary coherent coefficients on arbitrary proper sources. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_base_independent
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (p : Y ⟶ X)
    (M : Y.Modules) [M.IsCoherent] (D : List (CartierDivisor X))
    (hlen : D.length = n) (E F : CartierDivisor X) :
    cartierPulledModuleMixedEulerDifference K p M D E =
      cartierPulledModuleMixedEulerDifference K p M D F := by
  have hvan := proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hdim p M
    ((F - E) :: D) (by simp only [List.length_cons, hlen]; omega) E
  change cartierPulledModuleMixedEulerDifference K p M D (E + (F - E)) -
    cartierPulledModuleMixedEulerDifference K p M D E = 0 at hvan
  have hshift : E + (F - E) = F := by abel
  rw [hshift] at hvan
  exact (sub_eq_zero.mp hvan).symm


/-- Original top-dimensional Cartier mixed Euler coefficients are
independent of the original base divisor, with no extra vanishing input. -/
theorem proper_cartierMixedEulerDifference_top_base_independent
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (D : List (CartierDivisor X)) (hlen : D.length = n) (E F : CartierDivisor X) :
    cartierMixedEulerDifference K D E = cartierMixedEulerDifference K D F := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let : O.IsCoherent := invertible_module_isCoherent (X := X) O
  rw [← cartierPulledModuleMixedEulerDifference_id_unit K D E,
    ← cartierPulledModuleMixedEulerDifference_id_unit K D F]
  exact proper_cartierPulledModuleMixedEulerDifference_top_base_independent K n hdim (𝟙 X)
    (SheafOfModules.unit X.ringCatSheaf) D hlen E F


/-- The additivity defect of a top-dimensional coefficient is geometrically
zero. Symmetry transports this additivity to any chosen factor. -/
theorem proper_cartierMixedEulerDifference_top_add_first
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (D : List (CartierDivisor X)) (hlen : D.length + 1 = n)
    (H J E : CartierDivisor X) :
    cartierMixedEulerDifference K ((H + J) :: D) E =
      cartierMixedEulerDifference K (H :: D) E + cartierMixedEulerDifference K (J :: D) E := by
  apply cartierMixedEulerDifference_add_of_next_vanishing
  exact proper_cartierMixedEulerDifference_vanish_of_length K n hdim (H :: J :: D)
    (by simp only [List.length_cons]; omega) E


/-- Top-dimensional mixed Cartier Euler coefficients are additive in any
specified factor, not just in a preferred ordering of the directions. -/
theorem proper_cartierMixedEulerDifference_top_add_factor
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n)
    (A B : List (CartierDivisor X)) (hlen : A.length + B.length + 1 = n)
    (H J E : CartierDivisor X) :
    cartierMixedEulerDifference K (A ++ (H + J) :: B) E =
      cartierMixedEulerDifference K (A ++ H :: B) E +
        cartierMixedEulerDifference K (A ++ J :: B) E := by
  have perm (L : CartierDivisor X) : (A ++ L :: B).Perm (L :: (A ++ B)) :=
    List.perm_append_comm.trans (List.perm_append_comm.cons L)
  rw [cartierMixedEulerDifference_perm K (perm (H + J)) E,
    cartierMixedEulerDifference_perm K (perm H) E,
    cartierMixedEulerDifference_perm K (perm J) E]
  exact proper_cartierMixedEulerDifference_top_add_first K n hdim (A ++ B)
    (by simpa only [List.length_append] using hlen) H J E

end MixedFujita
