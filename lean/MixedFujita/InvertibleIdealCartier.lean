/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EffectiveCartierIdealSheaf
public import Hironaka.Scheme.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
An invertible ideal in the resolution library defines an actual effective Cartier divisor.
On a separated integral scheme, two affine opens have affine intersection. The generators of
the ideal on that intersection differ by a unit, so their regular equations glue. The negative
Cartier sheaf has exactly the original ideal as its image, including multiplicities.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]

/-- Two affine local generators of the same ideal differ by a unit on their intersection. -/
theorem ideal_local_generators_transition (I : X.IdealSheafData)
    (U V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : I.ideal U = Ideal.span {f}) (hg : I.ideal V = Ideal.span {g}) :
    ∃ w : Γ(X, U.1 ⊓ V.1)ˣ,
      X.presheaf.map (homOfLE inf_le_left).op f =
        (w : Γ(X, U.1 ⊓ V.1)) * X.presheaf.map (homOfLE inf_le_right).op g := by
  have : Nonempty (U.1 ⊓ V.1 : X.Opens) := integral_opens_inter_nonempty X _ _
  let W : X.affineOpens := ⟨U.1 ⊓ V.1, U.2.inf V.2⟩
  have hspan : Ideal.span {X.presheaf.map (homOfLE inf_le_right).op g} =
      Ideal.span {X.presheaf.map (homOfLE inf_le_left).op f} := by
    have hWU : W ≤ U := by change U.1 ⊓ V.1 ≤ U.1; exact inf_le_left
    have hWV : W ≤ V := by change U.1 ⊓ V.1 ≤ V.1; exact inf_le_right
    have hU := I.map_ideal hWU
    have hV := I.map_ideal hWV
    rw [hf, Ideal.map_span, Set.image_singleton] at hU
    rw [hg, Ideal.map_span, Set.image_singleton] at hV
    exact hV.trans hU.symm
  obtain ⟨w, hw⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  exact ⟨w, by simpa only [mul_comm] using hw.symm⟩

/-- The original invertible ideal is the ideal of an actual effective Cartier divisor. -/
theorem exists_effectiveCartier_of_invertibleIdeal (I : X.IdealSheafData)
    (hI : I.IsInvertible) :
    ∃ (D : CartierDivisor X) (hD : D.IsEffective), effectiveCartierIdealSheaf D hD = I := by
  classical
  choose U hx f hf hIf using hI
  let (x : X) : Nonempty (U x).1 := ⟨⟨x, hx x⟩⟩
  have hf0 : ∀ x, f x ≠ 0 := fun x => (mem_nonZeroDivisors_iff_ne_zero.mp (hf x))
  have hcover : ⨆ x : X, (U x).1 = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  obtain ⟨D, ⟨hDloc, hD⟩, -⟩ := cartier_existsUnique_effective_of_regularEquations X
    (fun x => (U x).1) hcover f hf0
    (fun x y => ideal_local_generators_transition I (U x) (U y) (f x) (f y) (hIf x) (hIf y))
  refine ⟨D, hD, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hcover
  intro x
  rw [hIf x]
  apply SetLike.coe_injective
  ext a
  rw [← effectiveCartierIdealSheaf_affine_image]
  exact (negativeCartierToUnit_range_iff X D hD (U x).1 a).trans
    (negativeCartier_regularSection_mem_iff X D (U x).1 (f x) (hf0 x) (hDloc x).symm a)

end MixedFujita
