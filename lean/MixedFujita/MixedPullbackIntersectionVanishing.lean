/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperBaseMixedEulerNilpotence

/-! 引き戻し因子と任意追加因子の通常混合交点数の基底次元超過消滅。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual representatives compare a Cartier coefficient on the source with
the original translated Euler difference, even along a nondominant map. -/
theorem cartierPulledModuleMixedEulerDifference_cartier_coefficient_eq_of_representations
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (C : CartierDivisor Y) (E : CartierDivisor X) (G : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj E.sheaf ≅ G.sheaf) :
    cartierPulledModuleMixedEulerDifference K p C.sheaf D E =
      cartierMixedEulerDifference K F (G + C) := by
  induction h generalizing E G with
  | nil =>
    exact moduleEulerChar_congr K (tensorIso a (Iso.refl C.sheaf) ≪≫ cartierTensorSheafIso G C)
  | @cons H J D F hHJ hDF ih =>
    obtain ⟨b⟩ := hHJ
    change cartierPulledModuleMixedEulerDifference K p C.sheaf D (E + H) -
      cartierPulledModuleMixedEulerDifference K p C.sheaf D E =
        cartierMixedEulerDifference K F ((G + C) + J) - cartierMixedEulerDifference K F (G + C)
    simpa only [add_right_comm G J C] using congrArg₂ (· - ·)
      (ih (E + H) (G + J)
        ((Scheme.Modules.pullback p).mapIso (cartierTensorSheafIso E H).symm ≪≫
          cartierPullbackTensorIso E p H.sheaf ≪≫ tensorIso a b ≪≫ cartierTensorSheafIso G J))
      (ih E G a)


/-- Too many base directions vanish in the ORIGINAL Cartier Euler
difference on a proper integral source, for every source translate. -/
theorem proper_cartierMixedEulerDifference_representations_vanish_of_base_dimension
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (p : Y ⟶ X)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (hlen : n < D.length) (C : CartierDivisor Y) :
    cartierMixedEulerDifference K F C = 0 := by
  let := C.isInvertible_sheaf
  let : C.sheaf.IsCoherent := invertible_module_isCoherent C.sheaf
  have hzero := proper_cartierPulledModuleMixedEulerDifference_vanish_of_base_dimension
    K n hdim p C.sheaf D hlen 0
  have a : (Scheme.Modules.pullback p).obj (0 : CartierDivisor X).sheaf ≅
      (0 : CartierDivisor Y).sheaf :=
    (Scheme.Modules.pullback p).mapIso (cartierZeroSheafIso X) ≪≫
      Scheme.Modules.pullbackObjUnitIso p ≪≫ (cartierZeroSheafIso Y).symm
  rw [cartierPulledModuleMixedEulerDifference_cartier_coefficient_eq_of_representations
    K p h C 0 0 a, zero_add] at hzero
  exact hzero


/-- Arbitrary additional source factors preserve the base-dimension
vanishing. This directly covers powers of a pullback mixed with any ample family. -/
theorem proper_cartierMixedEulerDifference_mixed_pullback_vanish_of_base_dimension
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (p : Y ⟶ X)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (hlen : n < D.length) (A : List (CartierDivisor Y)) (C : CartierDivisor Y) :
    cartierMixedEulerDifference K (F ++ A) C = 0 := by
  have hvan : ∀ A : List (CartierDivisor Y), ∀ C : CartierDivisor Y,
      cartierMixedEulerDifference K (A ++ F) C = 0 := by
    intro A
    induction A with
    | nil =>
      intro C
      exact proper_cartierMixedEulerDifference_representations_vanish_of_base_dimension
        K n hdim p h hlen C
    | cons H A ih =>
      intro C
      change cartierMixedEulerDifference K (A ++ F) (C + H) -
        cartierMixedEulerDifference K (A ++ F) C = 0
      rw [ih, ih, sub_self]
  exact (cartierMixedEulerDifference_perm K List.perm_append_comm C).trans (hvan A C)


/-- The usual INTEGER top mixed intersection, with its original dimension
and Euler-coefficient normalization, vanishes above the base dimension. -/
theorem proper_cartierMixedIntersection_mixed_pullback_vanish_of_base_dimension
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (p : Y ⟶ X)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (hlen : n < D.length) (A : List (CartierDivisor Y))
    (hdimY : topologicalKrullDim Y = (F ++ A).length) :
    cartierMixedIntersection K (F ++ A) hdimY = 0 :=
  proper_cartierMixedEulerDifference_mixed_pullback_vanish_of_base_dimension K n hdim p h hlen A 0


/-- In the manuscript power notation, D^k times ANY remaining source
factors is zero for k larger than the proper integral base dimension,
whenever O(D) is the actual pullback of O(H). Ampleness is unnecessary. -/
theorem proper_cartierMixedIntersection_pullback_power_vanish
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X ≤ n) (p : Y ⟶ X)
    (H : CartierDivisor X) (D : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj H.sheaf ≅ D.sheaf)
    (k : ℕ) (hk : n < k) (A : List (CartierDivisor Y))
    (hdimY : topologicalKrullDim Y = (List.replicate k D ++ A).length) :
    cartierMixedIntersection K (List.replicate k D ++ A) hdimY = 0 := by
  have h : List.Forall₂
      (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf))
      (List.replicate k H) (List.replicate k D) := by
    clear hk hdimY
    induction k with
    | zero => exact .nil
    | succ k ih => exact .cons ⟨a⟩ ih
  exact proper_cartierMixedIntersection_mixed_pullback_vanish_of_base_dimension
    K n hdim p h (by simpa only [List.length_replicate] using hk) A hdimY

end MixedFujita
