/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierGeneratedPullbackRepresentatives
public import MixedFujita.CartierMixedIntersectionRepresentatives

/-! 有限semiample因子族の実代表元と元混合Euler係数比較。 See reports/check-228-semiample-mixed-intersection-nonnegative.json for the verified scope. Strict ample-pullback positivity and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A whole ORIGINAL semiample family has actual semiample representatives
on an integral source and preserves the actual mixed Euler coefficient. -/
theorem semiample_exists_cartier_representatives
    (K : Type u) [Field K] {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
    [Z.Over (Spec (CommRingCat.of K))] (p : Z ⟶ X)
    (D : List (CartierDivisor X))
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H)) :
    ∃ F : List (CartierDivisor Z), F.length = D.length ∧
      (∀ J ∈ F, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • J)) ∧
      cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Z) D 0 =
        cartierMixedEulerDifference K F 0 := by
  obtain ⟨F, hF⟩ := exists_cartier_direction_representations p D
  have hall : ∀ J ∈ F, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • J) := by
    induction hF with
    | nil => simp
    | @cons H J D F hHJ hDF ih =>
      intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · obtain ⟨a⟩ := hHJ
        exact cartierSemiample_of_pullback_representative p H _ a (hD H (by simp))
      · exact ih (fun L hL => hD L (List.mem_cons_of_mem _ hL)) A hA
  refine ⟨F, hF.length_eq.symm, hall, ?_⟩
  exact cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K p hF 0 0
    ((Scheme.Modules.pullback p).mapIso (cartierZeroSheafIso X) ≪≫
      Scheme.Modules.pullbackObjUnitIso p ≪≫ (cartierZeroSheafIso Z).symm)


/-- Semiample families preserve original global generation under any
specified actual pullback representative family. -/
theorem cartierSemiample_list_of_pullback_representatives
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (p : Y ⟶ X)
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback p).obj H.sheaf ≅ J.sheaf)) D F)
    (hD : ∀ H ∈ D, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H)) :
    ∀ J ∈ F, ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • J) := by
  induction h with
  | nil => simp
  | @cons H J D F hHJ hDF ih =>
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · obtain ⟨a⟩ := hHJ
      exact cartierSemiample_of_pullback_representative p H _ a (hD H (by simp))
    · exact ih (fun L hL => hD L (List.mem_cons_of_mem _ hL)) A hA

end MixedFujita
