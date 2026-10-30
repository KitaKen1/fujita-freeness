/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierHyperplanePower
public import MixedFujita.CartierGeneratedPullbackRepresentatives
public import MixedFujita.ClosedHyperplanePowerRepresentatives

/-! 実射影冪表示の元semiample性と閉代表元族への保存。 See reports/check-231-semiample-numerical-iitaka-dictionary.json for the verified scope. The full original semiample numerical/Iitaka dictionary is proved in the declared scope; general nef positivity, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- A power presentation gives an ORIGINAL positive globally generated
multiple. This auxiliary representation does not replace semiampleness. -/
theorem cartierHasHyperplanePower_semiample
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (H : CartierDivisor X) (hH : CartierHasHyperplanePower K H) :
    ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • H) := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, ⟨a⟩⟩ := hH
  let := he
  exact ⟨m, hm, cartierIsGloballyGenerated_of_pullback_representative (𝟙 X)
    (projectiveHyperplaneCartier e g hg hgen) (m • H)
    ((Scheme.Modules.pullbackId X).app _ ≪≫ a.symm)
    (projectiveHyperplaneCartier_globallyGenerated e g hg hgen)⟩


/-- A power presentation internally supplies an original ample divisor
on the same base, used only for the actual Cartier pullback dictionary. -/
theorem cartierHasHyperplanePower_exists_ample
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (H : CartierDivisor X) (hH : CartierHasHyperplanePower K H) :
    ∃ J : CartierDivisor X, CartierIsAmpleProj K J := by
  obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, a⟩ := hH
  let := he
  exact ⟨_, projectiveHyperplaneCartier_isAmpleProj_of_finite e g hg hgen hover⟩


/-- Closed representatives retain actual hyperplane power data for a
whole family, while retaining the actual line-bundle representation relation. -/
theorem hyperplanePower_list_of_closed_representatives
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
    (i : Y ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    {D : List (CartierDivisor X)} {F : List (CartierDivisor Y)}
    (h : List.Forall₂ (fun H J => Nonempty ((Scheme.Modules.pullback i).obj H.sheaf ≅ J.sheaf)) D F)
    (hD : ∀ H ∈ D, CartierHasHyperplanePower K H) :
    ∀ J ∈ F, CartierHasHyperplanePower K J := by
  induction h with
  | nil => simp
  | @cons H J D F hHJ hDF ih =>
    intro A hA
    rcases List.mem_cons.mp hA with rfl | hA
    · obtain ⟨a⟩ := hHJ
      exact cartierHasHyperplanePower_of_closed_representative K i H _ a (hD H (by simp))
    · exact ih (fun L hL => hD L (List.mem_cons_of_mem _ hL)) A hA

end MixedFujita
