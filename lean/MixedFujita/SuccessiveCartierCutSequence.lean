/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierCutEuler

/-! 固定捻りを含む実有効Cartier逐次切断短完全列。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The actual successive Cartier-cut sequence, indexed so its first
term is literally O(E+mG) and its second is literally O(E+(m+1)G). -/
noncomputable def cartierSuccessiveCutShortComplex
    {X : Scheme.{u}} [IsIntegral X] (E G : CartierDivisor X) (hG : G.IsEffective) (m : ℕ) :
    ShortComplex X.Modules := by
  let S := cartierCutShortComplex (E + (m + 1) • G) G hG
  let a : S.X₁ ≅ (E + m • G).sheaf := eqToIso (congrArg CartierDivisor.sheaf
    (show E + (m + 1) • G - G = E + m • G by rw [add_nsmul, one_nsmul, ← add_assoc, add_sub_cancel_right]))
  exact ShortComplex.mk (a.inv ≫ S.f) S.g (by simp only [Category.assoc, S.zero, comp_zero])


/-- The successive sequence is the ACTUAL short exact Cartier quotient
sequence transported through the canonical divisor arithmetic identity. -/
theorem cartierSuccessiveCutShortComplex_shortExact
    {X : Scheme.{u}} [IsIntegral X] (E G : CartierDivisor X) (hG : G.IsEffective) (m : ℕ) :
    (cartierSuccessiveCutShortComplex E G hG m).ShortExact := by
  let S := cartierCutShortComplex (E + (m + 1) • G) G hG
  let a : S.X₁ ≅ (E + m • G).sheaf := eqToIso (congrArg CartierDivisor.sheaf
    (show E + (m + 1) • G - G = E + m • G by rw [add_nsmul, one_nsmul, ← add_assoc, add_sub_cancel_right]))
  let e : S ≅ cartierSuccessiveCutShortComplex E G hG m :=
    ShortComplex.isoMk a (Iso.refl _) (Iso.refl _)
      (by
        change a.hom ≫ (a.inv ≫ S.f) = S.f ≫ 𝟙 _
        simp only [Category.comp_id, Iso.hom_inv_id_assoc])
      (by
        change S.g ≫ 𝟙 _ = 𝟙 _ ≫ S.g
        simp only [Category.comp_id, Category.id_comp])
  exact ShortComplex.shortExact_of_iso e (cartierCutShortComplex_shortExact _ G hG)

end MixedFujita
