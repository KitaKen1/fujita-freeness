/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierActualPullbackOrder
public import MixedFujita.CartierGlobalGenerationOperations
public import MixedFujita.CartierGradedPullback

/-! 任意射の実Cartier代表元による元の大域生成性とsemiample性の保存。 See reports/check-228-semiample-mixed-intersection-nonnegative.json for the verified scope. Strict ample-pullback positivity and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- ORIGINAL Cartier global generation pulls back through ANY actual
line-bundle representative. Dominance, closedness and flatness are unnecessary. -/
theorem cartierIsGloballyGenerated_of_pullback_representative
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) (D : CartierDivisor X) (F : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj D.sheaf ≅ F.sheaf)
    (hD : CartierIsGloballyGenerated D) : CartierIsGloballyGenerated F := by
  apply (cartierIsGloballyGenerated_iff_local_frames F).mpr
  intro y g hg
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (p y)
  obtain ⟨s, hs⟩ := (cartierIsGloballyGenerated_iff_local_frames D).mp hD (p y) f hf
  obtain ⟨g', hg', v, hv⟩ := cartierActualPullback_local_coefficients D p F a y f hf
  have ht : IsUnit (cartierLocalCoefficient F y g' hg'
      (cartierPullbackGlobalSectionViaIso D p F a s)) := by
    have h : IsUnit ((v : Y.presheaf.stalk y) * cartierLocalCoefficient F y g' hg'
        (cartierPullbackGlobalSectionViaIso D p F a s)) := by
      rw [← hv s, cartierStalkPullbackCoefficient_apply]
      exact hs.map (p.stalkMap y).hom
    exact (Units.isUnit_units_mul v _).mp h
  obtain ⟨u, hu⟩ := cartierLocalCoefficient_change_frame F y g g' hg hg'
  refine ⟨cartierPullbackGlobalSectionViaIso D p F a s, ?_⟩
  rw [hu]
  exact u.isUnit.mul ht


/-- Positive generated multiples restrict through actual Cartier
representatives along arbitrary maps, including nondominant closed embeddings. -/
theorem cartierSemiample_of_pullback_representative
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : Y ⟶ X) (D : CartierDivisor X) (F : CartierDivisor Y)
    (a : (Scheme.Modules.pullback p).obj D.sheaf ≅ F.sheaf)
    (hD : ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • D)) :
    ∃ q : ℕ, 0 < q ∧ CartierIsGloballyGenerated (q • F) := by
  obtain ⟨q, hq, hgen⟩ := hD
  exact ⟨q, hq, cartierIsGloballyGenerated_of_pullback_representative p (q • D) (q • F)
    (cartierPullbackGradedIso D p F a q) hgen⟩

end MixedFujita
