/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialHyperplaneSerreVanishing
public import MixedFujita.CartierSerreResidueDescent
public import MixedFujita.CartierAmpleDefinition
public import MixedFujita.CartierSectionDivisor

/-! Serre vanishing for every supplied CartierIsAmpleProj H over any field: for any Cartier divisor D, every positive actual TauCeti cohomology group of D+jH vanishes once j is sufficiently large. Use the original embedding and principal-shift equation for mH, actual hyperplane Serre vanishing and all residue classes modulo m. No infinite-field, smoothness, characteristic-zero, separate finiteness or vanishing premise is needed. Kodaira and Kawamata--Viehweg vanishing remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem cartierIsAmpleProj_eventually_cohomology_subsingleton
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) (D : CartierDivisor X) :
    ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology (D + j • H).sheaf (q + 1)) := by
  obtain ⟨m, hm, n, e, he, _, g, hg, hgX, f, hmH⟩ := hH
  letI := he
  let J := projectiveHyperplaneCartier e g hg hgX
  let a : (m • H).sheaf ≅ J.sheaf :=
    eqToIso (congrArg CartierDivisor.sheaf hmH) ≪≫ cartierSheafPrincipalShiftIso J f
  apply cartier_serreVanishing_of_positive_multiple H m (by omega) ?_ D
  intro F
  obtain ⟨j₀, hj₀⟩ := projectiveHyperplane_cartier_serreVanishing e g hg hgX F
  refine ⟨j₀, fun j hj q => ?_⟩
  letI := hj₀ j hj q
  exact (actualCohomologyLinearEquivOfIso
    (cartierAddNaturalMultiplesSheafIsoOfIso F (m • H) J a j) (q + 1)).subsingleton

end MixedFujita
