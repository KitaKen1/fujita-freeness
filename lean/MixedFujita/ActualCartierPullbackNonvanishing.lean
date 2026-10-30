/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierActualPullbackOrder
public import MixedFujita.CartierSectionUnitPrincipality
public import MixedFujita.CartierSectionNonvanishingOpen

/-! 非優勢な実Cartier引き戻し切断の非消滅開と像上非消滅からの主因子性。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Actual pullback sections preserve their exact nonvanishing opens
under every actual Cartier presentation, with no dominance assumption. -/
theorem cartierActualPullback_nonvanishingOpen
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (D : CartierDivisor X) (φ : Y ⟶ X) (E : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf) (s : Γ(D.sheaf, ⊤)) :
    cartierSectionNonvanishingOpen E (cartierPullbackGlobalSectionViaIso D φ E a s) =
      φ ⁻¹ᵁ cartierSectionNonvanishingOpen D s := by
  ext y
  change y ∈ cartierSectionNonvanishingOpen E (cartierPullbackGlobalSectionViaIso D φ E a s) ↔
    φ y ∈ cartierSectionNonvanishingOpen D s
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
  obtain ⟨g, hg, v, hv⟩ := cartierActualPullback_local_coefficients D φ E a y f hf
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient E _ y g hg,
    mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (φ y) f hf,
    ← isUnit_map_iff (φ.stalkMap y).hom, ← cartierStalkPullbackCoefficient_apply, hv s]
  exact (Units.isUnit_units_mul v _).symm


/-- If the entire actual source maps into the nonvanishing open of one
actual section, every actual Cartier representative of its pullback is principal. -/
theorem cartierPullback_representation_principal_of_image_nonvanishing
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (D : CartierDivisor X) (φ : Y ⟶ X) (E : CartierDivisor Y)
    (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf) (s : Γ(D.sheaf, ⊤))
    (h : ∀ y : Y, φ y ∈ cartierSectionNonvanishingOpen D s) :
    ∃ f : Y.functionFieldˣ, E = principalCartierDivisor Y f := by
  let t := cartierPullbackGlobalSectionViaIso D φ E a s
  have ht (y : Y) : y ∈ cartierSectionNonvanishingOpen E t := by
    rw [cartierActualPullback_nonvanishingOpen]
    exact h y
  have htne : t ≠ 0 := (cartierSectionNonvanishingOpen_nonempty_iff E t).mp
    ⟨⟨genericPoint Y, ht _⟩⟩
  exact principal_of_section_everywhere_unit E t htne
    (fun y f hf => (mem_cartierSectionNonvanishingOpen_iff_localCoefficient E t y f hf).mp (ht y))

end MixedFujita
