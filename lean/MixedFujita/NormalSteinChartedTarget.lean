/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalCodimensionOneCharts
public import MixedFujita.NormalSteinIitakaDescent

/-!
The actual normal Stein target of a positive free multiple has the dimension and all
codimension-one etale charts used by the positive semiample-contraction interface. The target,
proper dominant map over the base, connected fibres, actual normal stalks, chart cover, ample
Cartier divisor and linear pullback identity are internally constructed. A second version
constructs the Iitaka exponent too. Only a positive free multiple qD is descended here;
descending D itself by consecutive free multiples remains a separate required step.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]

/-- The target charts are derived from normality, with no chart data supplied on either scheme. -/
theorem eventuallyGloballyGenerated_exists_normal_stein_charted_target
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {k : ℕ} (hk : CartierIitakaDimension K D k) :
    ∃ q : ℕ, 0 < q ∧ ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      topologicalKrullDim Y = k ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ CodimOneChartCovered k K Y ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧ IsProper g ∧
      IsProper (Y ↘ Spec (CommRingCat.of K)) ∧ (∀ y : Y, ConnectedSpace (g.fiber y)) ∧
      H.IsEffective ∧ CartierIsGloballyGenerated H ∧ CartierIsAmpleProj K H ∧
      q • D = cartierPullback g H + principalCartierDivisor X φ := by
  obtain ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hdimY, hg, hp, hnormY, happ, hconn, heff, hgg, hamp, hdesc⟩ :=
    eventuallyGloballyGenerated_exists_normal_stein_target_dimension hdim hn hA D hfree hnorm hk
  letI := hY
  letI := hYN
  letI := hYO
  letI := hYft
  exact ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hdimY, hnormY, normal_codimOneChartCovered hdimY hnormY,
    happ, hg, hp, hconn, heff, hgg, hamp, hdesc⟩

/-- Ordinary eventual freeness also supplies the exponent on the same charted target. -/
theorem eventuallyGloballyGenerated_exists_iitaka_and_normal_stein_charted_target
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    ∃ k : ℕ, CartierIitakaDimension K D k ∧ ∃ q : ℕ, 0 < q ∧
      ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      topologicalKrullDim Y = k ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ CodimOneChartCovered k K Y ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧ IsProper g ∧
      IsProper (Y ↘ Spec (CommRingCat.of K)) ∧ (∀ y : Y, ConnectedSpace (g.fiber y)) ∧
      H.IsEffective ∧ CartierIsGloballyGenerated H ∧ CartierIsAmpleProj K H ∧
      q • D = cartierPullback g H + principalCartierDivisor X φ := by
  obtain ⟨k, hk⟩ := eventuallyGloballyGenerated_exists_iitakaDimension_of_normal_projective
    hdim hn hA D hfree hnorm
  exact ⟨k, hk, eventuallyGloballyGenerated_exists_normal_stein_charted_target
    hdim hn hA D hfree hnorm hk⟩

end MixedFujita
