/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinPowerSectionDescent
public import MixedFujita.SteinAmpleLinearComparison
public import MixedFujita.NormalSteinChartedTarget
public import MixedFujita.SemiampleIitakaZero
public import MixedFujita.KodairaLemmaNormal

/-!
Prove the original semiample-contraction input of F2, including descent of D itself. Use the
already constructed normal charted Stein target of one positive free multiple, descend large
consecutive free multiples there by powers and actual rational-equation gluing, and subtract.
The previously proved Stein linear-equivalence reflection gives ampleness of the descended D.
Dimension, normality, target codimension-one charts and the all-open function isomorphisms are
all retained on the same target. The original zero-Iitaka case completes the full contraction
statement. Base-point-freeness for klt pairs and Ambro remain separate unproved inputs.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- The actual ample contraction of the original D, on the same normal charted Stein target. -/
theorem eventuallyGloballyGenerated_exists_normal_ample_cartier_contraction
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    {A : CartierDivisor X} (hA : CartierIsAmpleProj K A) (D : CartierDivisor X)
    (hfree : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → CartierIsGloballyGenerated (q • D))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {k : ℕ} (hk : CartierIitakaDimension K D k) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsLocallyNoetherian Y)
      (_ : Y.Over (Spec (CommRingCat.of K)))
      (_ : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K)))
      (g : X ⟶ Y) (_ : IsDominant g) (_ : g.IsOver (Spec (CommRingCat.of K)))
      (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      IsProper g ∧ IsProper (Y ↘ Spec (CommRingCat.of K)) ∧
      (∀ y : Y, ConnectedSpace (g.fiber y)) ∧ topologicalKrullDim Y = k ∧
      (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧ CodimOneChartCovered k K Y ∧
      (∀ U : Y.Opens, Function.Bijective (g.app U).hom) ∧ CartierIsAmpleProj K H ∧
      D = cartierPullback g H + principalCartierDivisor X φ := by
  obtain ⟨q, hq, Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hdimY, hnormY, hcovY, happ, hg, hp, hconn, heff, hgg, hamp, hqD⟩ :=
    eventuallyGloballyGenerated_exists_normal_stein_charted_target hdim hn hA D hfree hnorm hk
  letI := hY
  letI := hYN
  letI := hYO
  letI := hYft
  letI := hgd
  letI := hgo
  letI := hg
  have hsurj := surjective_of_isProper_of_isDominant g
  obtain ⟨B, ψ, hD⟩ := stein_exists_cartier_descent_of_eventual_generation g happ hsurj D
    hfree hq H φ hqD
  have hB := stein_descended_divisor_isAmple_of_ample_multiple g (fun U => (happ U).2)
    hsurj D B H hq φ ψ hD hqD hamp
  exact ⟨Y, hY, hYN, hYO, hYft, g, hgd, hgo, B, ψ,
    hg, hp, hconn, hdimY, hnormY, hcovY, happ, hB, hD⟩

/-- The original positive-Iitaka semiample-contraction statement is a theorem. -/
theorem semiampleContractionPositiveStatement_holds : SemiampleContractionPositiveStatement.{u} := by
  intro K _ _ _ _ X _ _ _ _ n hdim hn hnorm hcov hH D hfree k hk hk1
  obtain ⟨A, hA⟩ := hH
  have : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    obtain ⟨m, hm, N, e, he, hbase, F, hF, hFgen, φ, hrel⟩ := hA
    have : IsClosedImmersion e := he
    have := polynomialProjectiveToBase_isProper N K
    rw [← hbase]
    infer_instance
  obtain ⟨Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hg, hp, hconn, hdimY, hnormY, hcovY, happ, hamp, hD⟩ :=
    eventuallyGloballyGenerated_exists_normal_ample_cartier_contraction hdim hn hA D hfree hnorm hk
  exact ⟨Y, hY, hYN, hYO, hYft, g, hgd, hgo, H, φ,
    hdimY, hnormY, hcovY, happ, hamp, hD⟩

/-- Combine the proved positive-Iitaka contraction with the existing principal zero case. -/
theorem semiampleContractionStatement_holds : SemiampleContractionStatement.{u} :=
  semiampleContraction_of_positive semiampleContractionPositiveStatement_holds

/-- F2 no longer requires a supplied semiample-contraction theorem. -/
theorem linearEffectiveFreeness_of_knf_of_basePointFree_of_nefAddAmple_of_ambro
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hna : NefAddAmpleStatement.{u}) (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_basePointFree_of_nefAddAmple
    hKNF hbpf semiampleContractionPositiveStatement_holds hna hamb

end MixedFujita
