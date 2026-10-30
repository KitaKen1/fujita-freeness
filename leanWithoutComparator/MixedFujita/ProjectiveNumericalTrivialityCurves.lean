/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointedSmoothCurve
public import MixedFujita.CartierNumericalTriviality
public import MixedFujita.CartierFiniteJets
public import MixedFujita.CartierSectionUnitPrincipality

/-! 全正次元smooth射影源の数値自明切断・点付き曲線次数0。 See reports/check-215-curve-f1-f2-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open scoped Classical
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra
  functionFieldBaseScalarTower

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [Smooth (X ↘ Spec (CommRingCat.of K))]
  {b : ℕ} (e : X ⟶ polynomialProjectiveScheme b K) [IsClosedImmersion e]
  (he : e ≫ polynomialProjectiveToBase b K = X ↘ Spec (CommRingCat.of K))
  (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 1 ≤ d)

include e he d hdim hd


theorem polynomialProjective_numericallyTrivial_section_order_zero
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (x : X) (hx : IsClosed {x}) : cartierSectionVanishingOrder D x s = 0 := by
  obtain ⟨C, i, hic, hCi, hsm, hproper, hdimC, ⟨c, hcx⟩, hhit⟩ :=
    polynomialProjective_exists_pointed_proper_smooth_curve e he d hdim hd x hx
      (cartierSectionNonvanishingOpen D s)
      ((cartierSectionNonvanishingOpen_nonempty_iff D s).mpr hs)
  let := hCi
  let := hic
  let : C.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : Smooth (C ↘ Spec (CommRingCat.of K)) := hsm
  let : IsProper (C ↘ Spec (CommRingCat.of K)) := hproper
  have hc : IsClosed ({c} : Set C) := by
    have hpre : i ⁻¹' {x} = {c} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hz => i.isClosedEmbedding.injective (hz.trans hcx.symm), fun hz => hz ▸ hcx⟩
    rw [← hpre]
    exact hx.preimage i.continuous
  obtain ⟨A, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D i
  have hdeg : properCurveCartierDegree (K := K) hdimC A = 0 :=
    (cartierCurvePullbackDegree_eq_representation_degree (K := K) hdimC D i A a).symm.trans
      (hD C hdimC i rfl)
  have hbound := cartierSourceOrder_le_degree_of_curve_image_meets_nonvanishingOpen
    (K := K) hdimC D i A a c hc s hhit
  simp only [hdeg, Int.toNat_zero, Nat.cast_zero, hcx] at hbound
  exact le_antisymm hbound bot_le


theorem polynomialProjective_numericallyTrivial_graded_sections_bound
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D) (j : ℕ) :
    FiniteDimensional K Γ((j • D).sheaf, ⊤) ∧
      Module.finrank K Γ((j • D).sheaf, ⊤) ≤ 1 := by
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper b K
    rw [← he]
    infer_instance
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := X)).exists_closed_singleton
    ⟨genericPoint X, Set.mem_univ _⟩
  have hbound (s : Γ((j • D).sheaf, ⊤)) (hs : s ≠ 0) :
      cartierSectionVanishingOrder (j • D) x s ≤ (0 : ℕ) :=
    le_of_eq (polynomialProjective_numericallyTrivial_section_order_zero e he d hdim hd (j • D)
      (cartierIsNumericallyTrivial_nsmul hD j) s hs x hx)
  exact ⟨geometricSmoothCartier_closedPoint_finiteDimensional_of_order_bound
      (K := K) d hdim (j • D) x hx 0 hbound,
    by simpa using (geometricSmoothCartier_closedPoint_finrank_le_of_order_bound
      (K := K) d hdim (j • D) x hx 0 hbound)⟩


theorem polynomialProjective_numericallyTrivial_nonzero_section_unit
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (x : X) (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    IsUnit (cartierLocalCoefficient D x f hf s) := by
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper b K
    rw [← he]
    infer_instance
  let : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  have hzclosed (z : X) (hz : IsClosed ({z} : Set X)) :
      z ∈ cartierSectionNonvanishingOpen D s := by
    have ho : cartierSectionVanishingOrder D z s = 0 :=
      polynomialProjective_numericallyTrivial_section_order_zero e he d hdim hd D hD s hs z hz
    obtain ⟨a, ha⟩ := D.exists_isLocalEquationAt z
    have hm := ((cartierSectionVanishingOrder_eq_nat_iff D z a ha s 0).mp ho).2
    simp only [zero_add, pow_one, IsLocalRing.mem_maximalIdeal] at hm
    change ¬ ¬ IsUnit ((cartierLocalCoefficient D z a ha) s) at hm
    exact (mem_cartierSectionNonvanishingOpen D s z).mpr ⟨a, ha, not_not.mp hm⟩
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hspec : x ⤳ z := specializes_iff_mem_closure.mpr hz
  exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s x f hf).mp
    (hspec.mem_open (cartierSectionNonvanishingOpen D s).isOpen (hzclosed z hzc))


theorem polynomialProjective_numericallyTrivial_principal_of_nonzero_section
    (D : CartierDivisor X) (hD : CartierIsNumericallyTrivial K D)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    ∃ φ : X.functionFieldˣ, D = principalCartierDivisor X φ :=
  principal_of_section_everywhere_unit D s hs
    (polynomialProjective_numericallyTrivial_nonzero_section_unit e he d hdim hd D hD s hs)

end MixedFujita
