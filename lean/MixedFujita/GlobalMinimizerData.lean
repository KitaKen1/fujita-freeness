/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GlobalMinimizerHyperplane
public import MixedFujita.KltMinimizerDataFromWeights

/-!
From a minimizing pair to the data of the minimizer used by section 6 of the manuscript (steps 11
and 14).

* The point-centre property of a profile datum p = (a, v) of a tuple of sections at x: on every
  proper simple normal crossing model and every weight over the fibre of x with datum p, every
  point of the model whose closure meets the fibre of x and whose polytope contains the normalized
  profile v/a lies over x. This is the conclusion of section 5 of the manuscript (the centre of
  every minimizing pair is the point), in the form used by section 6. It is a definition.
* A profile datum of a tuple of sections of j L on a klt pair which is minimal among the data of
  the same tuple, has objective smaller than N and has the point-centre property gives the data of
  the minimizer (`KltIsolationMinimizerData`) when d t < 1 and m₀ divides j: the weight is a
  nonzero minimizer on its model, so the first-order conditions give c, q, the inequality (24)
  and the budget.
* For the hyperplane class of a smooth closed subvariety of projective space with zero boundary:
  for all large j, every closed point x and t ≤ b with t < 1, the closedness of the realization
  sets at x, the interior condition (7) for one basis and the point-centre property of the global
  minimizing pairs give the data of the minimizer at x.

So, for the hyperplane class, what remains of the minimizer statement is: the closedness (Lemma 3),
the interior condition (7) (sections 7 and 8) and the point-centre property (section 5).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Data

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]

/-- The point-centre property of a profile datum p of the tuple s at x: on every proper simple
normal crossing model and every weight over the fibre of x with datum p, every point whose closure
meets the fibre of x and whose polytope contains the normalized profile lies over x. -/
def SNCWeightProfileHasPointCentre (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (x : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤))
    (p : ℝ × (Fin N → ℝ)) : Prop :=
  ∀ (hs : ∀ i, s i ≠ 0) (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
    (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
    (r : ℕ) (ξ : Fin r → X) (w : Fin r → ℝ), Function.Injective ξ →
    (∀ k, Order.coheight (ξ k) = 1) → IsSNCFamily K n ξ →
    (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
        (z : X) = 0) →
    (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0) →
    (∀ k, 0 ≤ w k) →
    (∃ y ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) →
    p.1 = ∑ k, w k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) →
    (∀ i, p.2 i = ∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) →
    ∀ pt : X, (closure ({pt} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
      InSNCProfilePolytope ξ d (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
        (fun i => cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (fun i => p.2 i / p.1) pt →
      pt ∈ π ⁻¹' ({x} : Set Y)

variable [IsProper (Y ↘ Spec (CommRingCat.of K))]

omit [IsLocallyNoetherian Y] in
/-- The data of the minimizer from a minimal profile datum with the point-centre property: on a
klt pair, a profile datum of a tuple of sections of j L which is minimal among the data of the
tuple, has objective smaller than N and has the point-centre property gives
`KltIsolationMinimizerData` when d t < 1 and m₀ divides j. -/
theorem kltIsolationMinimizerData_of_minimal_sncWeightProfile
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y)
    (hklt : LogPairIsKlt cY fY d D₀) (L : CartierDivisor Y) (m₀ : ℕ) (x : Y)
    (j : ℕ) (hj : 1 ≤ j) (hjm₀ : m₀ ∣ j) {N : ℕ} (hN : 0 < N)
    (s : Fin N → Γ((j • L).sheaf, ⊤)) {t : ℝ} (ht : 0 < t) (hdt : (d : ℝ) * t < 1)
    {p : ℝ × (Fin N → ℝ)} (hp : p ∈ sncWeightProfiles cY fY d D₀ (j • L) x s)
    (hmin : ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • L) x s,
      (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j))
    (hlt : (∑ i, Real.exp (p.1 / t - p.2 i / j)) < N)
    (hpc : SNCWeightProfileHasPointCentre cY fY d D₀ (j • L) x s p) :
    KltIsolationMinimizerData cY fY d D₀ L m₀ x := by
  obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp,
    hGsupp, hw0, ⟨y, hy, hwy⟩, hA, hv⟩ := hp
  have hXprop : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  have hb : ∀ k, cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover)
      (ξ k) < (d : ℤ) := fun k =>
    logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY fY d D₀ hklt cX ⟨ξ k, hξ k⟩
  -- the objective of the weight is the objective of its datum
  have hL : weightExponentialObjective
      (fun k => ((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
      (fun i k => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w =
      ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
    unfold weightExponentialObjective
    rw [hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hv i]
  -- the weight is a minimizer on its model
  have hwmin : ∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
      (∃ p' ∈ π ⁻¹' ({x} : Set Y), ∀ k, w' k ≠ 0 → p' ∈ closure ({ξ k} : Set X)) →
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
      weightExponentialObjective
        (fun k => ((d : ℝ) - cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d)
        (fun i k => (cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w' := by
    intro w' hw'0 hw'Φ
    have h := hmin (∑ k, w' k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d),
      fun i => ∑ k, w' k * (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ))
      ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w', hinj, hξ, hsnc, hBsupp,
        hGsupp, hw'0, hw'Φ, rfl, fun i => rfl⟩
    rw [hL]
    exact h
  -- the weight is not zero
  have hwne : ∃ k, w k ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : p.1 = 0 := by
      rw [hA]
      simp [hall]
    have hv0 : ∀ i, p.2 i = 0 := fun i => by
      rw [hv i]
      simp [hall]
    simp only [h0, hv0, zero_div, sub_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨hc, hcq, hqy, hpoly, hsum⟩ := isolation_data_of_sncWeight_minimizer hN ξ d hd _ hb
    (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
    (π ⁻¹' ({x} : Set Y)) ht j hj w hw0 y hy hwy hwne hwmin
  have hcentre := hpc hs X π hπ cX r ξ w hinj hξ hsnc hBsupp hGsupp hw0 ⟨y, hy, hwy⟩ hA hv
  have hq : (fun i => p.2 i / p.1) = fun i => (∑ k, w k * (cartierCoefficient (cartierPullback π
      (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) /
      ∑ k, w k * (((d : ℝ) - cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) / d) := by
    funext i
    rw [hv i, hA]
  rw [hq] at hcentre
  refine ⟨j, N, s, hs, X, hXi, hXn, hXo, hXprop, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, y, _, _,
    hjm₀, hinj, hξ, hsnc, hBsupp, hGsupp, hy, hc, hcq, hqy, hpoly, hcentre, ?_⟩
  have hcast : ((d * j : ℕ) : ℝ) = (d : ℝ) * (j : ℝ) := by push_cast; ring
  rw [hcast, mul_assoc, hsum]
  exact hdt

end Data

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n m : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The data of the minimizer for the hyperplane class of a smooth closed subvariety of projective
space with zero boundary: for all large j, every closed point x, m₀ dividing j and t ≤ b with
t < 1, the closedness of the realization sets at x, the interior condition (7) for one basis and
the point-centre property of the global minimizing pairs give the data of the minimizer at x. -/
theorem projectiveHyperplane_kltIsolationMinimizerData_of_pointCentre
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ j : ℕ in atTop, ∀ x : Y, IsClosed ({x} : Set Y) → ∀ m₀ : ℕ, m₀ ∣ j →
      ∀ {t δ : ℝ}, 0 < t → t ≤ b → t < 1 → 0 < δ → δ < 1 →
      RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen) x →
      (∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ) →
      (∀ (B : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
        ∀ p ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          (j • projectiveHyperplaneCartier e g hg hggen) x B,
        (∀ (B' : Module.Basis (Fin (Module.finrank K
            Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
            Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
          ∀ p' ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) x B',
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
        SNCWeightProfileHasPointCentre cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          (j • projectiveHyperplaneCartier e g hg hggen) x B p) →
      KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (projectiveHyperplaneCartier e g hg hggen) m₀ x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hYn : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  obtain ⟨κ, hκ, hκ1, c, hc, hev⟩ := projectiveHyperplane_exists_global_sncWeight_minimizer e g
    hg hggen he hm cY hb
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro x hx m₀ hm₀ t δ ht htb ht1 hδ hδ1 hclosed hstart hpc
  obtain ⟨B, p, hp, hmin, hpval, -, -⟩ := hj x hx ht htb hδ hδ1 hclosed hstart
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  -- the space of sections is not zero
  have hN : 0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he
      (etaleChart_topologicalKrullDim cY) hm
    have := hfin j
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩
  have hNpos : (0 : ℝ) < (Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by exact_mod_cast hN
  exact kltIsolationMinimizerData_of_minimal_sncWeightProfile cY (1 : Y.functionFieldˣ) 1 le_rfl
    (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) hklt
    (projectiveHyperplaneCartier e g hg hggen) m₀ x j hj1 hm₀ hN (fun i => B i) ht
    (by rw [Nat.cast_one, one_mul]; exact ht1) hp (fun p' hp' => hmin B p' hp')
    (lt_of_le_of_lt hpval (by nlinarith)) (hpc B p hp hmin)

end Hyperplane

end MixedFujita
