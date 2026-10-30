/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplanePointCentre
public import MixedFujita.KltMinimizerDataPowers

/-!
The data of the minimizer for the hyperplane class from section 5 along a degree sequence
(steps 11 and 14).

Let Y be a smooth closed subvariety of projective space with hyperplane divisor J, cut by a
linear form g that does not vanish at the closed point x, and take the zero boundary. Fix s ≥ 1
and b ≤ 1 with s b = dim Y + 1, t₀ < b and δ ∈ (0, 1). Assume, for all large degrees j and all
t in [t₀, b):

* the realization sets of the tuples of sections of j J at x are Zariski closed (Lemma 3);
* the interior condition (7) with margin δ holds for one basis of the sections of j J;
* the specialization comparison (6) holds at the closed points of a set whose closed points are
  dense over each generization w ≠ x of x (`ClosedPointsDenseOver`: for example an open set, or
  the complement of countably many proper closed subsets over an uncountable field).

Assume also, as in `projectiveHyperplane_eventually_pointCentre`, that the closures of the
generizations of x have finite dimension and that those other than x have degree at least s^dim.
Then the data of the minimizer (`KltIsolationMinimizerData`) exist at x for every m₀ ≥ 1.

The main step is `projectiveHyperplane_exists_minimal_pointCentre_of_degree_sequence`, which gives
a minimizing profile datum with the point-centre property at one degree and one t < b; the data of
the minimizer for J follow when b ≤ 1, and for a divisor A with k A = J + div φ when k b ≤ 1
(`KltMinimizerDataShift`).

Proof: for large j the normalized infimum f_j lies in [κ, 1 − δ], by the bound (8) and the global
minimizing pair. So its liminf c is positive and some degree sequence realizes it. For large j
every minimizing profile datum has log discrepancy at least −log(1 − δ)/c₁ (Lemma 1, since its
objective is at most N (1 − δ)). Section 5 along this sequence
(`projectiveHyperplane_pointCentre_along_sequence`) gives a degree at which the global minimizing
pair has the point-centre property. That gives the data for m₀ = 1, and the powers of the sections
give every m₀ (`kltIsolationMinimizerData_of_kltIsolationMinimizerData`).
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

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n m : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- A minimizing profile datum with the point-centre property, for the hyperplane class with zero
boundary: under the hypotheses of the data of the minimizer below (without b ≤ 1) there are t in
[t₀, b), a degree j and a profile datum of a basis of the sections of j J at x which is minimal
among the data of that basis, has objective smaller than h^0(j J) and has the point-centre
property. -/
theorem projectiveHyperplane_exists_minimal_pointCentre_of_degree_sequence
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgx : g ∉ (e x).asHomogeneousIdeal) {b t₀ δ : ℝ} (hb : 0 < b) (s : ℕ)
    (hs : 1 ≤ s) (hsb : (s : ℝ) * b = m + 1) (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ m ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      ∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ)
    (h6 : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b → ∀ w : Y, w ⤳ x → w ≠ x →
      ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
        ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ G → w ⤳ y →
        sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) x
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j ≤
          sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) y
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ j : ℕ, 1 ≤ j ∧
      0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ∧
      ∃ (B : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)),
      ∃ p ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen) x B,
        (∀ p' ∈ sncWeightProfiles cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          (j • projectiveHyperplaneCartier e g hg hggen) x B,
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
        (∑ i, Real.exp (p.1 / t - p.2 i / j)) <
          (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ∧
        SNCWeightProfileHasPointCentre cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          (j • projectiveHyperplaneCartier e g hg hggen) x B p := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hYn : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, hr₀, hfin, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  have hν : (0 : ℝ) < (r₀ : ℝ) / m.factorial := by
    have : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
    positivity
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  -- the spaces of sections are not zero
  have hNpos : ∀ j : ℕ, 0 < Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    intro j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    have := hfin j
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩
  -- the global minimizing pairs, the bounds of the profile data and the bound (8)
  obtain ⟨κ, -, -, c₀, -, hevmin⟩ := projectiveHyperplane_exists_global_sncWeight_minimizer e g
    hg hggen he hm cY hb
  obtain ⟨κ', -, -, c₁, c₂, hc₁, hevbd⟩ := projectiveHyperplane_sncWeightProfiles_bounds e g hg
    hggen he hm cY hb
  obtain ⟨κ₈, hκ₈, -, hev8⟩ := projectiveHyperplane_weightExponentialObjective_ge (m := m) e g hg
    hggen he hdimY hm hb
  have hc₁pos : (0 : ℝ) < (c₁ : ℝ) := by exact_mod_cast hc₁
  have ha : 0 < -Real.log (1 - δ) / c₁ := by
    have hlog : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
    exact div_pos (by linarith) hc₁pos
  -- the parameter t of section 5
  obtain ⟨t, ht₀', ht, htb, hpc⟩ := projectiveHyperplane_pointCentre_along_sequence_of_dense e g hg
    hggen
    he cY (1 : Y.functionFieldˣ) le_rfl
    (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) hklt x
    hxc hgx (by omega) ha hb s hs hsb ht₀ hdim hdeg
  -- the normalized infimum is eventually at most 1 - δ
  have hfle : ∀ᶠ j : ℕ in atTop, sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤ 1 - δ := by
    filter_upwards [hevmin, hclosed, hstart] with j hjmin hjcl hjst
    obtain ⟨B₁, p₁, hp₁, -, hp₁val, -, -⟩ := hjmin x hxc ht htb.le hδ hδ1 hjcl (hjst t ht₀' htb)
    have hNj : (0 : ℝ) < (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
      exact_mod_cast hNpos j
    rw [div_le_iff₀ hNj]
    calc _ ≤ ∑ i, Real.exp (p₁.1 / t - p₁.2 i / j) := sncWeightInfimum_le _ _ _ _ _ _ t j B₁ hp₁
      _ ≤ _ := hp₁val
      _ = _ := by ring
  -- the normalized infimum is eventually at least κ₈
  have hfge : ∀ᶠ j : ℕ in atTop, κ₈ ≤ sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    filter_upwards [hev8, hevmin, hclosed, hstart] with j hj8 hjmin hjcl hjst
    obtain ⟨B₁, p₁, hp₁, -, -, -, -⟩ := hjmin x hxc ht htb.le hδ hδ1 hjcl (hjst t ht₀' htb)
    have hNj : (0 : ℝ) < (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
      exact_mod_cast hNpos j
    rw [le_div_iff₀ hNj]
    refine le_sncWeightInfimum _ _ _ _ _ x _ t j ⟨_, B₁, p₁, hp₁, rfl⟩ fun B p hp => ?_
    obtain ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, hGsupp, hw0, hwΦ, hA, hv⟩ := hp
    have hobj : weightExponentialObjective
        (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
          (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
            principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
          ((1 : ℕ) : ℝ))
        (fun i k => (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor
          (j • projectiveHyperplaneCartier e g hg hggen) (B i) (hs i))) (ξ k) : ℝ)) t j w =
        ∑ i, Real.exp (p.1 / t - p.2 i / j) := by
      unfold weightExponentialObjective
      rw [hA]
      exact Finset.sum_congr rfl fun i _ => by rw [hv i]
    -- the log discrepancy of the weight is not negative
    have hA0 : 0 ≤ p.1 := by
      rw [hA]
      refine Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) ?_
      have h1 := logPairIsKlt_crepantBoundary_coefficient_lt π hπ cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        hklt cX ⟨ξ k, hξ k⟩
      have h2 : ((cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
          cX etaleCharts_cover) (ξ k) : ℤ) : ℝ) < ((1 : ℕ) : ℝ) := by exact_mod_cast h1
      exact div_nonneg (by linarith) (by norm_num)
    have h8 := hj8 x X π hπ cY cX ξ hinj hξ hsnc hBsupp B hGsupp w hw0 hwΦ ht htb.le
    rw [← hA] at h8
    have hexp : 1 ≤ Real.exp (p.1 / (2 * t)) := Real.one_le_exp (div_nonneg hA0 (by linarith))
    calc κ₈ * (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ)
        ≤ κ₈ * (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) *
          Real.exp (p.1 / (2 * t)) := le_mul_of_one_le_right (by positivity) hexp
      _ ≤ _ := h8
      _ = _ := hobj
  -- a degree sequence realizing the liminf, which is positive
  have hf0 : ∀ j : ℕ, 0 ≤ sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := fun j =>
    div_nonneg (sncWeightInfimum_nonneg _ _ _ _ _ _ _ _ _) (Nat.cast_nonneg _)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (fun j : ℕ => sncWeightInfimum cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hf0)
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop (fun j : ℕ => sncWeightInfimum cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) :=
    isCoboundedUnder_ge_of_eventually_le atTop hfle
  obtain ⟨mseq, hmseqf, hmseq⟩ := exists_seq_tendsto_liminf hcobdd hbdd
  have hcpos : 0 < liminf (fun j : ℕ => sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x
      (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) atTop :=
    lt_of_lt_of_le hκ₈ (le_liminf_of_le hcobdd hfge)
  -- the bound of Lemma 1 for the minimizing profile data of large degree
  have hAj : ∀ᶠ j : ℕ in atTop, ∀ (B : Module.Basis (Fin (Module.finrank K
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
          (∑ i, Real.exp (p.1 / t - p.2 i / (j : ℝ))) ≤
            ∑ i, Real.exp (p'.1 / t - p'.2 i / (j : ℝ))) →
      -Real.log (1 - δ) / c₁ ≤ p.1 := by
    filter_upwards [hevmin, hevbd, hclosed, hstart] with j hjmin hjbd hjcl hjst
    intro B p hp hpmin
    obtain ⟨B₁, p₁, hp₁, -, hp₁val, -, -⟩ := hjmin x hxc ht htb.le hδ hδ1 hjcl (hjst t ht₀' htb)
    exact (hjbd x (hNpos j) B p hp ht htb.le hδ.le ((hpmin B₁ p₁ hp₁).trans hp₁val)).1
  -- section 5 along the sequence
  have hpcev := hpc hν hlim hcpos rfl hbdd mseq hmseq hmseqf
    (hmseq.eventually (h6.mono fun j hj => hj t ht₀' htb)) (hmseq.eventually hAj)
  -- one degree of the sequence where everything holds
  obtain ⟨k, hk, hkmin, hkcl, hkst, hk1⟩ := (hpcev.and ((hmseq.eventually hevmin).and
    ((hmseq.eventually hclosed).and ((hmseq.eventually hstart).and
      (hmseq.eventually (eventually_ge_atTop 1)))))).exists
  obtain ⟨B, p, hp, hmin, hpval, -, -⟩ := hkmin x hxc ht htb.le hδ hδ1 hkcl (hkst t ht₀' htb)
  have hNk : (0 : ℝ) < (Module.finrank K
      Γ((mseq k • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
    exact_mod_cast hNpos (mseq k)
  exact ⟨t, ht₀', ht, htb, mseq k, hk1, hNpos (mseq k), B, p, hp, fun p' hp' => hmin B p' hp',
    lt_of_le_of_lt hpval (by nlinarith), hk B p hp hmin⟩

/-- The data of the minimizer at x for the hyperplane class with zero boundary, for every
m₀ ≥ 1, from the closedness of the realization sets, the interior condition (7) and the
specialization comparison (6) (at a set of closed points dense over each generization of x) at all
large degrees, and the degree condition on the closures of the generizations of x. -/
theorem projectiveHyperplane_kltIsolationMinimizerData_of_degree_sequence
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgx : g ∉ (e x).asHomogeneousIdeal) {b t₀ δ : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) (s : ℕ)
    (hs : 1 ≤ s) (hsb : (s : ℝ) * b = m + 1) (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ m ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ((D • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (D : ℝ) ^ D') atTop (nhds ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      ∃ (B₀ : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) (ζ : ℝ), 0 ≤ ζ ∧
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B₀ i)).toNat : ℝ)) ≤ 1 - δ)
    (h6 : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b → ∀ w : Y, w ⤳ x → w ≠ x →
      ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
        ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ G → w ⤳ y →
        sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) x
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j ≤
          sncWeightInfimum cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
            (j • projectiveHyperplaneCartier e g hg hggen) y
            (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) t j)
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (projectiveHyperplaneCartier e g hg hggen) m₀ x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  obtain ⟨t, -, ht, htb, j, hj1, hN, B, p, hp, hmin, hlt, hpc⟩ :=
    projectiveHyperplane_exists_minimal_pointCentre_of_degree_sequence e g hg hggen he hm cY x hxc
      hgx hb s hs hsb ht₀ hδ hδ1 hdim hdeg hclosed hstart h6
  have hdata := kltIsolationMinimizerData_of_minimal_sncWeightProfile cY (1 : Y.functionFieldˣ)
    1 le_rfl (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
    hklt (projectiveHyperplaneCartier e g hg hggen) 1 x j hj1 (one_dvd _) hN (fun i => B i) ht
    (by rw [Nat.cast_one, one_mul]; exact lt_of_lt_of_le htb hb1) hp hmin hlt hpc
  exact kltIsolationMinimizerData_of_kltIsolationMinimizerData cY _ 1 _ _ x hdata m₀ hm₀

end Hyperplane

end MixedFujita
