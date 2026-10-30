/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleSumMinimizerData
public import MixedFujita.OrderAverageMinimizerData
public import MixedFujita.KltClosedPointHyperplane

/-!
Smooth isolation data from the corrected closed-point realization loci. The ordinary-point
start, its strict-volume and order-average constructions, principal shifts and powers are reused.
The point-centre step now uses closed representatives agreeing only at closed points; full-scheme
closedness of profiles defined by K-valued bases is not an input.
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

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- An ordinary-point interior start gives smooth isolation data with point closedness
required only at closed points, including the principal shift back to A. -/
theorem smoothHyperplane_minimizerData_of_start_closedPoints
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (A : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l) (φ : Y.functionFieldˣ)
    (hlA : l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (hstartJ : ∃ t₀, 0 < t₀ ∧ t₀ < 1 / (l : ℝ) ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t,
      t₀ ≤ t → t ≤ 1 / (l : ℝ) →
      ∃ B : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B i)).toNat : ℝ)) ≤ 1 - δ)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen)
        (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hYn : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of K))
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := hlr.ne'
  -- every multiple of J has a nonzero section
  have hNpos : ∀ j : ℕ, 0 < Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    intro j
    have := hfin j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, ?_⟩
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  -- the numerical hypothesis for J with s = l (m + 1), and the degree condition
  have hgrowJ : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
          ((((l * (m + 1) : ℕ) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V := by
    intro η d hd hd1 ε hε
    have h := restrictedGrowth_of_nsmul_eq_add_principal A
      (projectiveHyperplaneCartier e g hg hggen) hl φ hlA η (hgrow η d hd hd1) ε hε
    have hc : (((l * (m + 1) : ℕ) : ℕ) : ℝ) ^ d = (l : ℝ) ^ d * ((m : ℝ) + 1) ^ d := by
      push_cast
      rw [mul_pow]
    rw [hc]
    exact h
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ := hstartJ
  let D₀ := 1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))
  refine klt_projectiveHyperplane_minimizerData_shift_of_closedPoints e g hg hggen he hm cY
    (1 : Y.functionFieldˣ) 1 le_rfl D₀ A hklt hl φ hlA x hxc hgx
    (b := 1 / (l : ℝ)) (t₀ := t₀) (δ := min δ (1 / 2)) (one_div_pos.mpr hlr)
    (by simpa only [Nat.cast_one, one_mul] using (le_of_eq (mul_one_div_cancel hl0)))
    (l * (m + 1)) (by simpa using Nat.mul_le_mul hl (Nat.le_add_left 1 m))
    (by push_cast; field_simp) ht₀b (lt_min hδ (by norm_num))
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hgrowJ hclosed hclosedPt ?_ m₀ hm₀
  filter_upwards [hev, eventually_ge_atTop 1] with j hj hj1
  intro t ht₀t htb
  obtain ⟨B, hB⟩ := hj t ht₀t htb.le
  obtain ⟨p, hp, hle⟩ := exists_sncWeightProfile_le_of_smooth_point hm cY
    (j • projectiveHyperplaneCartier e g hg hggen) B B.ne_zero x hxc
    (ht₀.trans_le ht₀t) (j := (j : ℝ)) (by exact_mod_cast hj1) hζ.le
  have hinf := (sncWeightInfimum_le cY (1 : Y.functionFieldˣ) 1 D₀
    (j • projectiveHyperplaneCartier e g hg hggen) x t j B hp).trans hle
  rw [sum_exp_eq_mul_minimizationFunctional (hNpos j)] at hinf
  exact hinf.trans (mul_le_mul_of_nonneg_left
    (hB.trans (sub_le_sub_left (min_le_left δ (1 / 2)) 1)) (Nat.cast_nonneg _))

/-- The strict-volume start and the closed-point representatives give isolation data. -/
theorem smoothHyperplane_minimizerData_of_strictVolume_closedPoints
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (A : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l) (φ : Y.functionFieldˣ)
    (hlA : l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (hvol : ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop
        (𝓝 ((r : ℝ) / m.factorial)) → (l * (m + 1)) ^ m < r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen)
        (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := hlr.ne'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- every multiple of J has a nonzero section
  have hsec : ∀ q : ℕ, 0 ≤ q → ∃ σ : Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      σ ≠ 0 := by
    intro q _
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x q
    refine ⟨σ₀, ?_⟩
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  -- the interior condition (7) with b = 1/l, from the strict volume inequality
  obtain ⟨r, -, -, hlim, hstart⟩ := projectiveHyperplane_multiple_interior_start e g hg hggen he
    hdimY hm (projectiveHyperplaneCartier e g hg hggen) (k := 1) one_pos (one_nsmul _) 0 hsec
  have hlim' : Tendsto (fun D : ℕ => (Module.finrank K
      Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop
      (𝓝 ((r : ℝ) / m.factorial)) := by
    simpa using hlim
  have hvolr : ((l : ℝ) * ((m : ℝ) + 1)) ^ m < (r : ℝ) := by exact_mod_cast hvol r hlim'
  have hroot : (l : ℝ) * ((m : ℝ) + 1) < (r : ℝ) ^ ((m : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hm0, Real.rpow_natCast]
    exact hvolr
  have hb : (m : ℝ) / (1 / l) <
      (m : ℝ) / (m + 1) * ((r : ℝ) / ((1 : ℕ) : ℝ) ^ m) ^ (m : ℝ)⁻¹ := by
    rw [Nat.cast_one, one_pow, div_one, div_div_eq_mul_div, div_one, div_mul_eq_mul_div,
      lt_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ := hstart (b := 1 / l) (one_div_pos.mpr hlr) hb x hxc
  exact smoothHyperplane_minimizerData_of_start_closedPoints e g hg hggen he hm cY A hl φ hlA
    x hxc hgx hgrow ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ hclosed hclosedPt m₀ hm₀

end Hyperplane

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]


/-- The order-average bound (33) supplies the start for an ample sum, with closed-point loci. -/
theorem ampleSum_minimizerData_of_orderAverage_closedPoints (hm : 1 ≤ m) (cY : EtaleChart K Y m)
    (A : CartierDivisor Y) (hA : CartierIsAmpleSum K A) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (havg : ∃ σ : ℝ, (m : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
          ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ))
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • A) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨l, hl, n, e, hci, he, g, hg, hggen, hgx, φ, hlA⟩ :=
    cartierIsAmpleProj_exists_hyperplane_nonvanishing (cartierIsAmpleProj_of_isAmpleSum hA) x
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  refine smoothHyperplane_minimizerData_of_start_closedPoints e g hg hggen he hm cY A hl
    φ hlA x hxc hgx hgrow
    (projectiveHyperplane_start_of_orderAverage e g hg hggen he hm hdimY A hl φ hlA x hxc havg)
    ?_ ?_ m₀ hm₀
  · filter_upwards [htend.eventually hclosed] with j hj
    exact realizationSetsZariskiClosed_of_nsmul_eq cY _ 1 _ hlA x j hj
  · filter_upwards [htend.eventually hclosedPt] with j hj
    exact normalizedProfiles_closedPoints_of_nsmul_eq cY _ 1 _ hlA j hj

/-- The strict-volume branch for an ample sum, with closed-point loci. -/
theorem ampleSum_minimizerData_of_strictVolume_closedPoints (hm : 1 ≤ m) (cY : EtaleChart K Y m)
    (A : CartierDivisor Y) (hA : CartierIsAmpleSum K A) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (hvol : ∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
        Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop (𝓝 ((r : ℝ) / m.factorial)) →
        (l * (m + 1)) ^ m < r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • A) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  obtain ⟨l, hl, n, e, hci, he, g, hg, hggen, hgx, φ, hlA⟩ :=
    cartierIsAmpleProj_exists_hyperplane_nonvanishing (cartierIsAmpleProj_of_isAmpleSum hA) x
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  refine smoothHyperplane_minimizerData_of_strictVolume_closedPoints e g hg hggen he hm
    cY A hl φ hlA x hxc hgx hgrow ?_ ?_ ?_ m₀ hm₀
  · intro r hr
    refine hvol l hl r (Tendsto.congr (fun D => ?_) hr)
    rw [finrank_nsmul_eq_of_nsmul_eq (K := K) hlA D]
  · filter_upwards [htend.eventually hclosed] with j hj
    exact realizationSetsZariskiClosed_of_nsmul_eq cY _ 1 _ hlA x j hj
  · filter_upwards [htend.eventually hclosedPt] with j hj
    exact normalizedProfiles_closedPoints_of_nsmul_eq cY _ 1 _ hlA j hj

end Assembly

end MixedFujita
