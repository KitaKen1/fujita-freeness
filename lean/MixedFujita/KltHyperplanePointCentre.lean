/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltNormalizedInfimum
public import MixedFujita.ProjectiveIntegralHilbert
public import MixedFujita.ProjectiveHyperplanePointCentre

/-!
The existing section 5 point-centre argument already permits a general klt boundary and a singular
source when the divisor is a hyperplane class. Here the general klt estimates and attainment
theorems supply its analytic hypotheses. Point centres are a conclusion, not an extra input.
Tuple closedness, an interior infimum gap, specialization comparison and degree growth remain
explicit hypotheses; subsequent wrappers supply the gap and comparison from volume and closedness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {N n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [IsLocallyNoetherian Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme N K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin N) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

set_option quotPrecheck false

local notation "J" => projectiveHyperplaneCartier e g hg hggen
local notation "Nsec" => (fun j : ℕ => Module.finrank K Γ((j • J).sheaf, ⊤))

/-- A general klt minimizing profile with point centre for a hyperplane divisor. The source
need not be smooth and the boundary need not vanish. -/
theorem klt_projectiveHyperplane_exists_minimal_pointCentre
    (he : e ≫ polynomialProjectiveToBase N K = Y ↘ Spec (CommRingCat.of K)) (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D₀ : CartierDivisor Y) (hklt : LogPairIsKlt cY fY d D₀)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    {b t₀ δ : ℝ} (hb : 0 < b) (s : ℕ) (hs : 1 ≤ s)
    (hsb : (s : ℝ) * b = n + 1) (ht₀ : t₀ < b) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hdim : ∀ w : Y, w ⤳ x → ∃ D' : ℕ, D' ≤ n ∧
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞))
    (hdeg : ∀ (w : Y) (hgW : g ∉ ((pointClosureι w ≫ e)
        (genericPoint (pointClosureScheme w))).asHomogeneousIdeal) (D' : ℕ), w ⤳ x → w ≠ x →
      topologicalKrullDim (closure ({w} : Set Y)) = ((D' : ℕ) : WithBot ℕ∞) →
      ∀ r : ℕ, Tendsto (fun j : ℕ => (Module.finrank K
          Γ((j • projectiveHyperplaneCartier (pointClosureι w ≫ e) g hg hgW).sheaf, ⊤) : ℝ) /
            (j : ℝ) ^ D') atTop (𝓝 ((r : ℝ) / D'.factorial)) → s ^ D' ≤ r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY fY d D₀ (j • J) x)
    (hstart : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b →
      sncWeightInfimum cY fY d D₀ (j • J) x (Nsec j) t j ≤ (Nsec j : ℝ) * (1 - δ))
    (h6 : ∀ᶠ j : ℕ in atTop, ∀ t : ℝ, t₀ ≤ t → t < b → ∀ w : Y, w ⤳ x → w ≠ x →
      ∃ G : Set Y, ClosedPointsDenseOver K w G ∧
        ∀ y : Y, IsClosed ({y} : Set Y) → y ∈ G → w ⤳ y →
          sncWeightInfimum cY fY d D₀ (j • J) x (Nsec j) t j ≤
            sncWeightInfimum cY fY d D₀ (j • J) y (Nsec j) t j) :
    ∃ t : ℝ, t₀ ≤ t ∧ 0 < t ∧ t < b ∧ ∃ j : ℕ, 1 ≤ j ∧ 0 < Nsec j ∧
      ∃ B : Module.Basis (Fin (Nsec j)) K Γ((j • J).sheaf, ⊤),
        ∃ p ∈ sncWeightProfiles cY fY d D₀ (j • J) x B,
          (∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • J) x B,
            (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) < (Nsec j : ℝ) ∧
          SNCWeightProfileHasPointCentre cY fY d D₀ (j • J) x B p := by
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field e he
  have hdimY : topologicalKrullDim Y = n := etaleChart_topologicalKrullDim cY
  have hJ : CartierIsAmpleProj K J := projectiveHyperplaneCartier_isAmpleProj e g hg hggen he
  obtain ⟨r₀, hr₀, hfin, hlim⟩ := projectiveHyperplane_hilbert_leading_integral e g hg hggen he hdimY hn
  have hν : (0 : ℝ) < (r₀ : ℝ) / n.factorial := by
    have : (0 : ℝ) < r₀ := by exact_mod_cast hr₀
    positivity
  have hNpos : ∀ j : ℕ, 0 < Nsec j := by
    intro j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    have hσ₀0 : σ₀ ≠ 0 := by
      rintro rfl
      obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
      rw [map_zero] at hu
      exact not_isUnit_zero hu
    have := hfin j
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, hσ₀0⟩
  obtain ⟨C, hC, hcoeff⟩ := klt_sncWeightProfiles_lower_bounds hn cY fY d hd D₀ J hklt hJ
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have ha : 0 < -Real.log (1 - δ) / C := by
    have hlog : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
    exact div_pos (by linarith) hCr
  obtain ⟨t, ht₀', ht, htb, hpc⟩ := projectiveHyperplane_pointCentre_along_sequence_of_dense e g hg
    hggen he cY fY hd D₀ hklt x hxc hgx (show 0 < n from hn) ha hb s hs hsb ht₀ hdim hdeg
  let f : ℕ → ℝ := fun j => sncWeightInfimum cY fY d D₀ (j • J) x (Nsec j) t j / Nsec j
  have hfle : ∀ᶠ j : ℕ in atTop, f j ≤ 1 - δ := by
    filter_upwards [hstart] with j hj
    have hNr : (0 : ℝ) < Nsec j := by exact_mod_cast hNpos j
    exact (div_le_iff₀ hNr).mpr (by simpa [mul_comm] using hj t ht₀' htb)
  obtain ⟨κ, hκ, -, hev8⟩ := klt_ample_normalizedInfimum_ge hn cY fY d hd D₀ J hklt hJ hb
  have hfge : ∀ᶠ j : ℕ in atTop, κ ≤ f j := by
    filter_upwards [hev8] with j hj
    have := hfin j
    exact hj x (hNpos j) (Module.finBasis K _) ht htb.le
  have hf0 : ∀ j : ℕ, 0 ≤ f j := fun j =>
    div_nonneg (sncWeightInfimum_nonneg cY fY d D₀ (j • J) x (Nsec j) t j) (Nat.cast_nonneg _)
  have hbdd : IsBoundedUnder (· ≥ ·) atTop f :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall hf0)
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop f :=
    isCoboundedUnder_ge_of_eventually_le atTop hfle
  obtain ⟨mseq, hmseqf, hmseq⟩ := exists_seq_tendsto_liminf hcobdd hbdd
  have hcpos : 0 < liminf f atTop := hκ.trans_le (le_liminf_of_le hcobdd hfge)
  have hevmin := klt_ample_global_minimizer_of_infimum_gap hn cY fY d hd D₀ J hklt hJ hb
  have hmin : ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Nsec j)) K Γ((j • J).sheaf, ⊤),
        ∃ p ∈ sncWeightProfiles cY fY d D₀ (j • J) x B,
          (∀ B' : Module.Basis (Fin (Nsec j)) K Γ((j • J).sheaf, ⊤),
            ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • J) x B',
              (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) ∧
          (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ (Nsec j : ℝ) * (1 - δ) := by
    filter_upwards [hevmin, hclosed, hstart] with j hjmin hjcl hjst
    have := hfin j
    exact hjmin x (hNpos j) (Module.finBasis K _) ht htb.le hδ hjcl (hjst t ht₀' htb)
  have hAj : ∀ᶠ j : ℕ in atTop,
      ∀ B : Module.Basis (Fin (Nsec j)) K Γ((j • J).sheaf, ⊤),
        ∀ p ∈ sncWeightProfiles cY fY d D₀ (j • J) x B,
          (∀ B' : Module.Basis (Fin (Nsec j)) K Γ((j • J).sheaf, ⊤),
            ∀ p' ∈ sncWeightProfiles cY fY d D₀ (j • J) x B',
              (∑ i, Real.exp (p.1 / t - p.2 i / j)) ≤ ∑ i, Real.exp (p'.1 / t - p'.2 i / j)) →
          -Real.log (1 - δ) / C ≤ p.1 := by
    filter_upwards [hmin, eventually_ge_atTop 1] with j hj hj1
    intro B p hp hpmin
    obtain ⟨B₁, p₁, hp₁, -, hp₁val⟩ := hj
    exact (hcoeff j hj1 x (hNpos j) B p hp ht ((hpmin B₁ p₁ hp₁).trans hp₁val)).1
  have hpcev := hpc hν hlim hcpos rfl hbdd mseq hmseq hmseqf
    (hmseq.eventually (h6.mono fun j hj => hj t ht₀' htb)) (hmseq.eventually hAj)
  obtain ⟨k, hkpc, hkmin, hk1⟩ := (hpcev.and ((hmseq.eventually hmin).and
    (hmseq.eventually (eventually_ge_atTop 1)))).exists
  obtain ⟨B, p, hp, hpmin, hpval⟩ := hkmin
  have hNr : (0 : ℝ) < Nsec (mseq k) := by exact_mod_cast hNpos (mseq k)
  exact ⟨t, ht₀', ht, htb, mseq k, hk1, hNpos (mseq k), B, p, hp,
    fun p' hp' => hpmin B p' hp', hpval.trans_lt (by nlinarith), hkpc B p hp hpmin⟩

end MixedFujita
