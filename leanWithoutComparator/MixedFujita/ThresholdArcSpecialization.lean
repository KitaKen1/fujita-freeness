/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveThresholdDiagonal
public import MixedFujita.FreenessWithProvedThresholdModel

/-!
The degeneration form of Lemma 3 from its lower semicontinuity along one arc (step 9).

The degeneration statement asks: if the initial monomials of forms f_ℓ for a weight w satisfy the
threshold condition (34) at every point of every chart, then so does the member F(t) of the
degeneration family for some t ≠ 0. Every member with t ≠ 0 is a diagonal transform of the forms,
F(t) = t^(-⟨w,p⟩) f(t^w x), so the conclusion is (34) for the forms themselves, and the
properness of the exceptional divisor is not needed to see it. If (34) fails for the forms at a
point P of the chart x_k = 1, it fails for F(t) at λ_t⁻¹ P = [t^(M - w_i) P_i] for every t ≠ 0:
a polynomial arc in homogeneous coordinates whose value at t = 0 keeps the coordinates of the
largest weight M among k and the i with P_i ≠ 0, hence is a point of projective space. Lower
semicontinuity of the threshold along this one arc (`FormalThresholdArcSpecialization`: if (34)
fails at x(t) for all t ≠ 0, it fails at x(0), for forms depending polynomially on t) makes (34)
fail for the initial monomials at x(0), which is excluded.

The arc statement is the semicontinuity content of Lemma 3 for one parameter, in the formal-test
form of (34). It is a definition, used as a hypothesis; it is not proved here. F1 follows with it
in place of the degeneration statement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology MvPowerSeries
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

section Points

variable {K : Type*} [Field K] {n : ℕ}

/-- The threshold condition (34) at one point p of the chart x_k = 1. -/
def ProjectiveThresholdAt [DecidableEq K] {ι : Type*} (g : ι → MvPolynomial (Fin n) K) (h : ℕ)
    (k : Fin n) (p : {i : Fin n // i ≠ k} → K) : Prop :=
  ∀ (ψ : MvPowerSeries {i : Fin n // i ≠ k} K →ₐ[K] MvPowerSeries {i : Fin n // i ≠ k} K),
    (∀ i, ψ (X i) ≠ 0) → (powerSeriesJacobian ψ).det ≠ 0 → ∀ w : {i : Fin n // i ≠ k} → ℕ, w ≠ 0 →
      ∃ ℓ, (ψ (chartShiftedForm k p (g ℓ))).weightedOrder w <
        (h : ℕ∞) * (((∑ j, w j : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w)

theorem projectiveThresholdCondition_iff_forall_at [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (h : ℕ) :
    ProjectiveThresholdCondition g h ↔ ∀ k p, ProjectiveThresholdAt g h k p :=
  Iff.rfl

/-- (34) fails at the point of projective space with homogeneous coordinates P, in some chart
containing it. -/
def ProjectiveThresholdBadAt [DecidableEq K] {ι : Type*} (g : ι → MvPolynomial (Fin n) K) (h : ℕ)
    (P : Fin n → K) : Prop :=
  ∃ k, P k ≠ 0 ∧ ¬ ProjectiveThresholdAt g h k (fun i => P i / P k)

/-- (34) at one point gives (34) for the diagonal transforms at the rescaled point. -/
theorem projectiveThresholdAt_polynomialDiagonalHom [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (hg : ∀ ℓ, ∃ D, (g ℓ).IsHomogeneous D)
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) (h : ℕ) (k : Fin n) (p : {i : Fin n // i ≠ k} → K)
    (hcond : ProjectiveThresholdAt g h k (fun i => t ^ w i / t ^ w k * p i)) :
    ProjectiveThresholdAt (fun ℓ => polynomialDiagonalHom w t (g ℓ)) h k p := by
  intro ψ hψ hdet wt hwt
  set μ : {i : Fin n // i ≠ k} → K := fun i => t ^ w i / t ^ w k with hμdef
  have hμ : ∀ i, μ i ≠ 0 := fun i => div_ne_zero (pow_ne_zero _ ht) (pow_ne_zero _ ht)
  have hψ' : ∀ i, (ψ.comp (rescaleAlgHom μ)) (X i) ≠ 0 := by
    intro i
    rw [AlgHom.comp_apply, rescaleAlgHom_X_eq, map_mul, algHom_C]
    exact mul_ne_zero ((isUnit_iff_ne_zero.mpr (hμ i)).map (C (σ := {i : Fin n // i ≠ k}))).ne_zero
      (hψ i)
  have hdet' : (powerSeriesJacobian (ψ.comp (rescaleAlgHom μ))).det ≠ 0 := by
    rw [powerSeriesJacobian_det_comp_rescale]
    exact mul_ne_zero ((isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => hμ i)).map
      (C (σ := {i : Fin n // i ≠ k}))).ne_zero hdet
  obtain ⟨ℓ, hℓ⟩ := hcond (ψ.comp (rescaleAlgHom μ)) hψ' hdet' wt hwt
  refine ⟨ℓ, ?_⟩
  obtain ⟨D, hD⟩ := hg ℓ
  have hunit : ∀ c : K, c ≠ 0 →
      (C c : MvPowerSeries {i : Fin n // i ≠ k} K).weightedOrder wt = 0 := fun c hc =>
    weightedOrder_eq_zero_of_isUnit wt ((isUnit_iff_ne_zero.mpr hc).map _)
  simp only
  rw [chartShiftedForm_polynomialDiagonalHom w ht k p hD, map_mul, algHom_C, weightedOrder_mul,
    hunit _ (pow_ne_zero _ (pow_ne_zero _ ht)), zero_add]
  rw [powerSeriesJacobian_det_comp_rescale, weightedOrder_mul,
    hunit _ (Finset.prod_ne_zero_iff.mpr fun i _ => hμ i), zero_add] at hℓ
  exact hℓ

/-- (34) at one point for the diagonal transforms gives (34) for the forms at the rescaled
point. -/
theorem projectiveThresholdAt_of_polynomialDiagonalHom [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (hg : ∀ ℓ, ∃ D, (g ℓ).IsHomogeneous D)
    (w : Fin n → ℕ) {t : K} (ht : t ≠ 0) (h : ℕ) (k : Fin n) (p : {i : Fin n // i ≠ k} → K)
    (hcond : ProjectiveThresholdAt (fun ℓ => polynomialDiagonalHom w t (g ℓ)) h k p) :
    ProjectiveThresholdAt g h k (fun i => t ^ w i / t ^ w k * p i) := by
  have hp : (fun i : {i : Fin n // i ≠ k} =>
      t⁻¹ ^ w i / t⁻¹ ^ w k * (t ^ w i / t ^ w k * p i)) = p := by
    funext i
    rw [inv_pow, inv_pow]
    field_simp
  have h' := projectiveThresholdAt_polynomialDiagonalHom
    (fun ℓ => polynomialDiagonalHom w t (g ℓ))
    (fun ℓ => (hg ℓ).imp fun D hD => polynomialDiagonalHom_isHomogeneous w t hD) w
    (inv_ne_zero ht) h k (fun i => t ^ w i / t ^ w k * p i) (by rw [hp]; exact hcond)
  simpa only [polynomialDiagonalHom_inv_apply w ht] using h'

/-- Nonzero constant multiples of the forms do not change (34) at a point. -/
theorem projectiveThresholdAt_C_mul_iff [DecidableEq K] {ι : Type*}
    (g : ι → MvPolynomial (Fin n) K) (c : ι → K) (hc : ∀ ℓ, c ℓ ≠ 0) (h : ℕ) (k : Fin n)
    (p : {i : Fin n // i ≠ k} → K) :
    ProjectiveThresholdAt (fun ℓ => MvPolynomial.C (c ℓ) * g ℓ) h k p ↔
      ProjectiveThresholdAt g h k p := by
  have hform : ∀ ℓ, chartShiftedForm k p (MvPolynomial.C (c ℓ) * g ℓ) =
      C (c ℓ) * chartShiftedForm k p (g ℓ) := by
    intro ℓ
    unfold chartShiftedForm
    rw [map_mul, MvPolynomial.aeval_C]
    rfl
  have hval : ∀ (ψ : MvPowerSeries {i : Fin n // i ≠ k} K →ₐ[K]
      MvPowerSeries {i : Fin n // i ≠ k} K) (wt : {i : Fin n // i ≠ k} → ℕ) ℓ,
      (ψ (chartShiftedForm k p (MvPolynomial.C (c ℓ) * g ℓ))).weightedOrder wt =
        (ψ (chartShiftedForm k p (g ℓ))).weightedOrder wt := by
    intro ψ wt ℓ
    rw [hform, map_mul, algHom_C, weightedOrder_mul,
      weightedOrder_eq_zero_of_isUnit wt ((isUnit_iff_ne_zero.mpr (hc ℓ)).map _), zero_add]
  constructor
  · intro hcond ψ hψ hdet wt hwt
    obtain ⟨ℓ, hℓ⟩ := hcond ψ hψ hdet wt hwt
    exact ⟨ℓ, by rwa [hval] at hℓ⟩
  · intro hcond ψ hψ hdet wt hwt
    obtain ⟨ℓ, hℓ⟩ := hcond ψ hψ hdet wt hwt
    exact ⟨ℓ, by rwa [hval]⟩

end Points

section Arc

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K]

/-- Lower semicontinuity of the threshold (34) along one arc: for forms G_ℓ(t) of fixed degrees
depending polynomially on t and a polynomial arc x(t) in homogeneous coordinates with x(0) ≠ 0, if
(34) fails at x(t) for G(t) for every t ≠ 0, it fails at x(0) for G(0). This is the
semicontinuity content of Lemma 3 for one parameter in the formal-test form of (34). It is a
definition, used as a hypothesis; it is not proved here. -/
def FormalThresholdArcSpecialization : Prop :=
  ∀ (n : ℕ) {ι : Type} [Fintype ι] (G : ι → Polynomial (MvPolynomial (Fin n) K)) (D : ι → ℕ),
    (∀ ℓ (t : K), ((G ℓ).eval (MvPolynomial.C t)).IsHomogeneous (D ℓ)) →
    ∀ (x : Fin n → Polynomial K) (h : ℕ), (∃ k, (x k).eval 0 ≠ 0) →
    (∀ t : K, t ≠ 0 → ProjectiveThresholdBadAt (fun ℓ => (G ℓ).eval (MvPolynomial.C t)) h
      (fun i => (x i).eval t)) →
    ProjectiveThresholdBadAt (fun ℓ => (G ℓ).eval (MvPolynomial.C 0)) h (fun i => (x i).eval 0)

variable {K}

/-- The degeneration form of Lemma 3 from its lower semicontinuity along one arc: the arc is the
orbit λ_t⁻¹ P of a point where (34) fails for the forms, followed to its limit as t → 0. -/
theorem thresholdDegenerationStatement_of_arcSpecialization
    (harc : FormalThresholdArcSpecialization K) : ThresholdDegenerationStatement K := by
  classical
  intro n ι _ w p f h hhom _hp huniq hzero
  by_cases hf : ProjectiveThresholdCondition f h
  · refine ⟨1, one_ne_zero, ?_⟩
    have h1 : ∀ ℓ, (weightedPolynomialFamily w (p ℓ) (f ℓ)).eval (MvPolynomial.C 1) = f ℓ := by
      intro ℓ
      rw [map_one, weightedPolynomialFamily_at_one]
    simpa only [h1] using hf
  · exfalso
    rw [projectiveThresholdCondition_iff_forall_at] at hf
    push Not at hf
    obtain ⟨k, p₀, hbad⟩ := hf
    choose D hD using hhom
    -- the largest weight M among k and the coordinates i with p₀ i ≠ 0
    let S : Finset (Fin n) := Finset.univ.filter fun i => i = k ∨ ∃ hi : i ≠ k, p₀ ⟨i, hi⟩ ≠ 0
    have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, Or.inl rfl⟩
    have hMk : w k ≤ S.sup w := Finset.le_sup hkS
    have hMi : ∀ i (hi : i ≠ k), p₀ ⟨i, hi⟩ ≠ 0 → w i ≤ S.sup w := fun i hi h0 =>
      Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ⟨hi, h0⟩⟩)
    obtain ⟨i₀, hi₀S, hi₀⟩ := Finset.exists_mem_eq_sup S ⟨k, hkS⟩ w
    -- the arc λ_t⁻¹ P in homogeneous coordinates
    let x : Fin n → Polynomial K := fun i =>
      if hi : i = k then Polynomial.X ^ (S.sup w - w k)
      else Polynomial.C (p₀ ⟨i, hi⟩) * Polynomial.X ^ (S.sup w - w i)
    let G : ι → Polynomial (MvPolynomial (Fin n) K) :=
      fun ℓ => weightedPolynomialFamily w (p ℓ) (f ℓ)
    have hGhom : ∀ ℓ (t : K), ((G ℓ).eval (MvPolynomial.C t)).IsHomogeneous (D ℓ) := by
      intro ℓ t
      rw [← homogeneousParameterFamily_baseChange]
      exact (homogeneousParameterFamily_isHomogeneous w (p ℓ) (hD ℓ)).map _
    have hx0 : ∃ k', (x k').eval 0 ≠ 0 := by
      refine ⟨i₀, ?_⟩
      by_cases hik : i₀ = k
      · have hpow : S.sup w - w k = 0 := by rw [hi₀, hik, Nat.sub_self]
        simp only [x, dite_eq_left hik, hpow, pow_zero, Polynomial.eval_one]
        exact one_ne_zero
      · obtain ⟨hi, h0⟩ : ∃ hi : i₀ ≠ k, p₀ ⟨i₀, hi⟩ ≠ 0 := by
          rcases (Finset.mem_filter.mp hi₀S).2 with h' | h'
          · exact absurd h' hik
          · exact h'
        have hpow : S.sup w - w i₀ = 0 := by rw [hi₀, Nat.sub_self]
        simp only [x, dite_eq_right hik, hpow, pow_zero, mul_one, Polynomial.eval_C]
        exact h0
    have hgen : ∀ t : K, t ≠ 0 → ProjectiveThresholdBadAt
        (fun ℓ => (G ℓ).eval (MvPolynomial.C t)) h (fun i => (x i).eval t) := by
      intro t ht
      have hxk : (x k).eval t = t ^ (S.sup w - w k) := by
        simp only [x, dite_eq_left rfl, Polynomial.eval_pow, Polynomial.eval_X]
      refine ⟨k, ?_, fun hgood => hbad ?_⟩
      · show (x k).eval t ≠ 0
        rw [hxk]
        exact pow_ne_zero _ ht
      -- F(t) = t^(-⟨w,p⟩) · diag_t f
      have hdiag : ∀ ℓ, polynomialDiagonalHom w t (f ℓ) =
          MvPolynomial.C (t ^ polynomialExponentWeight w (p ℓ)) *
            (G ℓ).eval (MvPolynomial.C t) := by
        intro ℓ
        refine (weightedPolynomialFamily_scaled_parameter w (p ℓ) (f ℓ) t fun q hq => ?_).symm
        by_cases hqp : q = p ℓ
        · rw [hqp]
        · exact (huniq ℓ q hq hqp).le
      have h1 : ProjectiveThresholdAt (fun ℓ => polynomialDiagonalHom w t (f ℓ)) h k
          (fun i => (x i).eval t / (x k).eval t) := by
        have hfun : (fun ℓ => polynomialDiagonalHom w t (f ℓ)) = fun ℓ =>
            MvPolynomial.C (t ^ polynomialExponentWeight w (p ℓ)) *
              (G ℓ).eval (MvPolynomial.C t) := funext hdiag
        rw [hfun]
        exact (projectiveThresholdAt_C_mul_iff (fun ℓ => (G ℓ).eval (MvPolynomial.C t))
          (fun ℓ => t ^ polynomialExponentWeight w (p ℓ)) (fun ℓ => pow_ne_zero _ ht) h k
          _).mpr hgood
      have h2 := projectiveThresholdAt_of_polynomialDiagonalHom f (fun ℓ => ⟨D ℓ, hD ℓ⟩) w ht h k
        _ h1
      -- the rescaled point is the original one
      have hpt : (fun i : {i : Fin n // i ≠ k} =>
          t ^ w i / t ^ w k * ((x i).eval t / (x k).eval t)) = p₀ := by
        funext i
        have hik : (i : Fin n) ≠ k := i.property
        rw [hxk]
        simp only [x, dite_eq_right hik, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X, Subtype.coe_eta]
        by_cases h0 : p₀ i = 0
        · rw [h0, zero_mul, zero_div, mul_zero]
        · have hwi : w i ≤ S.sup w := hMi i hik (by simpa only [Subtype.coe_eta] using h0)
          have e1 : t ^ w (i : Fin n) * t ^ (S.sup w - w i) = t ^ S.sup w := by
            rw [← pow_add, Nat.add_sub_cancel' hwi]
          have e2 : t ^ w k * t ^ (S.sup w - w k) = t ^ S.sup w := by
            rw [← pow_add, Nat.add_sub_cancel' hMk]
          rw [show t ^ w (i : Fin n) / t ^ w k * (p₀ i * t ^ (S.sup w - w i) /
              t ^ (S.sup w - w k)) = p₀ i * (t ^ w (i : Fin n) * t ^ (S.sup w - w i)) /
                (t ^ w k * t ^ (S.sup w - w k)) by ring, e1, e2, mul_div_assoc,
            div_self (pow_ne_zero _ ht), mul_one]
      rw [hpt] at h2
      exact h2
    obtain ⟨k', _, hbad'⟩ := harc n G D hGhom x h hx0 hgen
    apply hbad'
    have hC0 : (MvPolynomial.C (0 : K) : MvPolynomial (Fin n) K) = 0 := map_zero _
    have hz : ProjectiveThresholdAt (fun ℓ => (weightedPolynomialFamily w (p ℓ) (f ℓ)).eval 0) h k'
        (fun i => (x i).eval 0 / (x k').eval 0) := hzero k' _
    rw [hC0]
    exact hz

end Arc

section Freeness

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- F1 from sum KV, Lemma 3 at closed points, the closed-point realization hypothesis and lower
semicontinuity of the threshold along one arc; the degeneration statement is no longer
assumed. -/
theorem mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_closedPoints_and_arcSpecialization
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hlct : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (x : X), IsClosed ({x} : Set X) →
      IdealThresholdZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ))) x)
    (hpt : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (harc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      FormalThresholdArcSpecialization K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_closedPoints_and_degeneration hKV hlct hpt
    (fun K _ _ _ _ => thresholdDegenerationStatement_of_arcSpecialization (harc K))

/-- F1 from the usual KV, big plus nef, Lemma 3 at closed points, the closed-point realization
hypothesis and lower semicontinuity of the threshold along one arc. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_closedPoints_and_arcSpecialization
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hlct : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (x : X), IsClosed ({x} : Set X) →
      IdealThresholdZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ))) x)
    (hptc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (harc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      FormalThresholdArcSpecialization K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_closedPoints_and_degeneration hKV hba hlct
    hptc (fun K _ _ _ _ => thresholdDegenerationStatement_of_arcSpecialization (harc K))

end Freeness

end MixedFujita
