/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveConeFormalTest
public import MixedFujita.AffineMonomialModelThreshold

/-!
The degeneration form of Lemma 3 from Lemma 3 in the model form on affine space (step 9).

Lemma 3 in the model form on affine space (`AffineLemmaThreeStatement`): for polynomials G_j in
the coordinates x of A^N and parameters c of A^r and an integer M ≥ 1, the set of (x, c) at which
some prime divisor over A^N with centre containing x has ord(G_j(·, c)) ≥ M A for every nonzero
G_j(·, c) is Zariski closed. This is the lower semicontinuity of the log canonical threshold of
the ideal of the G_j(·, c) in (x, c). It is a definition, used as a hypothesis; it is not proved
here.

The degeneration statement follows. If (34) fails for the forms f_ℓ at a point P of a chart, it
fails for F(t) at the arc x(t) = [t^(M - w_i) P_i] for every t ≠ 0 (as in
`thresholdDegenerationStatement_of_arcSpecialization`), so the threshold fails in the model form
at the point x(t) of the affine cone A^n (`affineSpace_modelThresholdBadAt_of_projectiveThresholdBadAt`:
the chart test lifted to the cone by the identity in the cone parameter, then compared with
actual divisors). The family F(t) is one polynomial family on A^n × A^1; Lemma 3 makes the bad
set the zero set of an ideal, and a polynomial vanishing along the arc for t ≠ 0 vanishes at
t = 0, so the threshold fails in the model form at x(0) ≠ 0 for the initial monomials. That
contradicts (34) for the initial monomials, which gives the chart inequality at x(0), under
which monomials satisfy the threshold in the model form
(`affineSpace_monomials_not_modelThresholdBadAt`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology MvPowerSeries
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace MixedFujita

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

attribute [local instance] specAlgebraOver affineSpace_smoothOfRelativeDimension

section Statement

/-- Lemma 3 in the model form on affine space: for polynomials G_j in the coordinates x of A^N
and the parameters c of A^r and an integer M ≥ 1, the set of (x, c) where the threshold of the
ideal of the G_j(·, c) at x is at most 1/M (some prime divisor over A^N with centre containing x
has ord ≥ M A on every nonzero G_j(·, c)) is the zero set of an ideal. It is the lower
semicontinuity of the log canonical threshold in families. It is a definition, used as a
hypothesis; it is not proved here. -/
def AffineLemmaThreeStatement (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] : Prop :=
  ∀ (N r : ℕ) {J : Type} [Finite J] (G : J → MvPolynomial (Fin N ⊕ Fin r) K) (M : ℕ), 1 ≤ M →
    ∃ I : Ideal (MvPolynomial (Fin N ⊕ Fin r) K), ∀ (x : Fin N → K) (c : Fin r → K),
      (ModelThresholdBadAt (affineSpaceEtaleChart K N) 1 1
        (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K N) +
          principalCartierDivisor (affineSpace K N) 1))
        (affineSpacePoint K N x)
        (fun j => etaleChartFunctionFieldCoords (affineSpaceEtaleChart K N)
          (MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (c i))) (G j)))
        M ↔ ∀ g ∈ I, MvPolynomial.eval (Sum.elim x c) g = 0)

end Statement

section Arc

variable {K : Type*} [Field K]

/-- A polynomial vanishing along a polynomial arc for t ≠ 0 vanishes at t = 0. -/
theorem mvPolynomial_eval_zero_of_arc [Infinite K] {N r : ℕ}
    (g : MvPolynomial (Fin N ⊕ Fin r) K) (γ : Fin N → Polynomial K) (δ : Fin r → Polynomial K)
    (hg : ∀ t : K, t ≠ 0 →
      MvPolynomial.eval (Sum.elim (fun i => (γ i).eval t) (fun j => (δ j).eval t)) g = 0) :
    MvPolynomial.eval (Sum.elim (fun i => (γ i).eval 0) (fun j => (δ j).eval 0)) g = 0 := by
  set Q : Polynomial K := MvPolynomial.aeval (Sum.elim γ δ) g with hQ
  have hQt : ∀ t : K, Q.eval t =
      MvPolynomial.eval (Sum.elim (fun i => (γ i).eval t) (fun j => (δ j).eval t)) g := by
    intro t
    rw [hQ, ← congrFun (Polynomial.coe_aeval_eq_eval t) _, MvPolynomial.comp_aeval_apply,
      MvPolynomial.aeval_eq_eval]
    congr 2
    funext i
    cases i with
    | inl i => simp [Polynomial.coe_aeval_eq_eval]
    | inr j => simp [Polynomial.coe_aeval_eq_eval]
  have hQ0 : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (fun t ht => ?_) (Set.finite_singleton (0 : K)).infinite_compl
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    show Q.IsRoot t
    rw [Polynomial.IsRoot.def, hQt, hg t ht]
  rw [← hQt 0, hQ0, Polynomial.eval_zero]

/-- A polynomial family in one parameter as one polynomial on A^n × A^1. -/
noncomputable def polynomialFamilyTotal {n : ℕ} (G : Polynomial (MvPolynomial (Fin n) K)) :
    MvPolynomial (Fin n ⊕ Fin 1) K :=
  G.eval₂ (MvPolynomial.rename Sum.inl).toRingHom (MvPolynomial.X (Sum.inr 0))

theorem aeval_polynomialFamilyTotal {n : ℕ} (G : Polynomial (MvPolynomial (Fin n) K))
    (c : Fin 1 → K) :
    MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun i => MvPolynomial.C (c i)))
        (polynomialFamilyTotal G) = G.eval (MvPolynomial.C (c 0)) := by
  unfold polynomialFamilyTotal
  induction G using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, map_add, hp, hq, Polynomial.eval_add]
  | monomial k a =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval_monomial, map_mul, map_pow,
      MvPolynomial.aeval_X]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_rename,
      Sum.elim_comp_inl, MvPolynomial.aeval_X_left_apply, Sum.elim_inr]

end Arc

section Degeneration

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K]

/-- The degeneration form of Lemma 3 from Lemma 3 in the model form on affine space. -/
theorem thresholdDegenerationStatement_of_affineLemmaThree (hL : AffineLemmaThreeStatement K) :
    ThresholdDegenerationStatement K := by
  classical
  intro n ι _ w p f h hhom hp huniq hzero
  by_cases hf : ProjectiveThresholdCondition f h
  · refine ⟨1, one_ne_zero, ?_⟩
    have h1 : ∀ ℓ, (weightedPolynomialFamily w (p ℓ) (f ℓ)).eval (MvPolynomial.C 1) = f ℓ := by
      intro ℓ
      rw [map_one, weightedPolynomialFamily_at_one]
    simpa only [h1] using hf
  · exfalso
    have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
    rw [projectiveThresholdCondition_iff_forall_at] at hf
    push Not at hf
    obtain ⟨k, p₀, hbad⟩ := hf
    -- the special fibre is tested at a test where (34) fails for the forms: ι ≠ ∅ and h ≥ 1
    have hbad' := hbad
    unfold ProjectiveThresholdAt at hbad'
    push Not at hbad'
    obtain ⟨ψ, hψ, hdet, wt, hwt, -⟩ := hbad'
    obtain ⟨ℓ₀, hℓ₀⟩ := hzero k p₀ ψ hψ hdet wt hwt
    have hh : 1 ≤ h := by
      by_contra h0
      have h00 : h = 0 := by omega
      rw [h00, Nat.cast_zero, zero_mul] at hℓ₀
      exact absurd hℓ₀ (not_lt.mpr zero_le)
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
    -- F(t) = t^(-⟨w,p⟩) · diag_t f
    have hdiag : ∀ ℓ (t : K), polynomialDiagonalHom w t (f ℓ) =
        MvPolynomial.C (t ^ polynomialExponentWeight w (p ℓ)) *
          (G ℓ).eval (MvPolynomial.C t) := by
      intro ℓ t
      refine (weightedPolynomialFamily_scaled_parameter w (p ℓ) (f ℓ) t fun q hq => ?_).symm
      by_cases hqp : q = p ℓ
      · rw [hqp]
      · exact (huniq ℓ q hq hqp).le
    have hgen : ∀ t : K, t ≠ 0 → ProjectiveThresholdBadAt
        (fun ℓ => (G ℓ).eval (MvPolynomial.C t)) h (fun i => (x i).eval t) := by
      intro t ht
      have hxk : (x k).eval t = t ^ (S.sup w - w k) := by
        simp only [x, dite_eq_left rfl, Polynomial.eval_pow, Polynomial.eval_X]
      refine ⟨k, ?_, fun hgood => hbad ?_⟩
      · show (x k).eval t ≠ 0
        rw [hxk]
        exact pow_ne_zero _ ht
      have h1 : ProjectiveThresholdAt (fun ℓ => polynomialDiagonalHom w t (f ℓ)) h k
          (fun i => (x i).eval t / (x k).eval t) := by
        have hfun : (fun ℓ => polynomialDiagonalHom w t (f ℓ)) = fun ℓ =>
            MvPolynomial.C (t ^ polynomialExponentWeight w (p ℓ)) *
              (G ℓ).eval (MvPolynomial.C t) := funext fun ℓ => hdiag ℓ t
        rw [hfun]
        exact (projectiveThresholdAt_C_mul_iff (fun ℓ => (G ℓ).eval (MvPolynomial.C t))
          (fun ℓ => t ^ polynomialExponentWeight w (p ℓ)) (fun ℓ => pow_ne_zero _ ht) h k
          _).mpr hgood
      have h2 := projectiveThresholdAt_of_polynomialDiagonalHom f (fun ℓ => ⟨D ℓ, hD ℓ⟩) w ht h k
        _ h1
      have hpt : (fun i : {i : Fin n // i ≠ k} =>
          t ^ w i / t ^ w k * ((x i).eval t / (x k).eval t)) = p₀ := by
        funext i
        have hik : (i : Fin n) ≠ k := i.property
        rw [hxk]
        simp only [x, dite_eq_right hik, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, Subtype.coe_eta]
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
    -- the threshold fails in the model form along the arc in the affine cone
    have hGne : ∀ ℓ (t : K), t ≠ 0 → (G ℓ).eval (MvPolynomial.C t) ≠ 0 := by
      intro ℓ t ht h0
      have hf0 : f ℓ ≠ 0 := fun hf0 => by
        have hmem := hp ℓ
        rw [hf0, MvPolynomial.support_zero] at hmem
        exact Finset.notMem_empty _ hmem
      have h1 := hdiag ℓ t
      rw [h0, mul_zero] at h1
      have h2 := polynomialDiagonalHom_inverse w ht (f ℓ)
      rw [h1, map_zero] at h2
      exact hf0 h2.symm
    have hmodel : ∀ t : K, t ≠ 0 → ModelThresholdBadAt (affineSpaceEtaleChart K n) 1 1
        (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K n) +
          principalCartierDivisor (affineSpace K n) 1))
        (affineSpacePoint K n (fun i => (x i).eval t))
        (fun ℓ => etaleChartFunctionFieldCoords (affineSpaceEtaleChart K n)
          ((G ℓ).eval (MvPolynomial.C t))) h := fun t ht =>
      affineSpace_modelThresholdBadAt_of_projectiveThresholdBadAt
        (fun ℓ => (G ℓ).eval (MvPolynomial.C t)) D (fun ℓ => hGhom ℓ t) ⟨ℓ₀, hGne ℓ₀ t ht⟩ h hh
        _ (hgen t ht)
    -- Lemma 3: the bad set of the family on A^n × A^1 is closed, so it contains (x(0), 0)
    obtain ⟨I, hI⟩ := hL n 1 (fun ℓ => polynomialFamilyTotal (G ℓ)) h hh
    have hI0 : ∀ g ∈ I, MvPolynomial.eval
        (Sum.elim (fun i => (x i).eval 0) (fun _ : Fin 1 => (0 : K))) g = 0 := by
      intro g hg
      have harc := mvPolynomial_eval_zero_of_arc g x (fun _ => Polynomial.X) (fun t ht => by
        have hb := (hI (fun i => (x i).eval t) (fun _ => t)).mp
          (by simpa only [aeval_polynomialFamilyTotal] using hmodel t ht) g hg
        simpa only [Polynomial.eval_X] using hb)
      simpa only [Polynomial.eval_X] using harc
    have hbad0 := (hI (fun i => (x i).eval 0) (fun _ => 0)).mpr hI0
    simp only [aeval_polynomialFamilyTotal] at hbad0
    simp only [map_zero] at hbad0
    -- the special fibre consists of the initial monomials
    have hzero' : ∀ ℓ, (G ℓ).eval 0 = MvPolynomial.monomial (p ℓ) ((f ℓ).coeff (p ℓ)) :=
      fun ℓ => weightedPolynomialFamily_at_zero w (p ℓ) (f ℓ) (hp ℓ) (huniq ℓ)
    simp only [G, hzero'] at hbad0
    have hcond : ProjectiveThresholdCondition
        (fun ℓ => MvPolynomial.monomial (p ℓ) ((f ℓ).coeff (p ℓ))) h := by
      have h1 := hzero
      simp only [G, hzero'] at h1 ⊢
      exact h1
    have : Nonempty ι := ⟨ℓ₀⟩
    obtain ⟨i₁, hi₁⟩ := hx0
    exact affineSpace_monomials_not_modelThresholdBadAt p (fun ℓ => (f ℓ).coeff (p ℓ))
      (fun ℓ => MvPolynomial.mem_support_iff.mp (hp ℓ)) _ h hh
      (fun u hu0 hu => monomial_chart_inequality_of_projectiveThresholdCondition p _ h hcond _ i₁
        hi₁ u hu0 hu) hbad0

end Degeneration

section Freeness

/-- F1 from sum KV, Lemma 3 at closed points, the closed-point realization hypothesis and Lemma 3
in the model form on affine space; neither the degeneration statement nor the formal arc
statement is assumed. -/
theorem mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_closedPoints_and_affineLemmaThree
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
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], AffineLemmaThreeStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_closedPoints_and_degeneration hKV hlct hpt
    (fun K _ _ _ _ => thresholdDegenerationStatement_of_affineLemmaThree (hL3 K))

/-- F1 from the usual KV, big plus nef, Lemma 3 at closed points, the closed-point realization
hypothesis and Lemma 3 in the model form on affine space. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_closedPoints_and_affineLemmaThree
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
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], AffineLemmaThreeStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_closedPoints_and_degeneration hKV hba hlct
    hptc (fun K _ _ _ _ => thresholdDegenerationStatement_of_affineLemmaThree (hL3 K))

end Freeness

end MixedFujita
