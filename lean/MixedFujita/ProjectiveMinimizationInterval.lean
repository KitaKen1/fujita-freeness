/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveTestValuationBound
public import MixedFujita.MinimizationIntervalArithmetic

/-!
§3.1 of the manuscript for monomial test valuations on a smooth projective variety. The pulled-back
valuation of a sum is at least the minimum, and scalars do not lower it, so the sections with
v > c form a subspace. By Lemma 2 this subspace meets the subspace U of Lemma 2 only in 0, so
every basis of Γ(j J) has at least dim U ≥ κ h^0(j J) vectors with v ≤ A(v) ⌊j/(2b)⌋ ≤ j A(v)/(2t),
and the functional F_{j,t}(v, s) = (1/N) Σ_i exp(A(v)/t - v(s_i)/j) is at least κ exp(A(v)/(2t)),
the bound (8). By Lemma 1 every v(s_i) ≤ C j A(v), so F ≥ exp(A(v)/t - C A(v)), the bound (9).
Hence F ≤ 1 - δ/2 gives a_* ≤ A(v) ≤ a^* with a_* = -log(1 - δ/2)/C and a^* = 2 b log(1/κ), the
bound (10), and κ ≤ F always. The constants do not depend on j, t, the basis, the valuation or
the closed centre, and the threshold for j is uniform in the centre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Valuation

variable {K : Type u} [Field K] {T T' : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [T'.Over (Spec (CommRingCat.of K))] [IsIntegral T]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

omit [T.Over (Spec (CommRingCat.of K))] in
theorem cartierPullbackMonomialValuation_add (D : CartierDivisor T) (ρ : T' ⟶ T) (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) (s s' : Γ(D.sheaf, ⊤)) :
    min (cartierPullbackMonomialValuation D ρ p ep w s)
        (cartierPullbackMonomialValuation D ρ p ep w s') ≤
      cartierPullbackMonomialValuation D ρ p ep w (s + s') := by
  unfold cartierPullbackMonomialValuation
  rw [map_add, map_add, map_add]
  exact MvPowerSeries.min_weightedOrder_le_add w

theorem cartierStalkPullbackCoefficient_smul (D : CartierDivisor T) (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') (f : T.functionFieldˣ)
    (hf : D.IsLocalEquationAt (ρ p) f) (c : K) (s : Γ(D.sheaf, ⊤)) :
    cartierStalkPullbackCoefficient D ρ p f hf (c • s) =
      algebraMap K (T'.presheaf.stalk p) c * cartierStalkPullbackCoefficient D ρ p f hf s := by
  rw [cartierStalkPullbackCoefficient_apply, cartierStalkPullbackCoefficient_apply]
  change ρ.stalkMap p (cartierLocalCoefficient D (ρ p) f hf ((algebraMap K Γ(T, ⊤) c) • s)) = _
  rw [map_smul, Algebra.smul_def, map_mul]
  congr 1
  rw [← IsScalarTower.algebraMap_apply K Γ(T, ⊤) (T.presheaf.stalk (ρ p))]
  exact (schemeStalkMapAlgHom (K := K) ρ p).commutes c

/-- Scalars do not lower the pulled-back monomial valuation. -/
theorem cartierPullbackMonomialValuation_smul_ge (D : CartierDivisor T) (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) (c : K) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackMonomialValuation D ρ p ep w s ≤
      cartierPullbackMonomialValuation D ρ p ep w (c • s) := by
  unfold cartierPullbackMonomialValuation
  rw [cartierStalkPullbackCoefficient_smul, map_mul, map_mul]
  exact le_add_self.trans (MvPowerSeries.le_weightedOrder_mul w)

/-- The sections whose pulled-back valuation exceeds a finite threshold form a subspace. -/
noncomputable def cartierPullbackValuationAbove (D : CartierDivisor T) (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {n : ℕ}
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (w : Fin n → ℕ) (c : ℕ) : Submodule K Γ(D.sheaf, ⊤) where
  carrier := {s | (c : ℕ∞) < cartierPullbackMonomialValuation D ρ p ep w s}
  add_mem' := fun {s s'} hs hs' =>
    lt_of_lt_of_le (lt_min hs hs') (cartierPullbackMonomialValuation_add D ρ p ep w s s')
  zero_mem' := by
    change (c : ℕ∞) < cartierPullbackMonomialValuation D ρ p ep w 0
    unfold cartierPullbackMonomialValuation
    rw [map_zero, map_zero, map_zero, MvPowerSeries.weightedOrder_zero]
    exact ENat.natCast_lt_top c
  smul_mem' := fun a s hs =>
    lt_of_lt_of_le hs (cartierPullbackMonomialValuation_smul_ge D ρ p ep w a s)

end Valuation

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The log discrepancy Σ w + v(det J) of a test valuation. -/
noncomputable def testValuationLogDiscrepancy {T' : Scheme.{u}} [T'.Over (Spec (CommRingCat.of K))]
    (ρ : T' ⟶ Y) [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') {m : ℕ}
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
      (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K) (w : Fin m → ℕ) : ℕ∞ :=
  ((∑ i, w i : ℕ) : ℕ∞) +
    (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w

variable (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- Lemma 2 for test valuations with a threshold for j that does not depend on the centre. -/
theorem projectiveHyperplane_lemma2_testValuation_uniform
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) :
    ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ j : ℕ in atTop, ∀ x : Y, IsClosed {x} →
      ∃ U : Submodule K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        κ * (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ≤
          Module.finrank K U ∧
        ∀ s ∈ U, s ≠ 0 →
          cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x s ≤
              (⌊ε * j⌋₊ : ℕ∞) ∧
            ∀ (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
              [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
              (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
                (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
              (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
                (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
              (w : Fin m → ℕ),
                cartierPullbackMonomialValuation (j • projectiveHyperplaneCartier e g hg hggen)
                    ρ p ep w s ≤
                  testValuationLogDiscrepancy ρ p ez ep w * (⌊ε * j⌋₊ : ℕ∞) := by
  intro ε hε
  obtain ⟨c, hc⟩ := projectiveHyperplane_subspace_valuation_le e g hg hggen he hn hd
  obtain ⟨r, hr, -, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  set θ : ℝ := min 1 (ε / ((c : ℝ) + 1)) with hθdef
  have hc1 : (0 : ℝ) < (c : ℝ) + 1 := by positivity
  have hθ : 0 < θ := lt_min one_pos (div_pos hε hc1)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθc : ((c : ℝ) + 1) * θ ≤ ε := by
    have h := min_le_right 1 (ε / ((c : ℝ) + 1))
    rw [← hθdef] at h
    calc ((c : ℝ) + 1) * θ ≤ ((c : ℝ) + 1) * (ε / ((c : ℝ) + 1)) := by gcongr
      _ = ε := by field_simp
  have hℓ : (0 : ℝ) < r / d.factorial := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hratio := tendsto_ratio_floor_of_tendsto_div_pow hℓ hlim hθ
  refine ⟨θ ^ d / 2, by positivity, ?_⟩
  have hev1 := hratio.eventually (lt_mem_nhds (half_lt_self (pow_pos hθ d)))
  have hev2 : ∀ᶠ j : ℕ in atTop, 1 ≤ ⌊θ * j⌋₊ :=
    (tendsto_nat_floor_mul_atTop θ hθ).eventually (eventually_ge_atTop 1)
  filter_upwards [hev1, hev2] with j h1 h2
  have hfloor : (⌊θ * (j : ℝ)⌋₊ : ℝ) ≤ θ * j := Nat.floor_le (by positivity)
  have hqj : ⌊θ * (j : ℝ)⌋₊ ≤ j := by
    have h : (⌊θ * (j : ℝ)⌋₊ : ℝ) ≤ j :=
      hfloor.trans (mul_le_of_le_one_left (Nat.cast_nonneg j) hθ1)
    exact_mod_cast h
  generalize ⌊θ * (j : ℝ)⌋₊ = q at h1 h2 hfloor hqj
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hqj
  intro x hx
  obtain ⟨U, hU, hUval⟩ := hc x hx a q h2
  have h3 : ((c * q : ℕ) : ℝ) ≤ ε * ((a + q : ℕ) : ℝ) := by
    push_cast at hfloor ⊢
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have haq : (0 : ℝ) ≤ (a : ℝ) + q := by positivity
    calc (c : ℝ) * q ≤ ((c : ℝ) + 1) * q := by nlinarith
      _ ≤ ((c : ℝ) + 1) * (θ * ((a : ℝ) + q)) := by gcongr
      _ = (((c : ℝ) + 1) * θ) * ((a : ℝ) + q) := by ring
      _ ≤ ε * ((a : ℝ) + q) := by gcongr
  have h4 : ((c * q : ℕ) : ℕ∞) ≤ (⌊ε * ((a + q : ℕ) : ℝ)⌋₊ : ℕ∞) := by
    exact_mod_cast Nat.le_floor h3
  refine ⟨U, ?_, ?_⟩
  · rw [hU]
    have hNpos : (0 : ℝ) < (Module.finrank K
        Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) := by
      rcases (Nat.cast_nonneg (α := ℝ) (Module.finrank K
        Γ(((a + q) • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))).lt_or_eq with h | h
      · exact h
      · rw [← h, div_zero] at h1
        have : (0 : ℝ) < θ ^ d / 2 := by positivity
        linarith
    have h1' := (lt_div_iff₀ hNpos).mp h1
    linarith
  · intro s hs hs0
    obtain ⟨hord, hval⟩ := hUval s hs hs0
    refine ⟨hord.trans h4, fun T' _ ρ _ p hpx m ez ep w => ?_⟩
    exact (hval T' ρ p hpx ez ep w).trans (mul_le_mul_right h4 _)

/-- The bounds (8) and (9) of §3.1 for test valuations: one κ > 0 and one C > 0 such that for all
large j, every closed centre x, every basis of Γ(j·J), every test valuation v over x with finite
A(v) and every 0 < t ≤ b, the functional F_{j,t}(v, s) is at least κ exp(A(v)/(2t)) and at least
exp(A(v)/t - C A(v)). -/
theorem projectiveHyperplane_minimization_bounds
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ∧
      ∀ x : Y, IsClosed {x} →
      ∀ (bs : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
        (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
        [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
        (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
          (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
        (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
          (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
        (w : Fin m → ℕ), testValuationLogDiscrepancy ρ p ez ep w ≠ ⊤ →
        ∀ t : ℝ, 0 < t → t ≤ b →
          κ * Real.exp (((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) / (2 * t)) ≤
              minimizationFunctional j t ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ)
                (fun i => ((cartierPullbackMonomialValuation
                  (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w (bs i)).toNat : ℝ)) ∧
            Real.exp (((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) / t -
                C * ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ)) ≤
              minimizationFunctional j t ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ)
                (fun i => ((cartierPullbackMonomialValuation
                  (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w (bs i)).toNat : ℝ)) := by
  set ε : ℝ := 1 / (2 * b) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨κ, hκ, hL2⟩ := projectiveHyperplane_lemma2_testValuation_uniform e g hg hggen he hn hd ε hε
  obtain ⟨c₁, hL1⟩ := projectiveHyperplane_lemma1_testValuation e g hg hggen he hn hd
  obtain ⟨r, hr, -, hlim⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hn hd
  have hℓ : (0 : ℝ) < r / d.factorial := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    positivity
  have hNev : ∀ᶠ j : ℕ in atTop,
      0 < Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    filter_upwards [hlim.eventually (lt_mem_nhds (half_lt_self hℓ))] with j hj
    rcases Nat.eq_zero_or_pos (Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) with h | h
    · rw [h, Nat.cast_zero, zero_div] at hj
      linarith
    · exact h
  refine ⟨κ, hκ, (c₁ : ℝ) + 1, by positivity, ?_⟩
  filter_upwards [hL2, hNev, eventually_ge_atTop 1] with j hU hN hj
  refine ⟨hN, fun x hx bs T' _ ρ _ p hpx m ez ep w hA t ht htb => ?_⟩
  obtain ⟨U, hUdim, hUval⟩ := hU x hx
  set A := testValuationLogDiscrepancy ρ p ez ep w with hAdef
  set Aℕ := A.toNat with hAℕ
  have hAeq : (Aℕ : ℕ∞) = A := ENat.natCast_toNat hA
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hxc : IsClosed {ρ p} := by rw [hpx]; exact hx
  set cv : ℕ := Aℕ * ⌊ε * (j : ℝ)⌋₊ with hcv
  set W := cartierPullbackValuationAbove (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w cv
    with hW
  have hUW : U ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hsU, hsW⟩
    by_contra hs0
    have hv := (hUval s hsU hs0).2 T' ρ p hpx ez ep w
    rw [← hAdef, ← hAeq] at hv
    have hsW' : (cv : ℕ∞) < cartierPullbackMonomialValuation
        (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w s := hsW
    have : (cv : ℕ∞) = (Aℕ : ℕ∞) * (⌊ε * (j : ℝ)⌋₊ : ℕ∞) := by
      rw [hcv]
      push_cast
      rfl
    rw [this] at hsW'
    exact absurd hv (not_le.mpr hsW')
  have : FiniteDimensional K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
    Module.Finite.of_basis bs
  obtain ⟨S, hSU, hSW⟩ := basis_exists_card_not_mem bs U W hUW
  set vals : Fin (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℝ :=
    fun i => ((cartierPullbackMonomialValuation
      (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w (bs i)).toNat : ℝ) with hvals
  -- the bound (8)
  have hthr : ∀ i, bs i ∉ W → vals i ≤ (j : ℝ) * Aℕ / (2 * t) := by
    intro i hi
    have hle : cartierPullbackMonomialValuation (j • projectiveHyperplaneCartier e g hg hggen)
        ρ p ep w (bs i) ≤ (cv : ℕ∞) := not_lt.mp hi
    have h1 : (vals i : ℝ) ≤ (cv : ℝ) := by
      simp only [hvals]
      exact_mod_cast ENat.toNat_le_of_le_natCast hle
    have hfl : (⌊ε * (j : ℝ)⌋₊ : ℝ) ≤ ε * j := Nat.floor_le (by positivity)
    have hA0 : (0 : ℝ) ≤ Aℕ := Nat.cast_nonneg _
    have h2 : (cv : ℝ) ≤ (Aℕ : ℝ) * (ε * j) := by
      rw [hcv]
      push_cast
      exact mul_le_mul_of_nonneg_left hfl hA0
    have h3 : (Aℕ : ℝ) * (ε * j) ≤ (j : ℝ) * Aℕ / (2 * t) := by
      rw [hεdef]
      have hbt : 1 / (2 * b) ≤ 1 / (2 * t) := one_div_le_one_div_of_le (by positivity) (by linarith)
      calc (Aℕ : ℝ) * (1 / (2 * b) * j) ≤ (Aℕ : ℝ) * (1 / (2 * t) * j) := by gcongr
        _ = (j : ℝ) * Aℕ / (2 * t) := by ring
    linarith
  have hcount2 : Module.finrank K U ≤
      (Finset.univ.filter (fun i => vals i ≤ (j : ℝ) * Aℕ / (2 * t))).card :=
    hSU.trans (Finset.card_le_card (fun i hi =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, hthr i (hSW i hi)⟩))
  have hcount' : κ * (Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) ≤
        ((Finset.univ.filter (fun i => vals i ≤ (j : ℝ) * Aℕ / (2 * t))).card : ℝ) := by
    have h2 : (Module.finrank K U : ℝ) ≤
        ((Finset.univ.filter (fun i => vals i ≤ (j : ℝ) * Aℕ / (2 * t))).card : ℝ) := by
      exact_mod_cast hcount2
    linarith
  have h8 := minimizationFunctional_ge_of_count hN j (t := t) (A := (Aℕ : ℝ)) vals hcount'
  have hsimp : (Aℕ : ℝ) / t - (j : ℝ) * Aℕ / (2 * t) / j = (Aℕ : ℝ) / (2 * t) := by
    field_simp
    ring
  rw [hsimp] at h8
  -- the bound (9)
  have hall : ∀ i, vals i ≤ ((c₁ : ℝ) + 1) * j * Aℕ := by
    intro i
    have hv := hL1 T' ρ p hxc ez ep w j hj (bs i) (bs.ne_zero i)
    change cartierPullbackMonomialValuation _ ρ p ep w (bs i) ≤ A * _ at hv
    rw [← hAeq] at hv
    have hv' : cartierPullbackMonomialValuation (j • projectiveHyperplaneCartier e g hg hggen)
        ρ p ep w (bs i) ≤ ((Aℕ * (c₁ * j) : ℕ) : ℕ∞) := by
      push_cast
      exact hv
    have h1 : (vals i : ℝ) ≤ ((Aℕ * (c₁ * j) : ℕ) : ℝ) := by
      simp only [hvals]
      exact_mod_cast ENat.toNat_le_of_le_natCast hv'
    have hA0 : (0 : ℝ) ≤ Aℕ := Nat.cast_nonneg _
    have hj0' : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    push_cast at h1
    nlinarith
  have h9 := minimizationFunctional_ge_of_all hN j (t := t) (A := (Aℕ : ℝ)) vals hall
  have hsimp9 : (Aℕ : ℝ) / t - ((c₁ : ℝ) + 1) * j * Aℕ / j = (Aℕ : ℝ) / t - ((c₁ : ℝ) + 1) * Aℕ := by
    field_simp
  rw [hsimp9] at h9
  exact ⟨h8, h9⟩

/-- The bound (10) of §3.1: on F_{j,t} ≤ 1 - δ/2 the log discrepancy lies in a fixed interval
[a_*, a^*] with 0 < a_*, and κ ≤ F always; the constants do not depend on j, t, the basis, the
valuation or the centre. -/
theorem projectiveHyperplane_minimization_interval
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    {d : ℕ} (hn : topologicalKrullDim Y = d) (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop, ∀ x : Y, IsClosed {x} →
      ∀ (bs : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
        (T' : Scheme.{u}) [T'.Over (Spec (CommRingCat.of K))] (ρ : T' ⟶ Y)
        [ρ.IsOver (Spec (CommRingCat.of K))] (p : T'), ρ p = x → ∀ {m : ℕ}
        (ez : AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk (ρ p)))
          (Y.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin m) K)
        (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
          (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin m) K)
        (w : Fin m → ℕ), testValuationLogDiscrepancy ρ p ez ep w ≠ ⊤ →
        ∀ t : ℝ, 0 < t → t ≤ b →
          κ ≤ minimizationFunctional j t ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ)
              (fun i => ((cartierPullbackMonomialValuation
                (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w (bs i)).toNat : ℝ)) ∧
          ∀ δ : ℝ, 0 < δ → δ < 2 →
            minimizationFunctional j t ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ)
                (fun i => ((cartierPullbackMonomialValuation
                  (j • projectiveHyperplaneCartier e g hg hggen) ρ p ep w (bs i)).toNat : ℝ)) ≤
              1 - δ / 2 →
            -Real.log (1 - δ / 2) / C ≤ ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) ∧
              ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) ≤ 2 * b * Real.log (1 / κ) := by
  obtain ⟨κ, hκ, C, hC, hev⟩ := projectiveHyperplane_minimization_bounds e g hg hggen he hn hd hb
  refine ⟨κ, hκ, C, hC, ?_⟩
  filter_upwards [hev] with j hj
  intro x hx bs T' _ ρ _ p hpx m ez ep w hA t ht htb
  obtain ⟨h8, h9⟩ := hj.2 x hx bs T' ρ p hpx ez ep w hA t ht htb
  have hA0 : (0 : ℝ) ≤ ((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, fun δ hδ hδ2 hF => logDiscrepancy_bounds_of_functional hκ hC hδ hδ2 hA0 ht htb h8 h9 hF⟩
  have hexp : 1 ≤ Real.exp (((testValuationLogDiscrepancy ρ p ez ep w).toNat : ℝ) / (2 * t)) :=
    Real.one_le_exp (div_nonneg hA0 (by positivity))
  nlinarith

end MixedFujita
