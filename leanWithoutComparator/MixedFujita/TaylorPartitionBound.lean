/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SliceRestrictionCount
public import MixedFujita.FiniteDegree

/-!
The inequality (20) of §5.3 for actual Taylor data with the restriction to W. The exponent sets
Γ_j of the Taylor maps form a graded semigroup; the central slices satisfy
#G_0(q) ≥ dim (restriction image) and contain the cube {0,1}^(d+1) in degree h₀ (§5.2), so the
root bound (13) for the restriction image gives the slice growth (17) and the moment growth (18);
the simplex moment bound (19) at degree m closes the telescoping sum. The result is
(d+1) Σ_i ((s (j_{i+1} - j_i) - C')/m) (Q_{j_i}/Q_m) ≤ T_m/(m Q_m) + (d+1)/m, with Q the weighted
slice counts and T the weighted tangential sum, for any increasing partition degrees j_i with
j_k = m whose steps are long enough.
-/

@[expose] public section

namespace MixedFujita

variable {K : Type*} [Field K] {r d : ℕ} {V : ℕ → Type*} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)] [∀ j, FiniteDimensional K (V j)]

/-- (20) for actual Taylor data, with the central-slice input coming from the restriction to W. -/
theorem taylor_partition_moment_bound_of_restriction
    (m : MonomialOrder (Fin r ⊕ Fin (d + 1)))
    (T : ∀ j, V j →ₗ[K] MvPowerSeries (Fin r ⊕ Fin (d + 1)) K)
    (μ : ∀ j h, V j → V h → V (j + h))
    (hT : ∀ j h x y, T (j + h) (μ j h x y) = T j x * T h y)
    (R : ∀ j, V j →ₗ[K] MvPowerSeries (Fin (d + 1)) K)
    (Z : Set ((Fin r ⊕ Fin (d + 1)) →₀ ℕ))
    (hZ : ∀ a ∈ Z, ∀ b, b ∉ Z → m.toSyn a < m.toSyn b)
    (htan : ∀ β, tangentExponent r β ∈ Z)
    (hcoef : ∀ j x β, MvPowerSeries.coeff (tangentExponent r β) (T j x) =
      MvPowerSeries.coeff β (R j x))
    (hzero : ∀ j x, ∀ a ∈ Z, (∃ i, a (Sum.inl i) ≠ 0) → MvPowerSeries.coeff a (T j x) = 0)
    (h₀ : ℕ)
    (hprod : ∀ s : Finset (Fin (d + 1)), ∃ (x : V h₀) (u : MvPowerSeries (Fin r ⊕ Fin (d + 1)) K),
      MvPowerSeries.constantCoeff u ≠ 0 ∧
        T h₀ x = u * MvPowerSeries.monomial (tangentExponent r (∑ i ∈ s, Finsupp.single i 1)) 1)
    (s H : ℕ)
    (hroot : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * Module.finrank K (LinearMap.range (R q)) : ℕ) : ℝ) ^
        ((d : ℝ) + 1)⁻¹)
    (hH : 0 < (s : ℝ) * H - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1))
    (j : ℕ → ℕ) (k M : ℕ) (hM : 0 < M) (hj : Monotone j) (hjM : j k = M)
    (w : (Fin r → ℤ) → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hstep : ∀ i < k, H + h₀ ≤ j (i + 1) - j i)
    (hr : ∀ i < k, 0 ≤ (s : ℝ) * (j (i + 1) - j i : ℕ) -
      ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀))
    (hQM : 0 < weightedSliceCount (taylorExponentPoints m T) M w) :
    (d + 1 : ℝ) * (∑ i ∈ Finset.range k,
      (((s : ℝ) * (j (i + 1) - j i : ℕ) - ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀)) /
        M) * (weightedSliceCount (taylorExponentPoints m T) (j i) w /
          weightedSliceCount (taylorExponentPoints m T) M w)) ≤
      weightedTangentialSum (taylorExponentPoints m T) M w /
          ((M : ℝ) * weightedSliceCount (taylorExponentPoints m T) M w) +
        (d + 1 : ℝ) / M :=
  slice_partition_moment_bound (taylorExponentPoints m T)
    (taylorExponentPoints_semigroup m T μ hT) H h₀
    (taylor_binaryVectors_subset_zeroSlice m T h₀ hprod) (Nat.cast_nonneg s) hH
    (fun q hq => zeroSlice_radius_lower_of_root _
      (taylor_zeroSlice_card_ge m T R Z hZ htan hcoef hzero q) (hroot q hq))
    j k M hM hj hjM w hw hstep hr hQM
    (fun p _ _ hγ => taylor_exponentSlice_nonneg m T M p hγ)

end MixedFujita
