/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TangentSetPartitionBound
public import MixedFujita.SectionCentralSlice
public import MixedFujita.GradedPullbackTaylor
public import MixedFujita.TangentialMomentBound

/-!
The inequality (20) of section 5.3 for the Taylor data of a weight at a general closed point of
its centre, with the cube and the growth of the restricted sections as hypotheses.

Let η be the generic point of a component of the stratum of the members of positive weight, z a
point of a simple normal crossing chart in the closure of η with Taylor coordinates given by the
chart, whose selected coordinates are exactly those of the members of positive weight, and T a set
of d + 1 coordinates outside the family such that the pullbacks of the germs at π(η) have their
derivatives in the remaining coordinates outside the family in the maximal ideal of η (as provided
by `exists_closedPoint_tangent_chart_of_weight`). For a Cartier divisor A on the base with local
equation f at π(z):

* the coordinate weights are nonzero exactly on the coordinates of the members of positive weight;
* the sections of q A whose graded Taylor expansion has no coefficient at the exponents without
  crossing part are the sections vanishing at π(η), so these coefficients span a space of the
  dimension of the sections of q A restricted to the closure of π(η);
* if some sections of h₀ A have Taylor expansions which are units times the squarefree monomials
  in the coordinates of T (the cube) and the restricted dimensions of q A at π(η) satisfy the root
  bound with exponent d + 1, then (20) holds for the sums of exp(-ℓ(p)/θ) over the initial
  exponents, ℓ the old weight.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Weights

variable {r n : ℕ}

/-- The coordinate weights are nonzero exactly on the coordinates of the members of nonzero
weight. -/
theorem sncChartCoordinateWeights_ne_zero_iff {σc : Fin r → Option (Fin n)}
    (hinj : ∀ i j a, σc i = some a → σc j = some a → i = j) (w : Fin r → ℝ) (a : Fin n) :
    sncChartCoordinateWeights σc w a ≠ 0 ↔ ∃ k, w k ≠ 0 ∧ σc k = some a := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    apply h
    unfold sncChartCoordinateWeights
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : σc k = some a
    · rw [ite_eq_left hk]
      by_contra hw
      exact hcon k hw hk
    · rw [ite_eq_right hk]
  · rintro ⟨k, hk, hka⟩
    rw [sncChartCoordinateWeights_of_some hinj w hka]
    exact hk

end Weights

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]

omit [CharZero K] in
/-- The sections whose graded Taylor expansion has no coefficient at the exponents without
crossing part are the sections vanishing at π(η). -/
theorem ker_zeroSliceCoefficientMap_cartierGradedPullbackTaylor {r : ℕ} (ξ : Fin r → X)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (A : CartierDivisor Y) (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f) (q : ℕ) :
    LinearMap.ker (zeroSliceCoefficientMap
        {a : Fin n →₀ ℕ | ∀ i, (∃ k, w k ≠ 0 ∧ σc k = some i) → a i = 0}
        (cartierGradedPullbackTaylor π A z f hf ez q)) =
      cartierSectionsVanishingAt K (q • A) (π η) := by
  obtain ⟨u, hu, huT⟩ := cartierPullbackTaylorLinear_eq_unit_mul_graded π A z f hf ez q
  ext s
  rw [LinearMap.mem_ker, ← cartierPullbackTaylor_central_slice_eq_zero_iff π ξ c σc hc w η hη hwη
    hmax z hz hηz ez hez (q • A) s]
  have hs : cartierPullbackTaylor (q • A) π z ez s =
      u * cartierGradedPullbackTaylor π A z f hf ez q s := huT s
  rw [hs, map_mul, (hu.map (MvPowerSeries.rescale
    (stratumScale K {a | ∃ k, w k ≠ 0 ∧ σc k = some a}))).mul_right_eq_zero,
    rescale_stratumScale_eq_zero_iff]
  constructor
  · intro h e he
    exact congrFun h ⟨e, fun i hi => he i hi⟩
  · intro h
    funext a
    exact h a.1 (fun i hi => a.2 i hi)

omit [CharZero K] in
/-- The coefficients at the exponents without crossing part of the graded Taylor expansions of the
sections of q A span a space of the dimension of the sections restricted to the closure of
π(η). -/
theorem finrank_range_zeroSliceCoefficientMap_cartierGradedPullbackTaylor {r : ℕ}
    (ξ : Fin r → X) (c : EtaleChart K X n) (σc : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (A : CartierDivisor Y) (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f) (q : ℕ) :
    Module.finrank K (LinearMap.range (zeroSliceCoefficientMap
        {a : Fin n →₀ ℕ | ∀ i, (∃ k, w k ≠ 0 ∧ σc k = some i) → a i = 0}
        (cartierGradedPullbackTaylor π A z f hf ez q))) =
      cartierRestrictedDim K (q • A) (π η) := by
  rw [← (LinearMap.quotKerEquivRange (zeroSliceCoefficientMap
    {a : Fin n →₀ ℕ | ∀ i, (∃ k, w k ≠ 0 ∧ σc k = some i) → a i = 0}
    (cartierGradedPullbackTaylor π A z f hf ez q))).finrank_eq]
  exact (Submodule.quotEquivOfEq _ _ (ker_zeroSliceCoefficientMap_cartierGradedPullbackTaylor π ξ
    c σc hc w η hη hwη hmax z hz hηz ez hez A f hf q)).finrank_eq

/-- (20) for the Taylor data of a weight at a general closed point of its centre, given the cube
and the root bound for the restricted dimensions at π(η). -/
theorem sncWeight_partition_bound {r d : ℕ} (ξ : Fin r → X) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ)
    (hw0 : ∀ k, 0 ≤ w k) (η : X) (hη : η ∈ c.U)
    (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (hiff : ∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0)
    (Tan : Finset (Fin n)) (hTan : Tan.card = d + 1) (hTanfree : ∀ b ∈ Tan, ∀ k, σc k ≠ some b)
    (hsat : ∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ Tan →
      etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
        (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk η))
    (A : CartierDivisor Y) [∀ j : ℕ, FiniteDimensional K Γ((j • A).sheaf, ⊤)]
    (f : Y.functionFieldˣ) (hf : A.IsLocalEquationAt (π z) f)
    (m₀ : MonomialOrder (Fin n)) (v : Fin n → ℕ) (h₀ : ℕ)
    (hprod : ∀ s : Finset (Fin n), s ⊆ Tan → ∃ (x : Γ((h₀ • A).sheaf, ⊤))
      (u : MvPowerSeries (Fin n) K), MvPowerSeries.constantCoeff u ≠ 0 ∧
        cartierGradedPullbackTaylor π A z f hf ez h₀ x =
          u * MvPowerSeries.monomial (∑ i ∈ s, Finsupp.single i 1) 1)
    (s H : ℕ)
    (hroot : ∀ q ≥ H, (s : ℝ) * ((q : ℝ) + 1 - (s : ℝ) ^ (d + 1)) ≤
      (((d + 1).factorial * cartierRestrictedDim K (q • A) (π η) : ℕ) : ℝ) ^ ((d : ℝ) + 1)⁻¹)
    (hH : 0 < (s : ℝ) * H - (s : ℝ) * ((s : ℝ) ^ (d + 1) - 1))
    (l M : ℕ) (hl : 0 < l) (hM : l * (H + h₀ + s ^ (d + 1)) ≤ M) (θ : ℝ)
    (hQM : 0 < ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
        (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
        (LinearMap.range (cartierGradedPullbackTaylor π A z f hf ez M)),
      Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ)) :
    (d + 1 : ℝ) * (∑ i ∈ Finset.range l,
      (((s : ℝ) * (auxiliaryDegree M (i + 1) l - auxiliaryDegree M i l : ℕ) -
        ((s : ℝ) * ((s : ℝ) ^ (d + 1) - 1) + (s : ℝ) * h₀)) / M) *
          ((∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
              (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
              (LinearMap.range (cartierGradedPullbackTaylor π A z f hf ez
                (auxiliaryDegree M i l))),
            Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ)) /
            ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
              (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
              (LinearMap.range (cartierGradedPullbackTaylor π A z f hf ez M)),
            Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ))) ≤
      (∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
          (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
          (LinearMap.range (cartierGradedPullbackTaylor π A z f hf ez M)),
        Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ) *
          ∑ i ∈ Tan, (p i : ℝ)) /
          ((M : ℝ) * ∑ p ∈ initialMonomialFinset (weightedMonomialOrder m₀
            (sncChartCoordinateWeights σc w) v (sncChartCoordinateWeights_nonneg σc hw0))
            (LinearMap.range (cartierGradedPullbackTaylor π A z f hf ez M)),
          Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ)) +
        (d + 1 : ℝ) / M := by
  -- the coordinate weights vanish outside the crossing coordinates
  have hcr : ∀ i, sncChartCoordinateWeights σc w i ≠ 0 ↔ ∃ k, w k ≠ 0 ∧ σc k = some i :=
    sncChartCoordinateWeights_ne_zero_iff hc.1 w
  have hTan0 : ∀ i ∈ Tan, sncChartCoordinateWeights σc w i = 0 := by
    intro i hi
    by_contra hne
    obtain ⟨k, -, hk⟩ := (hcr i).mp hne
    exact hTanfree i hi k hk
  have hweight0 : ∀ a : Fin n →₀ ℕ, (∀ i, (∃ k, w k ≠ 0 ∧ σc k = some i) → a i = 0) →
      realExponentWeight (sncChartCoordinateWeights σc w) a = 0 := by
    intro a ha
    change ∑ i, sncChartCoordinateWeights σc w i * (a i : ℝ) = 0
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : sncChartCoordinateWeights σc w i = 0
    · rw [hi, zero_mul]
    · rw [ha i ((hcr i).mp hi), Nat.cast_zero, mul_zero]
  refine taylor_uniform_partition_bound_of_tangentSet Tan hTan _
    (fun j => cartierGradedPullbackTaylor π A z f hf ez j) (cartierGradedSectionProduct A)
    (cartierGradedPullbackTaylor_product π A z f hf ez)
    {a : Fin n →₀ ℕ | ∀ i, (∃ k, w k ≠ 0 ∧ σc k = some i) → a i = 0} ?_ ?_ ?_ h₀ hprod s H ?_ hH
    l M hl hM (fun p => Real.exp (-(realExponentWeight (sncChartCoordinateWeights σc w) p) / θ))
    (fun p => (Real.exp_pos _).le) ?_ hQM
  · -- the exponents without crossing part come first
    intro a ha b hb
    refine weightedMonomialOrder_zeroWeight_lt m₀ _ v _ (hweight0 a ha) ?_
    rw [Set.mem_ofPred_eq] at hb
    push Not at hb
    obtain ⟨i, hi, hbi⟩ := hb
    have hpos : 0 < sncChartCoordinateWeights σc w i :=
      lt_of_le_of_ne (sncChartCoordinateWeights_nonneg σc hw0 i) (Ne.symm ((hcr i).mpr hi))
    have hle : sncChartCoordinateWeights σc w i * (b i : ℝ) ≤
        realExponentWeight (sncChartCoordinateWeights σc w) b :=
      Finset.single_le_sum (f := fun j => sncChartCoordinateWeights σc w j * (b j : ℝ))
        (fun j _ => mul_nonneg (sncChartCoordinateWeights_nonneg σc hw0 j) (Nat.cast_nonneg _))
        (Finset.mem_univ i)
    have hbpos : (0 : ℝ) < (b i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hbi
    exact (lt_of_lt_of_le (mul_pos hpos hbpos) hle).ne'
  · -- the tangent exponents have no crossing part
    intro a ha i hi
    refine ha i fun hmem => ?_
    obtain ⟨k, -, hk⟩ := hi
    exact hTanfree i hmem k hk
  · -- the restriction to the stratum does not contain the fibre coordinates
    rintro j x a ha ⟨i, hi, hai⟩
    have hfree : ∀ k, σc k ≠ some i := by
      intro k hk
      exact hai (ha i ⟨k, (hiff k).mp ⟨i, hk⟩, hk⟩)
    exact stalkMap_taylor_coeff_eq_zero_of_saturated π ξ c σc hc w η hη hwη hmax z hz hηz ez hez
      i (fun h' => hsat h' i hfree hi)
      (cartierLocalCoefficient (j • A) (π z) (f ^ j) (cartierLocalEquation_pow A (π z) f hf j) x)
      a ha hai
  · -- the root bound
    intro q hq
    rw [finrank_range_zeroSliceCoefficientMap_cartierGradedPullbackTaylor π ξ c σc hc w η hη hwη
      hmax z hz hηz ez hez A f hf q]
    exact hroot q hq
  · -- the weight only depends on the part outside the tangent coordinates
    intro p q hpq
    have h1 : realExponentWeight (sncChartCoordinateWeights σc w) p =
        realExponentWeight (sncChartCoordinateWeights σc w) q := by
      change ∑ i, sncChartCoordinateWeights σc w i * (p i : ℝ) =
        ∑ i, sncChartCoordinateWeights σc w i * (q i : ℝ)
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : i ∈ Tan
      · rw [hTan0 i hi, zero_mul, zero_mul]
      · rw [hpq i hi]
    simp only [h1]

end MixedFujita
