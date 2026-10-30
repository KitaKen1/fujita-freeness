/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TaylorTestProfiles
public import MixedFujita.RealWeightedValuation

/-!
Weights on a simple normal crossing model are monomial Taylor tests, and a lower bound for the
objective over the profile data is a lower bound for the objective of the Taylor tests (step 11,
section 5.1 of the manuscript).

* On a simple normal crossing chart at a point z with Taylor coordinates the coordinates of the
  chart, for a nonzero section s of a Cartier divisor of the base whose pulled back zero divisor
  is supported on the family, the real weighted order of the Taylor expansion at z of the pullback
  of s is linear in the weights: v_u(s) = Σ_j ord_{ξ_j}(π^* div s) u_{a(j)}. So a weight on the
  members of the family through z, read as weights on the coordinates of the chart, has the same
  values on the sections of the tuple of the model as the weight itself.
* Comparison. If L is a lower bound for the objective Σ_i exp(a/t − v_i/j) over the profile data
  (a, v) at x of a tuple s of nonzero sections, then L is at most the objective
  Σ_i exp(A(u)/t − v_u(s_i)/j) of every monomial Taylor test with weights u ≥ 0, u ≠ 0 on a simple
  normal crossing chart of a model at a point y with π(y) specializing to x, read at a
  specialization z of y. The tuple s need not be the tuple of the model.

Together: when a weight on a model minimizes the objective over all bases and all weights, its
basis is maximal for the Taylor filtration of the weight at every closed point of its stratum
(y a point of the stratum, x the point of the base), and the objective of every perturbation of
the weight by weights on the other coordinates at a closed point z is bounded below by the infimum
at π(z) (y = z).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Algebra

variable {σ K : Type*} [Field K] [Fintype σ]

/-- Monomial valuations with nonnegative real weights are additive on finite products of nonzero
power series. -/
theorem realWeightedOrder_finset_prod {ι : Type*} {u : σ → ℝ} (hu : ∀ i, 0 ≤ u i)
    (s : Finset ι) (g : ι → MvPowerSeries σ K) (hg : ∀ i ∈ s, g i ≠ 0) :
    realWeightedOrder u (∏ i ∈ s, g i) = ∑ i ∈ s, realWeightedOrder u (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact realWeightedOrder_eq_zero_of_isUnit hu isUnit_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      realWeightedOrder_mul hu (hg i (Finset.mem_insert_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

end Algebra

section Values

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- On a simple normal crossing chart, the real weighted order of the Taylor expansion of the
pullback of a section whose pulled back zero divisor is supported on the family is linear in the
weights, with coefficients the orders of the zero divisor along the members of the family. -/
theorem cartierPullbackRealValuation_eq_sum_of_supported {r : ℕ} (ξ : Fin r → X)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ) (c : EtaleChart K X n) (σc : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σc) (z : X) (hz : z ∈ c.U)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (hsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D s hs)) (t : X) = 0)
    (u : Fin n → ℝ) (hu : ∀ a, 0 ≤ u a) :
    cartierPullbackRealValuation D π z ez u s =
      ∑ j, (cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D s hs)) (ξ j) : ℝ) *
        (σc j).elim 0 u := by
  classical
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnorm : ∀ t : X, IsIntegrallyClosed (X.presheaf.stalk t) :=
    isSNCFamily_stalk_isIntegrallyClosed hsnc
  have : ∀ t : CodimensionOnePoint X, IsRegularLocalRing (X.presheaf.stalk (t : X)) :=
    fun t => isSNCFamily_stalk_regular hsnc (t : X)
  have : ∀ t : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (t : X)) :=
    fun t => inferInstance
  have hBeff : (cartierPullback π (cartierSectionZeroDivisor D s hs)).IsEffective :=
    cartierPullback_isEffective π _ (cartierSectionZeroDivisor_isEffective D s hs)
  obtain ⟨f, hf, v, hv⟩ := normal_isSNCChart_boundary_local_product hnorm
    (cartierPullback π (cartierSectionZeroDivisor D s hs)) c ξ hinj hξ σc hc hsupp z hz
  obtain ⟨f₀, hf₀, hfdef⟩ : ∃ (f₀ : Y.functionFieldˣ) (hf₀ : D.IsLocalEquationAt (π z) f₀),
      cartierPullbackTaylor D π z ez s =
        stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient D π z f₀ hf₀ s) :=
    ⟨Classical.choose (D.exists_isLocalEquationAt (π z)),
      Classical.choose_spec (D.exists_isLocalEquationAt (π z)), rfl⟩
  have himg : algebraMap (Y.presheaf.stalk (π z)) Y.functionField
      (cartierLocalCoefficient D (π z) f₀ hf₀ s) =
      ((f₀ * cartierSectionUnit D s hs : Y.functionFieldˣ) : Y.functionField) := by
    simpa only [Units.val_mul, cartierSectionUnit_val] using
      cartierLocalCoefficient_image D (π z) f₀ hf₀ s
  have heq : (cartierSectionZeroDivisor D s hs).IsLocalEquationAt (π z)
      (f₀ * cartierSectionUnit D s hs) :=
    cartierSectionZeroDivisor_localEquation D s hs (π z) f₀ hf₀
  have hgimg : algebraMap (X.presheaf.stalk z) X.functionField
      (cartierStalkPullbackCoefficient D π z f₀ hf₀ s) =
      ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom
        (f₀ * cartierSectionUnit D s hs) : X.functionFieldˣ) : X.functionField) := by
    rw [cartierStalkPullbackCoefficient_apply, ← dominantFunctionFieldMap_algebraMap, himg]
    rfl
  obtain ⟨u', hu'⟩ := (cartierPullback_isLocalEquationAt π _ z heq).exists_unit_mul_eq hf
  -- the exponents
  obtain ⟨m, hm⟩ : ∃ m : Fin r → ℕ, ∀ j, (m j : ℤ) =
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D s hs)) (ξ j) :=
    ⟨fun j => (cartierCoefficient (cartierPullback π
        (cartierSectionZeroDivisor D s hs)) (ξ j)).toNat,
      fun j => Int.toNat_of_nonneg (cartierCoefficient_nonneg_of_isEffective _ hBeff (ξ j))⟩
  -- the monomial in the coordinates of the chart, as a germ at z
  obtain ⟨P, hP⟩ : ∃ P : X.presheaf.stalk z, P = ∏ i,
      ((σc i).elim 1 fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) ^ m i :=
    ⟨_, rfl⟩
  have hprod : ((∏ i, sncChartComponentEquation c σc i ^
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D s hs)) (ξ i) :
        X.functionFieldˣ) : X.functionField) =
      algebraMap (X.presheaf.stalk z) X.functionField P := by
    rw [hP, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hm i, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
    congr 1
    cases hσ : σc i with
    | none => simp [sncChartComponentEquation, hσ]
    | some a =>
      simp only [sncChartComponentEquation, hσ, Option.elim_some]
      exact (X.algebraMap_germ_eq_germToFunctionField hz _).symm
  have hgerm : cartierStalkPullbackCoefficient D π z f₀ hf₀ s =
      ((u' * v : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * P := by
    apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
    calc algebraMap (X.presheaf.stalk z) X.functionField
          (cartierStalkPullbackCoefficient D π z f₀ hf₀ s)
        = algebraMap (X.presheaf.stalk z) X.functionField (u' : X.presheaf.stalk z) *
            (f : X.functionField) := by rw [hgimg, hu']
      _ = algebraMap (X.presheaf.stalk z) X.functionField (u' : X.presheaf.stalk z) *
            (algebraMap (X.presheaf.stalk z) X.functionField (v : X.presheaf.stalk z) *
              algebraMap (X.presheaf.stalk z) X.functionField P) := by rw [hv, hprod]
      _ = algebraMap (X.presheaf.stalk z) X.functionField
            (((u' * v : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * P) := by
          rw [Units.val_mul, map_mul, map_mul, mul_assoc]
  -- the Taylor expansion
  have hT : ∀ i, stalkTaylorExpansion z ez
      ((σc i).elim 1 fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) =
      (σc i).elim 1 MvPowerSeries.X := by
    intro i
    cases σc i with
    | none => simp
    | some a => simpa using hez a
  have hXne : ∀ i, ((σc i).elim 1 MvPowerSeries.X : MvPowerSeries (Fin n) K) ^ m i ≠ 0 := by
    intro i
    apply pow_ne_zero
    cases σc i with
    | none => simp
    | some a =>
      simp only [Option.elim_some]
      intro h
      have h2 := congrArg (MvPowerSeries.coeff (Finsupp.single a 1)) h
      rw [map_zero, MvPowerSeries.coeff_X, ite_eq_left rfl] at h2
      exact one_ne_zero h2
  unfold cartierPullbackRealValuation
  rw [hfdef, hgerm, map_mul, hP, map_prod,
    realWeightedOrder_unit_mul hu ((u' * v).isUnit.map (stalkTaylorExpansion z ez))]
  simp only [map_pow, hT]
  rw [realWeightedOrder_finset_prod hu _ _ fun i _ => hXne i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hm i]
  cases σc i with
  | none =>
    simp only [Option.elim_none, one_pow, mul_zero]
    exact realWeightedOrder_eq_zero_of_isUnit hu isUnit_one
  | some a =>
    simp only [Option.elim_some]
    rw [MvPowerSeries.X_pow_eq, realWeightedOrder_monomial_one,
      Finset.sum_eq_single a (fun b _ hb => by rw [Finsupp.single_eq_of_ne hb, Nat.cast_zero,
        mul_zero]) (fun h => absurd (Finset.mem_univ a) h), Finsupp.single_eq_same]
    push_cast
    ring

end Values

section Comparison

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [IsIntegral X] [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- A lower bound for the objective over the profile data at x of a tuple of nonzero sections is a
lower bound for the objective of every monomial Taylor test with nonnegative real weights on a
simple normal crossing chart of a model at a point y with π(y) specializing to x, read at a
specialization z of y. -/
theorem le_taylorTest_objective_of_le_sncWeightProfiles {r N : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (y : X) (hy : y ∈ c.U) (u : Fin n → ℝ) (hu0 : ∀ a, 0 ≤ u a) (hu : u ≠ 0)
    (hnu : ∀ a, u a ≠ 0 → ¬ IsUnit (X.presheaf.germ c.U y hy (c.coords (MvPolynomial.X a))))
    (x : Y) (hx : π y ⤳ x) (z : X) (hz : z ∈ c.U) (hyz : y ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) {t j : ℝ}
    (ht : 0 < t) (hj : 0 < j) {L : ℝ}
    (hL : ∀ p ∈ sncWeightProfiles cY fY d D₀ D x s,
      L ≤ ∑ i, Real.exp (p.1 / t - p.2 i / j)) :
    L ≤ ∑ i, Real.exp (chartWeightLogDiscrepancy σc d (fun k => cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) u / t -
      cartierPullbackRealValuation D π z ez u (s i) / j) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = chartWeightLogDiscrepancy σc d (fun k => cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ k)) u := ⟨_, rfl⟩
  rw [← hA]
  -- the bound with an error η
  have hη : ∀ η : ℝ, 0 < η → L ≤ Real.exp (η * (1 / t + 1 / j)) *
      ∑ i, Real.exp (A / t - cartierPullbackRealValuation D π z ez u (s i) / j) := by
    intro η hη
    obtain ⟨p, hp, hpA, hpv⟩ := exists_sncWeightProfile_of_taylor_real_weights π hπ cY fY d hd D₀
      cX ξ hinj hξ hsnc hBsupp c σc hc y hy u hu0 hu hnu x hx z hz hyz ez hez D s hs hη
    rw [← hA] at hpA
    refine (hL p hp).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : p.1 / t ≤ (A + η) / t := div_le_div_of_nonneg_right hpA ht.le
    have h2 : (cartierPullbackRealValuation D π z ez u (s i) - η) / j ≤ p.2 i / j :=
      div_le_div_of_nonneg_right (hpv i) hj.le
    have h3 : (A + η) / t - (cartierPullbackRealValuation D π z ez u (s i) - η) / j =
        η * (1 / t + 1 / j) +
          (A / t - cartierPullbackRealValuation D π z ez u (s i) / j) := by
      field_simp
      ring
    linarith
  -- let η tend to 0
  have htend : Tendsto (fun η : ℝ => Real.exp (η * (1 / t + 1 / j)) *
      ∑ i, Real.exp (A / t - cartierPullbackRealValuation D π z ez u (s i) / j))
      (𝓝[>] 0) (𝓝 (∑ i, Real.exp (A / t -
        cartierPullbackRealValuation D π z ez u (s i) / j))) := by
    have hc : Continuous fun η : ℝ => Real.exp (η * (1 / t + 1 / j)) *
        ∑ i, Real.exp (A / t - cartierPullbackRealValuation D π z ez u (s i) / j) := by
      fun_prop
    have h0 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa only [zero_mul, Real.exp_zero, one_mul] using h0
  exact ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun η hη' => hη η hη')

end Comparison

end MixedFujita
