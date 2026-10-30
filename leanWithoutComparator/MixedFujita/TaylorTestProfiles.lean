/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ToricExtractionDomination
public import MixedFujita.BasisAttainment
public import MixedFujita.ProjectiveRealWeightedMinimization
public import MixedFujita.SNCWeightTestPrimes

/-!
Monomial Taylor tests at closed points of a model are profile data (step 11, section 5.1 of the
manuscript): the bridge from the test valuations given by Taylor expansions to the weights on
simple normal crossing models.

Let π : X → Y be a smooth birational model of the pair with a simple normal crossing family ξ
supporting the crepant boundary, y a point of X, c a simple normal crossing chart at y,
u weights on the coordinates of c, supported on coordinates vanishing at y, and z a specialization
of y in the chart (z = y when all the weights are positive; y the generic point of a stratum and
z a closed point of it for a weight on the stratum). The monomial valuation with weights u in the
coordinates of c has centre containing y and

* log discrepancy A(u) = Σ_a u_a − Σ_j (b_j/d) u_{a(j)} for the pair, where b_j/d is the
  coefficient of the crepant boundary at ξ_j and a(j) the coordinate cutting out ξ_j
  (`chartWeightLogDiscrepancy`): the coordinates outside the family have log discrepancy one;
* values at least v_u(s) = the u-weighted order of the Taylor expansion at z of the pullback of a
  section s of a Cartier divisor of Y (`cartierPullbackRealValuation`).

Proved:

* for natural weights w = g w', a prime divisor e of a smooth birational test model of Y whose
  centre contains π(y), with log discrepancy A(w') and ord_e(div s) ≥ v_{w'}(s) for every nonzero
  section s of every Cartier divisor of Y (the sections need not be monomial at z);
* hence, for a tuple of nonzero sections of D and every specialization x of π(y), a profile datum
  (a, v) at x of the tuple with a ≤ A(w) and v_i ≥ v_w(s_i);
* for real weights u ≥ 0, u ≠ 0 and every η > 0, a profile datum at x with a ≤ A(u) + η and
  v_i ≥ v_u(s_i) − η.

So the infimum of the objective over the profile data at x, for any tuple, is at most the
objective of the monomial Taylor tests at z: of the valuations v_ε of section 5.1 obtained from a
weight on a stratum by adding the weights ε and ε² in the directions along the stratum, whose
centre is the closed point z (y = z, x = π(z)), and of the weight itself read on another tuple
(y a point of the stratum over which the weight lives, x any point of the image of its
closure).
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

section LogDiscrepancy

/-- The log discrepancy of the monomial valuation with weights u on the coordinates of a simple
normal crossing chart, for a boundary with coefficients b_j/d on the members of the family: the
coordinates outside the family count with log discrepancy one. -/
noncomputable def chartWeightLogDiscrepancy {n r : ℕ} (σc : Fin r → Option (Fin n)) (d : ℕ)
    (b : Fin r → ℤ) (u : Fin n → ℝ) : ℝ :=
  ∑ a, u a - ∑ j, (b j : ℝ) / d * (σc j).elim 0 u

theorem chartWeightLogDiscrepancy_smul {n r : ℕ} (σc : Fin r → Option (Fin n)) (d : ℕ)
    (b : Fin r → ℤ) (lam : ℝ) (u : Fin n → ℝ) :
    chartWeightLogDiscrepancy σc d b (lam • u) = lam * chartWeightLogDiscrepancy σc d b u := by
  unfold chartWeightLogDiscrepancy
  have h : ∀ j, (σc j).elim 0 (lam • u) = lam * (σc j).elim 0 u := by
    intro j
    cases σc j <;> simp
  simp only [h, Pi.smul_apply, smul_eq_mul]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem continuous_chartWeightLogDiscrepancy {n r : ℕ} (σc : Fin r → Option (Fin n)) (d : ℕ)
    (b : Fin r → ℤ) : Continuous (chartWeightLogDiscrepancy σc d b) := by
  unfold chartWeightLogDiscrepancy
  refine Continuous.sub (continuous_finsetSum _ fun a _ => continuous_apply a)
    (continuous_finsetSum _ fun j _ => Continuous.mul continuous_const ?_)
  cases σc j with
  | none => exact continuous_const
  | some a => exact continuous_apply a

end LogDiscrepancy

section Prime

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Natural weights on the coordinates of a simple normal crossing chart at a point y of a model
are a multiple of a prime divisor over the base: a smooth birational test model σ : U → Y with a
prime divisor e whose centre contains π(y), with w = g w', whose log discrepancy for the pair
(with the denominator d cleared) is d Σ_a w'_a − Σ_j ord_{ξ_j}(B_X) w'_{a(j)}, and along which
the zero divisor of every nonzero section of every Cartier divisor of Y has order at least the
w'-weighted order of the Taylor expansion of the pullback of the section at every specialization z
of y in the chart. -/
theorem exists_base_test_prime_of_taylor_weights {r : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (y : X) (hy : y ∈ c.U) (w : Fin n → ℕ) (hw : w ≠ 0)
    (hwy : ∀ a, w a ≠ 0 → ¬ IsUnit (X.presheaf.germ c.U y hy (c.coords (MvPolynomial.X a)))) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : CodimensionOnePoint U) (g : ℕ) (w' : Fin n → ℕ),
      1 ≤ g ∧ (∀ a, w a = g * w' a) ∧ π y ∈ closure ({σ (e : U)} : Set Y) ∧
      (d : ℤ) + cartierCoefficient
          (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U) =
        (d : ℤ) * ∑ a, (w' a : ℤ) - ∑ j, cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j) *
            (((σc j).elim 0 w' : ℕ) : ℤ) ∧
      ∀ (z : X) (hz : z ∈ c.U), y ⤳ z →
      ∀ ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
          (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
          MvPowerSeries.X i) →
        ∀ (D : CartierDivisor Y) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0),
          (((cartierPullbackTaylor D π z ez s).weightedOrder w').toNat : ℤ) ≤
            cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D s hs)) (e : U) := by
  classical
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, hye, -, hdisc, hdom⟩ :=
    exists_snc_chart_extraction_prime ξ hinj hξ hsnc c σc hc y hy w hw hwy
  have hspy : σ (e : U) ⤳ y := specializes_iff_mem_closure.mpr hye
  refine ⟨U, hUi, hUn, hUo, hUs, σ ≫ π, inferInstance, inferInstance,
    dominantFunctionFieldAlgHom_comp_bijective π σ hπ hσ, cU, e, g, w', hg, hgw, ?_, ?_, ?_⟩
  · exact specializes_iff_mem_closure.mp (hspy.map π.continuous)
  · have h := hdisc cX (crepantPullbackFormUnit π hπ cY fY cX) d
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) hBsupp
    rw [crepantBoundaryCartier_smooth_recombine π hπ cY fY d D₀ cX] at h
    rw [logDiscrepancyDivisor_comp π σ hπ hσ cY fY d D₀ cX cU etaleCharts_cover]
    exact h
  · intro z hz hyz ez hez D s hs
    have hsp : σ (e : U) ⤳ z := hspy.trans hyz
    have hsmU : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
    have hdvr : IsDiscreteValuationRing (U.presheaf.stalk (e : U)) :=
      smoothOverField_codimensionOne_stalk_DVR (K := K) e
    obtain ⟨f, hf, hfdef⟩ : ∃ (f : Y.functionFieldˣ) (hf : D.IsLocalEquationAt (π z) f),
        cartierPullbackTaylor D π z ez s =
          stalkTaylorExpansion z ez (cartierStalkPullbackCoefficient D π z f hf s) :=
      ⟨Classical.choose (D.exists_isLocalEquationAt (π z)),
        Classical.choose_spec (D.exists_isLocalEquationAt (π z)), rfl⟩
    have himg : algebraMap (Y.presheaf.stalk (π z)) Y.functionField
        (cartierLocalCoefficient D (π z) f hf s) =
        ((f * cartierSectionUnit D s hs : Y.functionFieldˣ) : Y.functionField) := by
      simpa only [Units.val_mul, cartierSectionUnit_val] using
        cartierLocalCoefficient_image D (π z) f hf s
    have heq : (cartierSectionZeroDivisor D s hs).IsLocalEquationAt (π z)
        (f * cartierSectionUnit D s hs) :=
      cartierSectionZeroDivisor_localEquation D s hs (π z) f hf
    have hgimg : algebraMap (X.presheaf.stalk z) X.functionField
        (cartierStalkPullbackCoefficient D π z f hf s) =
        ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom
          (f * cartierSectionUnit D s hs) : X.functionFieldˣ) : X.functionField) := by
      rw [cartierStalkPullbackCoefficient_apply, ← dominantFunctionFieldMap_algebraMap, himg]
      rfl
    have hne : cartierStalkPullbackCoefficient D π z f hf s ≠ 0 := by
      intro h0
      have h1 : algebraMap (X.presheaf.stalk z) X.functionField
          (cartierStalkPullbackCoefficient D π z f hf s) ≠ 0 := by
        rw [hgimg]
        exact Units.ne_zero _
      exact h1 (by rw [h0, map_zero])
    -- the local equation of the pullback at the generization σ(e) of z
    have hloc₁ := cartierPullback_isLocalEquationAt π _ z heq
    have hloc₂ : (cartierPullback π (cartierSectionZeroDivisor D s hs)).IsLocalEquationAt
        (σ (e : U)) (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom
          (f * cartierSectionUnit D s hs)) := by
      obtain ⟨V, hV, hcls⟩ := CartierDivisor.isLocalEquationAt_iff.mp hloc₁
      have : Nonempty V := ⟨⟨z, hV⟩⟩
      exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hcls
        (hsp.mem_open V.isOpen hV)
    have hloc₃ := cartierPullback_isLocalEquationAt σ _ (e : U) hloc₂
    rw [cartierPullback_comp, cartierCoefficient_eq_ord hloc₃]
    have h := hdom z hz hyz ez hez (cartierStalkPullbackCoefficient D π z f hf s)
      ((cartierPullbackTaylor D π z ez s).weightedOrder w').toNat hne (by
        rw [← hfdef]
        exact ENat.natCast_toNat_le_self _)
    rw [hgimg] at h
    exact h

end Prime

section Profiles

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}} [IsIntegral Y]
  [IsIntegral X] [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- A monomial Taylor test with natural weights on a chart at a point y of a model, read at a
specialization z of y, gives a profile datum of every tuple of nonzero sections at every
specialization x of π(y): log discrepancy at most that of the weights and values at least the
weighted orders of the Taylor expansions at z of the pullbacks of the sections. -/
theorem exists_sncWeightProfile_of_taylor_weights {r N : ℕ} (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D₀ : CartierDivisor Y) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ t : CodimensionOnePoint X, (t : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (t : X) = 0)
    (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc)
    (y : X) (hy : y ∈ c.U) (w : Fin n → ℕ) (hw : w ≠ 0)
    (hwy : ∀ a, w a ≠ 0 → ¬ IsUnit (X.presheaf.germ c.U y hy (c.coords (MvPolynomial.X a))))
    (x : Y) (hx : π y ⤳ x) (z : X) (hz : z ∈ c.U) (hyz : y ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) :
    ∃ p ∈ sncWeightProfiles cY fY d D₀ D x s,
      p.1 ≤ chartWeightLogDiscrepancy σc d (fun j => cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j))
        (fun a => (w a : ℝ)) ∧
      ∀ i, cartierPullbackRealValuation D π z ez (fun a => (w a : ℝ)) (s i) ≤ p.2 i := by
  classical
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, hcl, hdisc, hdom⟩ :=
    exists_base_test_prime_of_taylor_weights π hπ cY fY d D₀ cX ξ hinj hξ hsnc hBsupp c σc hc y
      hy w hw hwy
  have hclx : x ∈ closure ({σ (e : U)} : Set Y) :=
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hcl).trans hx)
  obtain ⟨X₂, hXi, hXo, hXN, hXs, π₂, hπd, hπo, hπp, hπ₂, cX₂, r₂, ξ₂, hinj₂, hξ₂, hsnc₂, hBsupp₂,
    hGsupp₂⟩ := exists_proper_snc_model_with cY fY d D₀
      (fun i => cartierSectionZeroDivisor D (s i) (hs i))
  obtain ⟨v, hv0, hvΦ, hval, hA⟩ := exists_sncWeight_data_of_test_prime π₂ hπ₂ cY fY d hd D₀ cX₂
    ξ₂ hinj₂ hξ₂ hsnc₂ hBsupp₂ (fun i => cartierSectionZeroDivisor D (s i) (hs i)) hGsupp₂ σ hσ
    cU e x hclx
  have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hp₀ : ((∑ k, v k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π₂ hπ₂ cY fY d D₀ cX₂ etaleCharts_cover) (ξ₂ k)) / d),
      fun i => ∑ k, v k * (cartierCoefficient (cartierPullback π₂
        (cartierSectionZeroDivisor D (s i) (hs i))) (ξ₂ k) : ℝ)) : ℝ × (Fin N → ℝ)) ∈
      sncWeightProfiles cY fY d D₀ D x s :=
    ⟨hs, X₂, hXi, inferInstance, hXo, hXs, π₂, hπd, hπo, hπp, hπ₂, cX₂, r₂, ξ₂, v, hinj₂, hξ₂,
      hsnc₂, hBsupp₂, hGsupp₂, hv0, hvΦ, rfl, fun i => rfl⟩
  refine ⟨_, sncWeightProfiles_smul cY fY d D₀ D x s hp₀ hgpos.le, ?_, fun i => ?_⟩
  · -- the log discrepancy
    have hcast : ((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) =
        (d : ℝ) * ∑ a, (w' a : ℝ) - ∑ j, (cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j) : ℝ) *
            (((σc j).elim 0 w' : ℕ) : ℝ) := by
      exact_mod_cast hdisc
    have helim : ∀ j, (σc j).elim 0 (fun a => (w a : ℝ)) =
        (g : ℝ) * (((σc j).elim 0 w' : ℕ) : ℝ) := by
      intro j
      cases σc j with
      | none => simp
      | some a =>
        simp only [Option.elim_some]
        rw [hgw a]
        push_cast
        ring
    change (g : ℝ) * ∑ k, v k * (((d : ℝ) - cartierCoefficient
      (crepantBoundaryCartier π₂ hπ₂ cY fY d D₀ cX₂ etaleCharts_cover) (ξ₂ k)) / d) ≤ _
    refine (mul_le_mul_of_nonneg_left hA hgpos.le).trans_eq ?_
    unfold chartWeightLogDiscrepancy
    rw [hcast]
    simp only [helim]
    have hsum : ∑ a, ((w a : ℕ) : ℝ) = (g : ℝ) * ∑ a, (w' a : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by rw [hgw a]; push_cast; ring
    have h3 : ∑ j, (cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j) : ℝ) / d *
          ((g : ℝ) * (((σc j).elim 0 w' : ℕ) : ℝ)) =
        (g : ℝ) * ((∑ j, (cartierCoefficient
          (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j) : ℝ) *
            (((σc j).elim 0 w' : ℕ) : ℝ)) / d) := by
      rw [Finset.sum_div, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, h3, sub_div, mul_sub, mul_div_cancel_left₀ _ hdpos.ne']
  · -- the values
    change _ ≤ (g : ℝ) * ∑ k, v k * (cartierCoefficient (cartierPullback π₂
      (cartierSectionZeroDivisor D (s i) (hs i))) (ξ₂ k) : ℝ)
    rw [hval i]
    have hk := hdom z hz hyz ez hez D (s i) (hs i)
    have hk' : (((cartierPullbackTaylor D π z ez (s i)).weightedOrder w').toNat : ℝ) ≤
        (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) (hs i)))
          (e : U) : ℝ) := by exact_mod_cast hk
    unfold cartierPullbackRealValuation
    by_cases hF : cartierPullbackTaylor D π z ez (s i) = 0
    · rw [hF, realWeightedOrder, dite_eq_left rfl]
      exact mul_nonneg hgpos.le ((Nat.cast_nonneg _).trans hk')
    · have hw' : (fun a => (w a : ℝ)) = (g : ℝ) • (fun a => (w' a : ℝ)) := by
        funext a
        rw [Pi.smul_apply, smul_eq_mul, hgw a]
        push_cast
        ring
      rw [hw', realWeightedOrder_smul hgpos.le, realWeightedOrder_natCast w' hF]
      exact mul_le_mul_of_nonneg_left hk' hgpos.le

/-- A monomial Taylor test with nonnegative real weights on a chart at a point y of a model,
supported on coordinates vanishing at y and read at a specialization z of y, is approximated by
profile data of every tuple of nonzero sections at every specialization x of π(y): for every
η > 0 a profile datum with log discrepancy at most that of the weights plus η and values at least
the real weighted orders of the Taylor expansions at z minus η. -/
theorem exists_sncWeightProfile_of_taylor_real_weights {r N : ℕ} (cY : EtaleChart K Y n)
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
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) {η : ℝ}
    (hη : 0 < η) :
    ∃ p ∈ sncWeightProfiles cY fY d D₀ D x s,
      p.1 ≤ chartWeightLogDiscrepancy σc d (fun j => cartierCoefficient
        (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j)) u + η ∧
      ∀ i, cartierPullbackRealValuation D π z ez u (s i) - η ≤ p.2 i := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : Fin r → ℤ, (fun j => cartierCoefficient
      (crepantBoundaryCartier π hπ cY fY d D₀ cX etaleCharts_cover) (ξ j)) = b := ⟨_, rfl⟩
  rw [hb]
  -- continuity of the log discrepancy and of the values at u
  have hcont : Continuous fun u' : Fin n → ℝ =>
      (chartWeightLogDiscrepancy σc d b u',
        fun i => cartierPullbackRealValuation D π z ez u' (s i)) :=
    (continuous_chartWeightLogDiscrepancy σc d b).prodMk
      (continuous_pi fun i => continuous_realWeightedOrder _)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuous_iff.mp hcont u η hη
  obtain ⟨M, W, hM, hdist, hW0⟩ := exists_natural_weight_approximation u hu0 hδ
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hWne : W ≠ 0 := by
    intro h
    apply hu
    funext a
    exact (hW0 a).mp (by rw [h]; rfl)
  obtain ⟨p, hp, hpA, hpv⟩ := exists_sncWeightProfile_of_taylor_weights π hπ cY fY d hd D₀ cX ξ
    hinj hξ hsnc hBsupp c σc hc y hy W hWne
    (fun a ha => hnu a (fun h0 => ha ((hW0 a).mpr h0))) x hx z hz hyz ez hez D s hs
  rw [hb] at hpA
  have hscale : (fun k => (W k : ℝ) / M) = (1 / (M : ℝ)) • (fun k => (W k : ℝ)) := by
    funext k
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  have hd' := hclose (fun k => (W k : ℝ) / M) hdist
  rw [Prod.dist_eq, max_lt_iff] at hd'
  obtain ⟨hdA, hdv⟩ := hd'
  refine ⟨_, sncWeightProfiles_smul cY fY d D₀ D x s hp (by positivity : (0 : ℝ) ≤ 1 / M),
    ?_, fun i => ?_⟩
  · change 1 / (M : ℝ) * p.1 ≤ _
    have h1 : 1 / (M : ℝ) * p.1 ≤ chartWeightLogDiscrepancy σc d b (fun k => (W k : ℝ) / M) := by
      rw [hscale, chartWeightLogDiscrepancy_smul]
      exact mul_le_mul_of_nonneg_left hpA (by positivity)
    have h2 := hdA
    rw [Real.dist_eq, abs_lt] at h2
    linarith [h2.2]
  · change _ ≤ 1 / (M : ℝ) * p.2 i
    have h1 : cartierPullbackRealValuation D π z ez (fun k => (W k : ℝ) / M) (s i) ≤
        1 / (M : ℝ) * p.2 i := by
      unfold cartierPullbackRealValuation
      rw [hscale, realWeightedOrder_smul (by positivity)]
      exact mul_le_mul_of_nonneg_left (hpv i) (by positivity)
    have h2 := (dist_le_pi_dist _ _ i).trans_lt hdv
    rw [Real.dist_eq, abs_lt] at h2
    linarith [h2.1]

end Profiles

end MixedFujita
