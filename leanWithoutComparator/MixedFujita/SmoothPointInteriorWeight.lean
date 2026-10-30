/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltMinimizerDataFromWeights
public import MixedFujita.ToricChartModel
public import MixedFujita.EtaleChartRegularParameters
public import MixedFujita.SmoothClosedPoints
public import MixedFujita.CartierBirationalZeroDivisors
public import MixedFujita.CartierWeilVanishingOrder
public import MixedFujita.MinimizationIntervalArithmetic
public import MixedFujita.HironakaSNCModelExistence

/-!
The interior condition on a simple normal crossing model at a smooth point (steps 11 and 13,
sections 3, 7 and 8 of the manuscript).

The interior condition (7) is proved in the manuscript for the valuation ζ ord_x of a smooth
point x: for a basis s of the sections of j L,

  (1/N) Σ_i exp(ζ n/t − ζ mult_x(s_i)/j) ≤ 1 − δ.

This file moves it to the weights of a simple normal crossing model of the sections.

* Centred charts: an étale chart translated by the values of its coordinates at a K-point. At a
  point x of the chart with a K-valued point of the stalk the centred coordinates are not units,
  and x is the only point of the chart specializing to x at which none of them is a unit.
* The exceptional prime of the blow-up of the point: the toric chart of the centred chart with
  weights (1, …, 1) is a smooth birational model with a prime divisor e whose image is x and
  along which the relative canonical divisor has coefficient n − 1. The log discrepancy of e for
  the zero boundary is n.
* For a dominant morphism and a prime divisor of its source, the coefficient along the prime
  divisor of the pullback of the zero divisor of a nonzero section is at least the vanishing order
  of the section at the image of the prime divisor.
* Consequently, on every proper simple normal crossing model of the smooth variety with zero
  boundary and of the zero divisors of the sections, some weight over the fibre of x has objective
  at most Σ_i exp(lam n/τ − lam mult_x(s_i)/j), for every scale lam ≥ 0: the retraction of the
  scaled prime e. Under (7) the objective of this weight is smaller than N, the interior condition
  for the weights.
* With the point-centre property of the minimizers on the proper simple normal crossing models,
  (7) gives the data of the minimizer at x for the smooth variety with zero boundary. No model is
  assumed: it exists by resolution.
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

section Centered

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- The étale chart translated by the values of its coordinates at a K-point of the chart. -/
noncomputable def etaleChartCentered (c : EtaleChart K X n) (α : Γ(X, c.U) →ₐ[K] K) :
    EtaleChart K X n where
  U := c.U
  isAffine := c.isAffine
  nonempty := c.nonempty
  coords := centeredPolynomialChart c.coords α
  formallyEtale := by
    have hg := centeredPolynomialChart_etale c.coords α (etaleChart_coords_etale c)
    let _ := (centeredPolynomialChart c.coords α).toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, c.U) := hg
    exact Algebra.Etale.formallyEtale

/-- At a point of the chart with a K-valued point of the stalk, the coordinates centred at the
point are not units. -/
theorem etaleChartCentered_germ_not_isUnit (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (β : X.presheaf.stalk x →ₐ[K] K) (a : Fin n) :
    ¬ IsUnit (X.presheaf.germ c.U x hx
      ((etaleChartCentered c (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X a))) := by
  intro hunit
  have h0 := centeredPolynomialChart_constantCoeff c.coords (rationalAffineGermPoint x hx β)
    (MvPolynomial.X a)
  rw [MvPolynomial.constantCoeff_X] at h0
  exact (rationalLocalPoint_isUnit_iff β _).mp hunit h0

/-- A point of the chart specializing to x at which no coordinate centred at x is a unit is x:
the centred coordinates generate the maximal ideal at x. -/
theorem etaleChartCentered_eq_of_specializes (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (β : X.presheaf.stalk x →ₐ[K] K) (y : X) (hyx : y ⤳ x) (hy : y ∈ c.U)
    (hnu : ∀ a, ¬ IsUnit (X.presheaf.germ c.U y hy
      ((etaleChartCentered c (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X a)))) :
    y = x := by
  have hxy : x ⤳ y := by
    rw [specializes_iff_forall_open]
    intro V hV hyV
    obtain ⟨f, hfV, hyf⟩ := c.isAffine.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨y, hyV⟩ hy
    refine hfV ?_
    rw [X.mem_basicOpen f x hx]
    by_contra hnot
    have hmem : X.presheaf.germ c.U x hx f ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnot)
    rw [etaleChart_maximalIdeal_eq_span c x hx β] at hmem
    have hle : Ideal.span (Set.range fun i =>
        etaleChartCenteredStalkCoords c x hx β (MvPolynomial.X i)) ≤
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap
          (X.presheaf.stalkSpecializes hyx).hom := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      have hgerm : (X.presheaf.stalkSpecializes hyx).hom
          (X.presheaf.germ c.U x hx ((etaleChartCentered c
            (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X i))) =
          X.presheaf.germ c.U y hy ((etaleChartCentered c
            (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X i)) :=
        TopCat.Presheaf.germ_stalkSpecializes_apply ..
      change ¬ IsUnit ((X.presheaf.stalkSpecializes hyx).hom
        (X.presheaf.germ c.U x hx ((etaleChartCentered c
          (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X i))))
      rw [hgerm]
      exact hnu i
    have hsp := hle hmem
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hsp
    have hgerm : (X.presheaf.stalkSpecializes hyx).hom (X.presheaf.germ c.U x hx f) =
        X.presheaf.germ c.U y hy f := TopCat.Presheaf.germ_stalkSpecializes_apply ..
    rw [hgerm] at hsp
    exact hsp ((X.mem_basicOpen f y hy).mp hyf)
  exact (hyx.antisymm hxy).eq

end Centered

section Extraction

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

omit [IsLocallyNoetherian X] in
/-- The exceptional prime of the blow-up of a point with a K-valued point of the stalk on a smooth
variety of dimension n ≥ 1: a smooth birational model with a prime divisor e whose image is the
point and along which the relative canonical divisor has coefficient n − 1. -/
theorem exists_extraction_prime_at_rational_point (hn : 1 ≤ n) (c₀ : EtaleChart K X n) (x : X)
    (β : X.presheaf.stalk x →ₐ[K] K) :
    ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
      (_ : U.Over (Spec (CommRingCat.of K)))
      (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
      (σ : U ⟶ X) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
      (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
      (cU : EtaleChart K U n) (e : U),
      Order.coheight e = 1 ∧ σ e = x ∧
      cartierCoefficient (birationalRelativeCanonicalDivisor n σ hσ c₀ etaleCharts_cover cU
        etaleCharts_cover) e = (n : ℤ) - 1 := by
  have : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨c, hx⟩ : ∃ c : EtaleChart K X n, x ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := n)).symm ▸ Opens.mem_top x)
  have hw : (fun _ : Fin n => 1) ≠ (0 : Fin n → ℕ) := fun h => by
    have h1 := congrFun h ⟨0, hn⟩
    simp at h1
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, g, w', hg, hgw, he, hecU, hxe, hord,
    hjac⟩ := exists_toric_extraction_model (etaleChartCentered c (rationalAffineGermPoint x hx β))
      x hx (fun _ => 1) hw (fun a _ => etaleChartCentered_germ_not_isUnit c x hx β a)
  have hw' : ∀ a, w' a = 1 := fun a =>
    Nat.dvd_one.mp ⟨g, (hgw a).trans (Nat.mul_comm _ _)⟩
  -- the image of the prime divisor is the point
  have hσe : σ e = x := by
    have hsp : σ e ⤳ x := specializes_iff_mem_closure.mpr hxe
    have hyU : σ e ∈ c.U := hsp.mem_open c.U.isOpen hx
    refine etaleChartCentered_eq_of_specializes c x hx β (σ e) hsp hyU fun a hunit => ?_
    have h1 := hord a
    rw [hw' a] at h1
    have h0 : U.ord (dominantFunctionFieldAlgHom (K := K) σ (etaleChartFunctionFieldCoords
        (etaleChartCentered c (rationalAffineGermPoint x hx β)) (MvPolynomial.X a))) e = 0 := by
      change U.ord ((dominantFunctionFieldMap σ).hom (X.germToFunctionField c.U
        ((etaleChartCentered c (rationalAffineGermPoint x hx β)).coords (MvPolynomial.X a)))) e = 0
      rw [← X.algebraMap_germ_eq_germToFunctionField hyU, dominantFunctionFieldMap_algebraMap]
      exact scheme_ord_stalk_unit e (hunit.map (σ.stalkMap e).hom).unit
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hσe, ?_⟩
  unfold birationalRelativeCanonicalDivisor
  rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt σ c₀ etaleCharts_cover
    cU etaleCharts_cover (isUnit_chartRelativeJacobianDet_of_bijective σ hσ c₀ cU) e
    (etaleChartCentered c (rationalAffineGermPoint x hx β)) (by rw [hσe]; exact hx) cU hecU),
    IsUnit.unit_spec, hjac]
  simp [hw']

end Extraction

section Order

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T] [IsLocallyNoetherian T]
  (ρ : T ⟶ X) [IsDominant ρ]

/-- The coefficient along a prime divisor of the pullback of the zero divisor of a nonzero section
is at least the vanishing order of the section at the image of the prime divisor. -/
theorem cartierPullback_sectionZeroDivisor_coefficient_ge_vanishingOrder (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) (t : CodimensionOnePoint T)
    [IsDiscreteValuationRing (T.presheaf.stalk (t : T))] :
    ((cartierSectionVanishingOrder D (ρ (t : T)) s).toNat : ℤ) ≤
      cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor D s hs)) (t : T) := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ (t : T))
  obtain ⟨r, hr, hrimage, heq, hrorder⟩ :=
    cartierSectionZeroDivisor_regular_localEquation D (ρ (t : T)) f hf s hs
  have himage : ((Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
      (f * cartierSectionUnit D s hs) : T.functionFieldˣ) : T.functionField) =
      algebraMap (T.presheaf.stalk (t : T)) T.functionField (ρ.stalkMap (t : T) r) := by
    rw [← dominantFunctionFieldMap_algebraMap, hrimage]
    rfl
  have hne : ρ.stalkMap (t : T) r ≠ 0 := by
    intro h0
    have h1 : algebraMap (T.presheaf.stalk (t : T)) T.functionField (ρ.stalkMap (t : T) r) ≠ 0 := by
      rw [← himage]
      exact Units.ne_zero _
    exact h1 (by rw [h0, map_zero])
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (fun h => hne ((localAdicOrder_eq_top_iff _).mp h))
  rw [cartierCoefficient_eq_ord (cartierPullback_isLocalEquationAt ρ _ (t : T) heq), himage,
    scheme_ord_regular_eq_localAdicOrder_nat t _ hne d hd.symm]
  have hle := scheme_stalkMap_localAdicOrder_le ρ (t : T) r
  rw [hrorder, ← hd] at hle
  exact_mod_cast ENat.toNat_le_of_le_natCast hle

end Order

section Interior

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- The retraction of the scaled exceptional prime of the blow-up of a point: on a proper simple
normal crossing model of a smooth variety with zero boundary and of the zero divisors of sections
s_i, for a point x with a K-valued point of the stalk and every scale lam ≥ 0, some weight over
π⁻¹(x) has objective at most Σ_i exp(lam n/τ − lam mult_x(s_i)/j). -/
theorem exists_sncWeight_objective_le_of_smooth_point {N r : ℕ} (hn : 1 ≤ n)
    (cY : EtaleChart K Y n) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
        etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0)
    (x : Y) (β : Y.presheaf.stalk x →ₐ[K] K) {τ : ℝ} (hτ : 0 < τ) {j : ℝ} (hj : 0 < j)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ∃ w : Fin r → ℝ, (∀ k, 0 ≤ w k) ∧
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      weightExponentialObjective
          (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
            (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
              principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
            ((1 : ℕ) : ℝ))
          (fun i k => (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) τ j w ≤
        ∑ i, Real.exp (lam * n / τ -
          lam * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) / j) := by
  obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, he, hσe, hK⟩ :=
    exists_extraction_prime_at_rational_point hn cY x β
  obtain ⟨w, hw0, hwΦ, hle⟩ := exists_sncWeight_objective_le_of_test_prime π hπ cY
    (1 : Y.functionFieldˣ) 1 le_rfl
    (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX ξ hinj
    hξ hsnc hBsupp (fun i => cartierSectionZeroDivisor D (s i) (hs i)) hDsupp σ hσ cU ⟨e, he⟩ x
    (by rw [hσe]; exact subset_closure rfl) hτ j lam hlam
  refine ⟨w, hw0, hwΦ, hle.trans (Finset.sum_le_sum fun i _ => Real.exp_le_exp.mpr ?_)⟩
  -- the log discrepancy of the prime divisor is n
  have hA : cartierCoefficient (logDiscrepancyDivisor n σ hσ cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU
      etaleCharts_cover) e = (n : ℤ) - 1 := by
    rw [logDiscrepancyDivisor_boundary_zero σ hσ cY (1 : Y.functionFieldˣ) 1 cU, one_nsmul]
    exact hK
  -- the order of the sections along the prime divisor is at least the multiplicity
  have : Smooth (U ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) (⟨e, he⟩ : CodimensionOnePoint U)
  have hv := cartierPullback_sectionZeroDivisor_coefficient_ge_vanishingOrder σ D (s i) (hs i)
    (⟨e, he⟩ : CodimensionOnePoint U)
  change ((cartierSectionVanishingOrder D (σ e) (s i)).toNat : ℤ) ≤
    cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) (hs i))) e at hv
  rw [hσe] at hv
  have hv' : ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) ≤
      (cartierCoefficient (cartierPullback σ (cartierSectionZeroDivisor D (s i) (hs i))) e : ℝ) := by
    exact_mod_cast hv
  change lam * ((((1 : ℕ) : ℝ) + cartierCoefficient (logDiscrepancyDivisor n σ hσ cY
      (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
        principalCartierDivisor Y (1 : Y.functionFieldˣ))) cU etaleCharts_cover) e) /
      ((1 : ℕ) : ℝ)) / τ -
    lam * (cartierCoefficient (cartierPullback σ
      (cartierSectionZeroDivisor D (s i) (hs i))) e : ℝ) / j ≤ _
  rw [hA]
  have h1 : lam * ((((1 : ℕ) : ℝ) + (((n : ℤ) - 1 : ℤ) : ℝ)) / ((1 : ℕ) : ℝ)) / τ =
      lam * n / τ := by
    push_cast
    ring
  have h2 : lam * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) / j ≤
      lam * (cartierCoefficient (cartierPullback σ
        (cartierSectionZeroDivisor D (s i) (hs i))) e : ℝ) / j :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv' hlam) hj.le
  rw [h1]
  linarith

/-- The interior condition for the weights from the interior condition (7) for the valuation
ζ ord_x: if (1/N) Σ_i exp(ζ n/τ − ζ mult_x(s_i)/j) ≤ 1 − δ with δ > 0, some weight over π⁻¹(x) has
objective smaller than N. -/
theorem exists_interior_sncWeight_of_smooth_point {N r : ℕ} (hn : 1 ≤ n) (hN : 0 < N)
    (cY : EtaleChart K Y n) (cX : EtaleChart K X n)
    (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hsnc : IsSNCFamily K n ξ)
    (hBsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier π hπ cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
        etaleCharts_cover) (z : X) = 0)
    (D : CartierDivisor Y) (s : Fin N → Γ(D.sheaf, ⊤)) (hs : ∀ i, s i ≠ 0)
    (hDsupp : ∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback π (cartierSectionZeroDivisor D (s i) (hs i)))
        (z : X) = 0)
    (x : Y) (β : Y.presheaf.stalk x →ₐ[K] K) {τ : ℝ} (hτ : 0 < τ) {j : ℕ} (hj : 1 ≤ j)
    {ζ δ : ℝ} (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hF : minimizationFunctional j τ (ζ * n) (fun i =>
      ζ * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ)) ≤ 1 - δ) :
    ∃ w : Fin r → ℝ, (∀ k, 0 ≤ w k) ∧
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) ∧
      weightExponentialObjective
          (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ cY
            (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor cY +
              principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
            ((1 : ℕ) : ℝ))
          (fun i k => (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor D (s i) (hs i))) (ξ k) : ℝ)) τ j w < N := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  obtain ⟨w, hw0, hwΦ, hle⟩ := exists_sncWeight_objective_le_of_smooth_point π hπ hn cY cX ξ hinj
    hξ hsnc hBsupp D s hs hDsupp x β hτ hjpos hζ
  refine ⟨w, hw0, hwΦ, lt_of_le_of_lt hle ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum : ∑ i, Real.exp (ζ * n / τ -
      ζ * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ) / j) =
      N * minimizationFunctional j τ (ζ * n) (fun i =>
        ζ * ((cartierSectionVanishingOrder D x (s i)).toNat : ℝ)) := by
    unfold minimizationFunctional
    field_simp
  rw [hsum]
  nlinarith [mul_le_mul_of_nonneg_left hF hNpos.le]

end Interior

section MinimizerData

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [IsProper (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- The data of the minimizer at a point of a smooth proper variety with zero boundary from the
interior condition (7) for the valuation ζ ord_x with t < 1 and the point-centre property of the
weight minimizers on the proper simple normal crossing models of the sections. -/
theorem smooth_kltIsolationMinimizerData_of_interior_start (hn : 1 ≤ n)
    (c₀ : EtaleChart K Y n) (L : CartierDivisor Y) (m₀ : ℕ) (x : Y)
    (β : Y.presheaf.stalk x →ₐ[K] K) (j : ℕ) (hj : 1 ≤ j) (hjm₀ : m₀ ∣ j) {N : ℕ} (hN : 0 < N)
    (s : Fin N → Γ((j • L).sheaf, ⊤)) (hs : ∀ i, s i ≠ 0) (i₀ : Fin N)
    (hi₀ : x ∈ cartierSectionNonvanishingOpen (j • L) (s i₀))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) {ζ δ : ℝ} (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hF : minimizationFunctional j t (ζ * n) (fun i =>
      ζ * ((cartierSectionVanishingOrder (j • L) x (s i)).toNat : ℝ)) ≤ 1 - δ)
    (hpc : ∀ (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
      [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
      (π : X ⟶ Y) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))] [IsProper π]
      (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π)) (cX : EtaleChart K X n)
      (r : ℕ) (ξ : Fin r → X), Function.Injective ξ → (∀ i, Order.coheight (ξ i) = 1) →
      IsSNCFamily K n ξ →
      (∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier π hπ c₀ (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
          etaleCharts_cover) (z : X) = 0) →
      (∀ i, ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback π
          (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (z : X) = 0) →
      ∀ w : Fin r → ℝ, (∀ k, 0 ≤ w k) →
      (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
      (∃ k, w k ≠ 0) →
      (∀ w' : Fin r → ℝ, (∀ k, 0 ≤ w' k) →
        (∃ p ∈ π ⁻¹' ({x} : Set Y), ∀ k, w' k ≠ 0 → p ∈ closure ({ξ k} : Set X)) →
        weightExponentialObjective
          (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ c₀
            (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor c₀ +
              principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
            ((1 : ℕ) : ℝ))
          (fun i k => (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w ≤
        weightExponentialObjective
          (fun k => (((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ c₀
            (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor c₀ +
              principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
            ((1 : ℕ) : ℝ))
          (fun i k => (cartierCoefficient (cartierPullback π
            (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) t j w') →
      ∀ p : X, (closure ({p} : Set X) ∩ π ⁻¹' ({x} : Set Y)).Nonempty →
        InSNCProfilePolytope ξ 1 (crepantBoundaryCartier π hπ c₀ (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX
            etaleCharts_cover)
          (fun i => cartierPullback π (cartierSectionZeroDivisor (j • L) (s i) (hs i)))
          (fun i => (∑ k, w k * (cartierCoefficient (cartierPullback π
              (cartierSectionZeroDivisor (j • L) (s i) (hs i))) (ξ k) : ℝ)) /
            ∑ k, w k * ((((1 : ℕ) : ℝ) - cartierCoefficient (crepantBoundaryCartier π hπ c₀
              (1 : Y.functionFieldˣ) 1 (1 • (smoothCanonicalDivisor c₀ +
                principalCartierDivisor Y (1 : Y.functionFieldˣ))) cX etaleCharts_cover) (ξ k)) /
              ((1 : ℕ) : ℝ))) p →
        p ∈ π ⁻¹' ({x} : Set Y)) :
    KltIsolationMinimizerData c₀ (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y (1 : Y.functionFieldˣ))) L m₀
      x := by
  obtain ⟨X, hXi, hXo, hXN, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, hinj, hξ, hsnc, hBsupp,
    hDsupp⟩ := exists_proper_snc_model_with c₀ (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (fun i => cartierSectionZeroDivisor (j • L) (s i) (hs i))
  have hXprop : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := π) (S := Spec (CommRingCat.of K))]
    infer_instance
  obtain ⟨w₁, hw₁0, hw₁Φ, hint⟩ := exists_interior_sncWeight_of_smooth_point π hπ hn hN c₀ cX ξ
    hinj hξ hsnc hBsupp (j • L) s hs hDsupp x β ht hj hζ hδ hF
  exact kltIsolationMinimizerData_of_sncWeight_minimizer c₀ (1 : Y.functionFieldˣ) 1 le_rfl
    (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
    (smooth_logPairIsKlt_boundary_zero c₀ (1 : Y.functionFieldˣ) 1 le_rfl) L m₀ x j hj hjm₀ hN s hs
    i₀ hi₀ X π hπ cX ξ hinj hξ hsnc hBsupp hDsupp ht
    (by rw [Nat.cast_one, one_mul]; exact ht1) w₁ hw₁0 hw₁Φ hint
    (hpc X π hπ cX r ξ hinj hξ hsnc hBsupp hDsupp)

end MinimizerData

end MixedFujita
