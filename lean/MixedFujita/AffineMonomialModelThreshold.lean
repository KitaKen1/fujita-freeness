/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FormalTestSNCBadComponent
public import MixedFujita.ThresholdArcSpecialization

/-!
Monomials satisfy the threshold in the model form wherever they satisfy the chart inequality.
Let x be a point of affine space and e a prime divisor of a smooth birational model σ : U → A^m
whose centre contains x. The coordinates X_a - x_a of the translated chart have orders ν_a ≥ 0 at e
and Σ ν_a ≤ 1 + k_e = A(e), where k_e is the coefficient of the relative canonical divisor (the
coordinate-sum inequality on actual models, `affineSpace_coordinate_sum_le_logDiscrepancy`). A
coordinate X_a with x_a ≠ 0 is a unit near the centre and has order zero; the others are the
X_a - x_a. So a monomial c X^β has order Σ_a β_a u_a with u_a = ν_a if x_a = 0 and u_a = 0
otherwise, and Σ u_a ≤ A(e). If for every nonzero natural u vanishing on the support of x some
monomial has Σ u_a β_a < h Σ u_a, no prime divisor has ord_e ≥ h A(e) on all of them
(`affineSpace_monomials_not_modelThresholdBadAt`). This chart inequality follows from (34) for the
monomials by the identity test in a chart containing x
(`monomial_chart_inequality_of_projectiveThresholdCondition`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPowerSeries
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section StalkOrder

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A germ at x has no pole at x. -/
theorem ord_algebraMap_stalk_nonneg (x : X) (a : X.presheaf.stalk x) :
    0 ≤ X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x := by
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty V := ⟨⟨x, hV⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  exact TauCeti.AlgebraicGeometry.Scheme.ord_germToFunctionField_nonneg s hV

/-- A unit of the local ring at x has order zero at x. -/
theorem ord_algebraMap_stalk_of_isUnit (x : X) {a : X.presheaf.stalk x} (ha : IsUnit a) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField a) x = 0 := by
  obtain ⟨v, rfl⟩ := ha
  have h1 := ord_algebraMap_stalk_nonneg x (v : X.presheaf.stalk x)
  have h2 := ord_algebraMap_stalk_nonneg x ((v⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x)
  rw [map_units_inv, TauCeti.AlgebraicGeometry.Scheme.ord_inv] at h2
  omega

/-- The order of a product of powers of nonzero rational functions. -/
theorem scheme_ord_prod_pow {ι : Type*} [Fintype ι] (f : ι → X.functionField)
    (hf : ∀ i, f i ≠ 0) (k : ι → ℕ) (t : X) :
    X.ord (∏ i, f i ^ k i) t = ∑ i, (k i : ℤ) * X.ord (f i) t := by
  classical
  have key : ∀ s : Finset ι,
      X.ord (∏ i ∈ s, f i ^ k i) t = ∑ i ∈ s, (k i : ℤ) * X.ord (f i) t := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        Scheme.ord_mul (pow_ne_zero _ (hf i))
          (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hf j)),
        ih, scheme_ord_pow (hf i)]
  exact key Finset.univ

end StalkOrder

section Pullback

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsIntegral Y]
  (σ : X ⟶ Y) [IsDominant σ]

/-- The pullback of a germ at σ(x) has no pole at x. -/
theorem ord_pullback_algebraMap_stalk_nonneg (x : X) (a : Y.presheaf.stalk (σ x)) :
    0 ≤ X.ord ((dominantFunctionFieldMap σ).hom
      (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField a)) x := by
  rw [dominantFunctionFieldMap_algebraMap]
  exact ord_algebraMap_stalk_nonneg x _

/-- The pullback of a unit at σ(x) has order zero at x. -/
theorem ord_pullback_algebraMap_stalk_of_isUnit (x : X) {a : Y.presheaf.stalk (σ x)}
    (ha : IsUnit a) :
    X.ord ((dominantFunctionFieldMap σ).hom
      (algebraMap (Y.presheaf.stalk (σ x)) Y.functionField a)) x = 0 := by
  rw [dominantFunctionFieldMap_algebraMap]
  exact ord_algebraMap_stalk_of_isUnit x (ha.map (σ.stalkMap x).hom)

end Pullback

section Affine

variable {K : Type u} [Field K] {m : ℕ}

attribute [local instance] specAlgebraOver affineSpace_smoothOfRelativeDimension

/-- A polynomial that does not vanish at p is a unit near every point whose closure contains p. -/
theorem affineSpace_germ_isUnit_of_eval_ne_zero (p : Fin m → K) (y : affineSpace K m)
    (hy : affineSpacePoint K m p ∈ closure ({y} : Set (affineSpace K m)))
    (P : MvPolynomial (Fin m) K) (hP : MvPolynomial.eval p P ≠ 0) :
    IsUnit ((affineSpace K m).presheaf.germ ⊤ y trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin m) K))).inv P)) := by
  rw [← Scheme.mem_basicOpen, basicOpen_eq_of_affine]
  have hmem : affineSpacePoint K m p ∈ PrimeSpectrum.basicOpen P := by
    rw [PrimeSpectrum.mem_basicOpen, affineSpacePoint_mem_iff]
    exact hP
  exact (specializes_iff_mem_closure.mpr hy).mem_open (PrimeSpectrum.basicOpen P).isOpen hmem

/-- The image of a polynomial in the function field of affine space is the image of its germ. -/
theorem affineSpace_coords_eq_algebraMap_germ (y : affineSpace K m)
    (P : MvPolynomial (Fin m) K) :
    etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P =
      algebraMap ((affineSpace K m).presheaf.stalk y) (affineSpace K m).functionField
        ((affineSpace K m).presheaf.germ ⊤ y trivial
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin m) K))).inv P)) := by
  have : Nonempty (⊤ : (affineSpace K m).Opens) := ⟨⟨y, trivial⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]
  rfl

section Model

variable {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
  (σ : U ⟶ affineSpace K m) [IsDominant σ]

/-- A polynomial has no pole on a birational model of affine space. -/
theorem affineSpace_ord_pullback_coords_nonneg (t : U) (P : MvPolynomial (Fin m) K) :
    0 ≤ U.ord ((dominantFunctionFieldMap σ).hom
      (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P)) t := by
  rw [affineSpace_coords_eq_algebraMap_germ (σ t)]
  exact ord_pullback_algebraMap_stalk_nonneg σ t _

/-- A polynomial not vanishing at p has order zero at every point whose image specializes to p. -/
theorem affineSpace_ord_pullback_coords_eq_zero (t : U) (p : Fin m → K)
    (hp : affineSpacePoint K m p ∈ closure ({σ t} : Set (affineSpace K m)))
    (P : MvPolynomial (Fin m) K) (hP : MvPolynomial.eval p P ≠ 0) :
    U.ord ((dominantFunctionFieldMap σ).hom
      (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P)) t = 0 := by
  rw [affineSpace_coords_eq_algebraMap_germ (σ t)]
  exact ord_pullback_algebraMap_stalk_of_isUnit σ t
    (affineSpace_germ_isUnit_of_eval_ne_zero p (σ t) hp P hP)

omit [IsLocallyNoetherian U] in
theorem affineSpace_pullback_coords_ne_zero {P : MvPolynomial (Fin m) K} (hP : P ≠ 0) :
    (dominantFunctionFieldMap σ).hom
      (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P) ≠ 0 := by
  rw [map_ne_zero]
  intro h0
  exact hP (affineSpaceEtaleChart_functionFieldCoords_injective K m (h0.trans (map_zero _).symm))

/-- The order of a monomial at a point whose image specializes to p. -/
theorem affineSpace_ord_pullback_monomial (t : U) (p : Fin m → K)
    (hp : affineSpacePoint K m p ∈ closure ({σ t} : Set (affineSpace K m)))
    (β : Fin m →₀ ℕ) {c : K} (hc : c ≠ 0) :
    U.ord ((dominantFunctionFieldMap σ).hom (etaleChartFunctionFieldCoords
        (affineSpaceEtaleChart K m) (MvPolynomial.monomial β c))) t =
      ∑ a, (β a : ℤ) * U.ord ((dominantFunctionFieldMap σ).hom (etaleChartFunctionFieldCoords
        (affineSpaceEtaleChart K m) (MvPolynomial.X a))) t := by
  classical
  have hC : (MvPolynomial.C c : MvPolynomial (Fin m) K) ≠ 0 := by simpa using hc
  have hX : ∀ a : Fin m, (MvPolynomial.X a : MvPolynomial (Fin m) K) ≠ 0 :=
    fun a => MvPolynomial.X_ne_zero a
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun a => pow_zero _), map_mul, map_mul,
    map_prod, map_prod]
  simp_rw [map_pow]
  rw [Scheme.ord_mul (affineSpace_pullback_coords_ne_zero σ hC)
      (Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _
        (affineSpace_pullback_coords_ne_zero σ (hX a))),
    affineSpace_ord_pullback_coords_eq_zero σ t p hp _ (by simpa using hc), zero_add,
    scheme_ord_prod_pow _ (fun a => affineSpace_pullback_coords_ne_zero σ (hX a))]

end Model

/-- The translation X_a ↦ X_a - x_a of the variables. -/
noncomputable def translationAlgHom (x : Fin m → K) :
    MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval fun a => MvPolynomial.X a - MvPolynomial.C (x a)

theorem translationAlgHom_X (x : Fin m → K) (a : Fin m) :
    translationAlgHom x (MvPolynomial.X a) = MvPolynomial.X a - MvPolynomial.C (x a) :=
  MvPolynomial.aeval_X _ a

theorem translationAlgHom_comp_neg (x : Fin m → K) :
    (translationAlgHom x).comp (translationAlgHom (fun a => -x a)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [translationAlgHom]

theorem translationAlgHom_bijective (x : Fin m → K) :
    Function.Bijective (translationAlgHom x) := by
  have h1 := translationAlgHom_comp_neg x
  have h2 := translationAlgHom_comp_neg (fun a => -x a)
  simp only [neg_neg] at h2
  exact (AlgEquiv.ofAlgHom _ _ h1 h2).bijective

/-- Polynomials as an algebra over polynomials through a translation of the variables. -/
def TranslatedPolynomial (K : Type u) [Field K] (m : ℕ) (_x : Fin m → K) : Type u :=
  MvPolynomial (Fin m) K

noncomputable instance (x : Fin m → K) : CommRing (TranslatedPolynomial K m x) :=
  (inferInstance : CommRing (MvPolynomial (Fin m) K))

noncomputable instance (x : Fin m → K) :
    Algebra (MvPolynomial (Fin m) K) (TranslatedPolynomial K m x) :=
  (translationAlgHom x).toRingHom.toAlgebra

theorem translationAlgHom_formallyEtale (x : Fin m → K) :
    (translationAlgHom x).toRingHom.FormallyEtale := by
  have h : Algebra.FormallyEtale (MvPolynomial (Fin m) K) (TranslatedPolynomial K m x) :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective
      (Algebra.ofId (MvPolynomial (Fin m) K) (TranslatedPolynomial K m x))
      (translationAlgHom_bijective x))
  exact h

/-- The étale chart of affine space with the coordinates X_a - x_a. -/
noncomputable def affineSpaceTranslatedChart (x : Fin m → K) :
    EtaleChart K (affineSpace K m) m where
  U := ⊤
  isAffine := isAffineOpen_top _
  nonempty := ⟨⟨genericPoint _, trivial⟩⟩
  coords := specAlgebraCoords (translationAlgHom x)
  formallyEtale := specAlgebraCoords_formallyEtale _ (translationAlgHom_formallyEtale x)

theorem affineSpaceTranslatedChart_coordinate (x : Fin m → K) (a : Fin m) :
    (etaleChartCoordinateRationalUnit (affineSpaceTranslatedChart x) a :
        (affineSpace K m).functionField) =
      etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m)
        (MvPolynomial.X a - MvPolynomial.C (x a)) := by
  rw [← translationAlgHom_X]
  rfl

section LogDiscrepancy

variable {U : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U]
  [U.Over (Spec (CommRingCat.of K))] [SmoothOfRelativeDimension m (U ↘ Spec (CommRingCat.of K))]
  (σ : U ⟶ affineSpace K m) [IsDominant σ] [σ.IsOver (Spec (CommRingCat.of K))]
  (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))

/-- The log discrepancy of a prime divisor over affine space bounds the sum of the orders of the
coordinates centred at any point. -/
theorem affineSpace_coordinate_sum_le_logDiscrepancy (cU : EtaleChart K U m)
    (e : CodimensionOnePoint U) (x : Fin m → K) :
    ∑ a, U.ord ((dominantFunctionFieldMap σ).hom (etaleChartFunctionFieldCoords
        (affineSpaceEtaleChart K m) (MvPolynomial.X a - MvPolynomial.C (x a)))) (e : U) ≤
      1 + cartierCoefficient (logDiscrepancyDivisor m σ hσ (affineSpaceEtaleChart K m) 1 1
        (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K m) +
          principalCartierDivisor (affineSpace K m) 1)) cU etaleCharts_cover) (e : U) := by
  set c := affineSpaceEtaleChart K m with hc
  have hlog : logDiscrepancyDivisor m σ hσ c 1 1
      (1 • (smoothCanonicalDivisor c + principalCartierDivisor (affineSpace K m) 1)) cU
      etaleCharts_cover =
      birationalRelativeCanonicalDivisor m σ hσ c etaleCharts_cover cU etaleCharts_cover := by
    have h := logDiscrepancyDivisor_boundary_add σ hσ c 1 1 0 cU
    rw [add_zero, cartierPullback_zero, sub_zero] at h
    rw [h, one_smul]
  have hcov : (e : U) ∈ iSup (fun c' : EtaleChart K U m => c'.U) := by
    rw [etaleCharts_cover]
    trivial
  obtain ⟨cS, hcS⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  have hR := isUnit_chartRelativeJacobianDet_of_bijective σ hσ c cU
  have hJloc := relativeCanonicalDivisor_isLocalEquationAt σ c etaleCharts_cover cU
    etaleCharts_cover hR (e : U) (affineSpaceTranslatedChart x) trivial cS hcS
  have hk : cartierCoefficient
      (birationalRelativeCanonicalDivisor m σ hσ c etaleCharts_cover cU etaleCharts_cover) (e : U) =
      U.ord (chartRelativeJacobianDet σ (affineSpaceTranslatedChart x) cS) (e : U) :=
    cartierCoefficient_eq_ord hJloc
  have hsum := actual_chart_coordinate_sum_le_jacobian σ hσ e (affineSpaceTranslatedChart x)
    trivial cS hcS
  simp_rw [affineSpaceTranslatedChart_coordinate] at hsum
  rw [hlog, hk]
  exact hsum

end LogDiscrepancy

/-- Monomials satisfying the chart inequality at x satisfy the threshold at x in the model form. -/
theorem affineSpace_monomials_not_modelThresholdBadAt {ι : Type*} [Nonempty ι]
    (β : ι → Fin m →₀ ℕ) (c₀ : ι → K) (hc₀ : ∀ ℓ, c₀ ℓ ≠ 0) (x : Fin m → K) (h : ℕ)
    (hh : 1 ≤ h)
    (hcomb : ∀ u : Fin m → ℕ, (∀ a, x a ≠ 0 → u a = 0) → u ≠ 0 →
      ∃ ℓ, ∑ a, u a * β ℓ a < h * ∑ a, u a) :
    ¬ ModelThresholdBadAt (affineSpaceEtaleChart K m) 1 1
      (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K m) +
        principalCartierDivisor (affineSpace K m) 1))
      (affineSpacePoint K m x)
      (fun ℓ => etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m)
        (MvPolynomial.monomial (β ℓ) (c₀ ℓ))) h := by
  classical
  rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hx, hApos, hall⟩
  set A := cartierCoefficient (logDiscrepancyDivisor m σ hσ (affineSpaceEtaleChart K m) 1 1
    (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K m) +
      principalCartierDivisor (affineSpace K m) 1)) cU etaleCharts_cover) (e : U) with hA
  set μ : Fin m → ℤ := fun a => U.ord ((dominantFunctionFieldMap σ).hom
    (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) (MvPolynomial.X a))) (e : U)
    with hμ
  set ν : Fin m → ℤ := fun a => U.ord ((dominantFunctionFieldMap σ).hom
    (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m)
      (MvPolynomial.X a - MvPolynomial.C (x a)))) (e : U) with hν
  have hμ0 : ∀ a, 0 ≤ μ a := fun a => affineSpace_ord_pullback_coords_nonneg σ (e : U) _
  have hν0 : ∀ a, 0 ≤ ν a := fun a => affineSpace_ord_pullback_coords_nonneg σ (e : U) _
  have hμx : ∀ a, x a ≠ 0 → μ a = 0 := fun a ha =>
    affineSpace_ord_pullback_coords_eq_zero σ (e : U) x hx _ (by simpa using ha)
  have hνμ : ∀ a, x a = 0 → ν a = μ a := fun a ha => by
    simp only [hν, hμ, ha, map_zero, sub_zero]
  set u : Fin m → ℕ := fun a => if x a = 0 then (μ a).toNat else 0 with hu
  have hu0 : ∀ a, x a ≠ 0 → u a = 0 := fun a ha => by simp [hu, ha]
  have huμ : ∀ a, (u a : ℤ) = μ a := by
    intro a
    by_cases ha : x a = 0
    · simp only [hu, ha, ite_true]
      exact Int.toNat_of_nonneg (hμ0 a)
    · simp only [hu, ha, ite_false, Nat.cast_zero]
      exact (hμx a ha).symm
  have huν : ∀ a, (u a : ℤ) ≤ ν a := by
    intro a
    by_cases ha : x a = 0
    · rw [huμ, hνμ a ha]
    · simp only [hu, ha, ite_false, Nat.cast_zero]
      exact hν0 a
  have hsumA : (∑ a, (u a : ℤ)) ≤ 1 + A :=
    (Finset.sum_le_sum fun a _ => huν a).trans
      (affineSpace_coordinate_sum_le_logDiscrepancy σ hσ cU e x)
  have hord : ∀ ℓ, U.ord ((dominantFunctionFieldMap σ).hom (etaleChartFunctionFieldCoords
      (affineSpaceEtaleChart K m) (MvPolynomial.monomial (β ℓ) (c₀ ℓ)))) (e : U) =
      ∑ a, (u a : ℤ) * (β ℓ a : ℤ) := by
    intro ℓ
    rw [affineSpace_ord_pullback_monomial σ (e : U) x hx (β ℓ) (hc₀ ℓ)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [huμ a, mul_comm]
  have hApos' : (0 : ℤ) < 1 + A := by
    have h1 : (0 : ℝ) < 1 + (A : ℝ) := by simpa [Nat.cast_one, div_one] using hApos
    exact_mod_cast h1
  have hbadℓ : ∀ ℓ, (h : ℤ) * (1 + A) ≤ ∑ a, (u a : ℤ) * (β ℓ a : ℤ) := by
    intro ℓ
    have hne : etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m)
        (MvPolynomial.monomial (β ℓ) (c₀ ℓ)) ≠ 0 := fun h0 =>
      (MvPolynomial.monomial_eq_zero.not.mpr (hc₀ ℓ))
        (affineSpaceEtaleChart_functionFieldCoords_injective K m (h0.trans (map_zero _).symm))
    have h1 := hall ℓ hne
    rw [hord ℓ] at h1
    simp only [Nat.cast_one, div_one] at h1
    exact_mod_cast h1
  have hh' : (1 : ℤ) ≤ h := by exact_mod_cast hh
  by_cases hu' : u = 0
  · obtain ⟨ℓ⟩ := ‹Nonempty ι›
    have h1 := hbadℓ ℓ
    simp only [hu', Pi.zero_apply, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h1
    nlinarith
  · obtain ⟨ℓ, hℓ⟩ := hcomb u hu0 hu'
    have h1 := hbadℓ ℓ
    have h2 : (∑ a, (u a : ℤ) * (β ℓ a : ℤ)) < (h : ℤ) * ∑ a, (u a : ℤ) := by
      exact_mod_cast hℓ
    have h3 : (h : ℤ) * ∑ a, (u a : ℤ) ≤ (h : ℤ) * (1 + A) :=
      mul_le_mul_of_nonneg_left hsumA (by positivity)
    linarith

/-- (34) for monomials gives the chart inequality at every point x, by the identity test in a
chart containing x. -/
theorem monomial_chart_inequality_of_projectiveThresholdCondition [DecidableEq K] {ι : Type*}
    (β : ι → Fin m →₀ ℕ) (c₀ : ι → K) (h : ℕ)
    (hcond : ProjectiveThresholdCondition (fun ℓ => MvPolynomial.monomial (β ℓ) (c₀ ℓ)) h)
    (x : Fin m → K) (k : Fin m) (hk : x k ≠ 0) (u : Fin m → ℕ)
    (hu0 : ∀ a, x a ≠ 0 → u a = 0) (hu : u ≠ 0) :
    ∃ ℓ, ∑ a, u a * β ℓ a < h * ∑ a, u a := by
  classical
  have huk : u k = 0 := hu0 k hk
  set w' : {i : Fin m // i ≠ k} → ℕ := fun i => u i with hw'
  have hw'ne : w' ≠ 0 := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hu
    have hak : a ≠ k := fun hak => ha (by rw [hak, huk]; rfl)
    exact Function.ne_iff.mpr ⟨⟨a, hak⟩, ha⟩
  have hsub : ∀ F : Fin m → ℕ, F k = 0 → ∑ i : {i : Fin m // i ≠ k}, F i = ∑ a, F a := by
    intro F hF
    rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ k), hF, zero_add,
      Finset.sum_subtype (p := fun i => i ≠ k) (Finset.univ.erase k) (fun i => by simp)]
  have hX : ∀ i, (AlgHom.id K (MvPowerSeries {i : Fin m // i ≠ k} K)) (X i) ≠ 0 := by
    intro i hi
    have hci := congrArg (coeff (Finsupp.single i 1)) hi
    rw [AlgHom.id_apply, coeff_index_single_self_X, map_zero] at hci
    exact one_ne_zero hci
  obtain ⟨ℓ, hℓ⟩ := hcond k (fun i => x i / x k) (AlgHom.id K _) hX
    (by rw [powerSeriesJacobian_id, Matrix.det_one]; exact one_ne_zero) w' hw'ne
  refine ⟨ℓ, ?_⟩
  rw [powerSeriesJacobian_id, Matrix.det_one, weightedOrder_one, add_zero, AlgHom.id_apply] at hℓ
  have hXord : ∀ i, (X i : MvPowerSeries {i : Fin m // i ≠ k} K).weightedOrder w' = w' i := by
    intro i
    rw [MvPowerSeries.X, weightedOrder_monomial_of_ne_zero w' one_ne_zero, Finsupp.weight_single,
      one_smul]
  have hlow : ((∑ a, u a * β ℓ a : ℕ) : ℕ∞) ≤
      (chartShiftedForm k (fun i => x i / x k)
        (MvPolynomial.monomial (β ℓ) (c₀ ℓ))).weightedOrder w' := by
    rw [chartShiftedForm_monomial]
    refine le_trans ?_ (le_weightedOrder_mul w')
    refine le_trans ?_ (add_le_add zero_le (le_weightedOrder_prod w' _ _))
    rw [zero_add, ← hsub (fun a => u a * β ℓ a) (by simp [huk]), Nat.cast_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans ?_ (le_weightedOrder_pow w' (β ℓ i))
    rw [nsmul_eq_mul]
    by_cases hxi : x i = 0
    · have hp0 : x i / x k = 0 := by rw [hxi, zero_div]
      rw [hp0, map_zero, zero_add, hXord, Nat.cast_mul, mul_comm]
    · rw [hu0 i hxi, zero_mul, Nat.cast_zero]
      exact zero_le
  have h2 : ((∑ a, u a * β ℓ a : ℕ) : ℕ∞) < ((h * ∑ a, u a : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul, ← hsub u huk]
    exact lt_of_le_of_lt hlow hℓ
  exact_mod_cast h2

end Affine

end MixedFujita
