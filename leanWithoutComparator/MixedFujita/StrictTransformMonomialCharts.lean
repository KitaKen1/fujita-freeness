/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformMember

/-!
Strict transform charts with the Jacobian as a quotient of monomials (step 9).

At the codimension-one point e of the model where the coordinate v_l vanishes, only the l-th
exponents matter, and the order of det J along e is nonnegative because det J is regular. So the
factorizations need not compare exponents: if det J(ψ) J'' (∏ v_s^{η_s}) = (∏ v_s^{κ_s}) J' with
J', J'' units at the point, the log discrepancy of e is 1 + κ_l − η_l
(`modelThresholdBadAt_of_affine_model_of_monomials`, and on spectra
`modelThresholdBadAt_spec_of_affine_model_of_monomials`). For the strict transform model this
removes the hypothesis η ≤ κ of check-334 (the effectivity of the relative canonical divisor of
H' → H along all coordinates), which is now a consequence along the meeting component
(`modelThresholdBadAt_hyperplane_of_strictTransform_of_monomials`): the factorizations of det J(μ)
and of w combine to det J(ρ μ̄) J_1 W_2 (∏ v^η) = (∏ v^κ) J_2 W_1 without cancellation. The weaker
`StrictTransformMonomialChartStatement` follows from the unit charts of check-334
(`strictTransformMonomialChartStatement_of_strictTransformUnitChartStatement`) and implies the
quotient case (`coordinateHyperplaneQuotientRestriction_of_strictTransformMonomialCharts`), so F1
follows from sum KV and these charts (`mixedFujitaFreeness_of_kvSum_of_strictTransformMonomialCharts`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section AffineModel

variable {K : Type u} [Field K] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra
  functionFieldBaseAlgebra specAlgebraOver

variable {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- A bad point from an affine model, with the Jacobian known as a quotient of monomials up to
units at the point: det J(ψ) J'' (∏ v_s^{η_s}) = (∏ v_s^{κ_s}) J', and ψ(g_j) V_j = v_l^a r_j with
J', J'', V_j ∉ 𝔓; the log discrepancy is 1 + κ_l − η_l. -/
theorem modelThresholdBadAt_of_affine_model_of_monomials (cY c : EtaleChart K Y n) {B : Type u}
    [CommRing B] [IsDomain B] [Algebra K B] (ψ : Γ(Y, c.U) →ₐ[K] B) (hψ : Function.Injective ψ)
    (hbir : ∀ b : B, ∃ r s : Γ(Y, c.U), s ≠ 0 ∧ ψ s * b = ψ r)
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.Etale)
    (hvfe : v.toRingHom.FormallyEtale) (y : Y) (hy : y ∈ c.U) (𝔓 : Ideal B) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap ψ = (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal) (l : Fin n)
    (hl : v (MvPolynomial.X l) ∈ 𝔓) (κ η : Fin n → ℕ) (J' J'' : B) (hJ' : J' ∉ 𝔓)
    (hJ'' : J'' ∉ 𝔓)
    (hJ : (etaleRelativeJacobian ψ c.coords v hvfe).det * J'' * (∏ s, v (MvPolynomial.X s) ^ η s) =
      (∏ s, v (MvPolynomial.X s) ^ κ s) * J')
    {ι : Type*} (g : ι → Γ(Y, c.U)) (a : ℕ)
    (hg : ∀ j, ∃ r V : B, V ∉ 𝔓 ∧ ψ (g j) * V = v (MvPolynomial.X l) ^ a * r) (M : ℕ)
    (hM : (M : ℤ) * (1 + ((κ l : ℤ) - η l)) ≤ a) :
    ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
      (fun j => Y.germToFunctionField c.U (g j)) M := by
  classical
  -- the algebra is smooth over the field and Noetherian
  let _ : Algebra (MvPolynomial (Fin n) K) B := v.toRingHom.toAlgebra
  have : IsScalarTower K (MvPolynomial (Fin n) K) B :=
    IsScalarTower.of_algebraMap_eq fun k => (v.commutes k).symm
  have hEt : Algebra.Etale (MvPolynomial (Fin n) K) B := hv
  have : Algebra.Smooth K (MvPolynomial (Fin n) K) := {}
  have hSm : Algebra.Smooth K B := Algebra.Smooth.comp K (MvPolynomial (Fin n) K) B
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have : Nonempty c.U := c.nonempty
  -- the model
  have hrel := specAlgebraOver_smoothOfRelativeDimension (K := K) B v hvfe
  have : Smooth (Spec (CommRingCat.of B) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth n _
  have hdom := specAlgebraHom_isDominant c.isAffine ψ hψ
  have hover := specAlgebraHom_isOver c.isAffine ψ
  have hbij := specAlgebraHom_functionField_bijective c.isAffine ψ hψ hbir
  have hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (specAlgebraHom c.isAffine ψ)) :=
    hbij
  let cB := specAlgebraEtaleChart (K := K) v hvfe
  -- the prime divisor: a minimal prime of v_l inside 𝔓
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {v (MvPolynomial.X l)} ≤ 𝔓 from (Ideal.span_singleton_le_iff_mem _).mpr hl)
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  have hmem : v (MvPolynomial.X l) ∈ 𝔮 := h𝔮min.1.2 (Ideal.subset_span rfl)
  have hvl0 : v (MvPolynomial.X l) ≠ 0 := by
    intro h0
    apply etaleChart_coordinate_ne_zero cB l
    change (Scheme.ΓSpecIso (CommRingCat.of B)).inv (v (MvPolynomial.X l)) = 0
    rw [h0, map_zero]
  let e : Spec (CommRingCat.of B) := ⟨𝔮, h𝔮prime⟩
  have hcoh : Order.coheight e = 1 := by
    rw [← idealHeight_eq_coheight]
    change 𝔮.height = 1
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ 𝔮 h𝔮min
    · rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      rintro rfl
      exact hvl0 ((Submodule.mem_bot B).mp hmem)
  let eC : CodimensionOnePoint (Spec (CommRingCat.of B)) := ⟨e, hcoh⟩
  haveI : IsDiscreteValuationRing ((Spec (CommRingCat.of B)).presheaf.stalk (eC : _)) :=
    smoothOverField_codimensionOne_stalk_DVR (K := K) eC
  -- the centre
  have hcentre : y ∈ closure ({specAlgebraHom c.isAffine ψ (eC : _)} : Set Y) := by
    let x𝔓 : Spec (CommRingCat.of B) := ⟨𝔓, inferInstance⟩
    have h1 : specAlgebraHom c.isAffine ψ x𝔓 = y :=
      specAlgebraHom_apply_of_comap c.isAffine ψ x𝔓 y hy h𝔓
    have hspec : e ⤳ x𝔓 := (PrimeSpectrum.le_iff_specializes e x𝔓).mp h𝔮le
    have h2 := hspec.map (specAlgebraHom c.isAffine ψ).continuous
    rw [h1] at h2
    exact h2.mem_closure
  have hσe : specAlgebraHom c.isAffine ψ (eC : _) ∈ c.U := by
    change c.isAffine.fromSpec (Spec.map (CommRingCat.ofHom ψ.toRingHom) e) ∈ c.U
    have h : c.isAffine.fromSpec (Spec.map (CommRingCat.ofHom ψ.toRingHom) e) ∈
        Set.range c.isAffine.fromSpec := ⟨_, rfl⟩
    rwa [c.isAffine.range_fromSpec] at h
  -- the function field of the model
  let ι : B → (Spec (CommRingCat.of B)).functionField := fun b =>
    (Spec (CommRingCat.of B)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)
  have hιmul : ∀ a b, ι (a * b) = ι a * ι b := fun a b => by
    simp only [ι, map_mul]
  have hιpow : ∀ a (m : ℕ), ι (a ^ m) = ι a ^ m := fun a m => by
    simp only [ι, map_pow]
  have hι0 : ∀ b, b ≠ 0 → ι b ≠ 0 := by
    intro b hb h0
    apply hb
    have h1 := Scheme.germToFunctionField_injective (Spec (CommRingCat.of B)) ⊤
      (h0.trans (map_zero _).symm)
    exact (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.injective
      (h1.trans (map_zero _).symm)
  have hunit : ∀ b, b ∉ 𝔮 → (Spec (CommRingCat.of B)).ord (ι b) (eC : _) = 0 := by
    intro b hb
    have hu : IsUnit ((Spec (CommRingCat.of B)).presheaf.germ ⊤ (eC : _) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) :=
      (spec_germ_isUnit_iff (CommRingCat.of B) e b).mpr hb
    have h := scheme_ord_stalk_unit (eC : Spec (CommRingCat.of B)) hu.unit
    rwa [IsUnit.unit_spec, Scheme.algebraMap_germ_eq_germToFunctionField] at h
  have hregular : ∀ b, 0 ≤ (Spec (CommRingCat.of B)).ord (ι b) (eC : _) := by
    intro b
    refine scheme_ord_nonneg_of_mem_stalk (eC : Spec (CommRingCat.of B)) _ ⟨(Spec
      (CommRingCat.of B)).presheaf.germ ⊤ (eC : _) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b), ?_⟩
    exact Scheme.algebraMap_germ_eq_germToFunctionField _ _ _
  -- the coordinate v_l is a non-unit at e, so the coordinates have orders δ_sl there
  have hnu : ¬ IsUnit ((Spec (CommRingCat.of B)).presheaf.germ cB.U (eC : _) trivial
      (cB.coords (MvPolynomial.X l))) := by
    change ¬ IsUnit ((Spec (CommRingCat.of B)).presheaf.germ ⊤ e trivial
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (v (MvPolynomial.X l))))
    rw [spec_germ_isUnit_iff, not_not]
    exact hmem
  have hmono : ∀ m : Fin n → ℕ,
      (Spec (CommRingCat.of B)).ord (ι (∏ s, v (MvPolynomial.X s) ^ m s)) (eC : _) = m l := by
    intro m
    have h := etaleChart_coordinate_prod_pow_ord cB eC trivial l hnu m
    have hprod : ι (∏ s, v (MvPolynomial.X s) ^ m s) =
        ∏ s, etaleChartFunctionFieldCoords cB (MvPolynomial.X s) ^ m s := by
      simp only [ι, map_prod, map_pow]
      rfl
    rw [hprod, h]
  have hordl : (Spec (CommRingCat.of B)).ord (ι (v (MvPolynomial.X l))) (eC : _) = 1 := by
    have h := etaleChart_coordinate_ord_of_not_isUnit cB eC trivial l hnu l
    rw [ite_eq_left rfl, ← etaleChartFunctionFieldCoords_X] at h
    exact h
  -- the log discrepancy of e is 1 + κ_l
  have hP0 : ∀ m : Fin n → ℕ, (∏ s, v (MvPolynomial.X s) ^ m s) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ fun h0 =>
      etaleChart_coordinate_ne_zero cB s (by
        change (Scheme.ΓSpecIso (CommRingCat.of B)).inv (v (MvPolynomial.X s)) = 0
        rw [h0, map_zero])
  have hJ'0 : J' ≠ 0 := fun h0 => hJ' (h0 ▸ 𝔓.zero_mem)
  have hJ''0 : J'' ≠ 0 := fun h0 => hJ'' (h0 ▸ 𝔓.zero_mem)
  have hdet0 : (etaleRelativeJacobian ψ c.coords v hvfe).det ≠ 0 := by
    intro h0
    have h := hJ
    rw [h0, zero_mul, zero_mul] at h
    exact mul_ne_zero (hP0 κ) hJ'0 h.symm
  have hcoef0 : cartierCoefficient (logDiscrepancyDivisor n (specAlgebraHom c.isAffine ψ) hσ cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cB
      etaleCharts_cover) (eC : _) =
      (Spec (CommRingCat.of B)).ord (ι (etaleRelativeJacobian ψ c.coords v hvfe).det) (eC : _) := by
    rw [logDiscrepancyDivisor_boundary_zero (specAlgebraHom c.isAffine ψ) hσ cY 1 1 cB, one_nsmul]
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt
      (specAlgebraHom c.isAffine ψ) cY etaleCharts_cover cB etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective (specAlgebraHom c.isAffine ψ) hσ cY cB)
      (eC : _) c hσe cB trivial), IsUnit.unit_spec, chartRelativeJacobianDet_specAlgebraHom c ψ v hvfe]
  have hcoef : cartierCoefficient (logDiscrepancyDivisor n (specAlgebraHom c.isAffine ψ) hσ cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cB
      etaleCharts_cover) (eC : _) = (κ l : ℤ) - η l := by
    rw [hcoef0]
    have h1 : (Spec (CommRingCat.of B)).ord
        (ι ((etaleRelativeJacobian ψ c.coords v hvfe).det * J'' *
          (∏ s, v (MvPolynomial.X s) ^ η s))) (eC : _) =
        (Spec (CommRingCat.of B)).ord (ι ((∏ s, v (MvPolynomial.X s) ^ κ s) * J')) (eC : _) := by
      rw [hJ]
    rw [hιmul, hιmul, hιmul,
      Scheme.ord_mul (mul_ne_zero (hι0 _ hdet0) (hι0 _ hJ''0)) (hι0 _ (hP0 η)),
      Scheme.ord_mul (hι0 _ hdet0) (hι0 _ hJ''0), Scheme.ord_mul (hι0 _ (hP0 κ)) (hι0 _ hJ'0),
      hmono κ, hmono η, hunit J' (fun h => hJ' (h𝔮le h)),
      hunit J'' (fun h => hJ'' (h𝔮le h))] at h1
    linarith
  have hnonneg : 0 ≤ cartierCoefficient (logDiscrepancyDivisor n (specAlgebraHom c.isAffine ψ) hσ cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cB
      etaleCharts_cover) (eC : _) := by
    rw [hcoef0]
    exact hregular _
  refine ⟨Spec (CommRingCat.of B), inferInstance, inferInstance, specAlgebraOver B, hrel,
    specAlgebraHom c.isAffine ψ, hdom, hover, hσ, cB, eC, hcentre, ?_, ?_⟩
  · have h0 := hnonneg
    rw [hcoef] at h0 ⊢
    have h0' : (0 : ℝ) ≤ (((κ l : ℤ) - η l : ℤ) : ℝ) := by exact_mod_cast h0
    rw [Nat.cast_one, div_one]
    linarith
  · intro j hj
    rw [hcoef]
    obtain ⟨r, V, hV, hr⟩ := hg j
    have hgj : dominantFunctionFieldAlgHom (K := K) (specAlgebraHom c.isAffine ψ)
        (Y.germToFunctionField c.U (g j)) = ι (ψ (g j)) := by
      change (dominantFunctionFieldMap (specAlgebraHom c.isAffine ψ)).hom
          (Y.germToFunctionField c.U (g j)) = _
      rw [dominantFunctionFieldMap_germ _ c.U ⊤ (specAlgebraHom_top_le c.isAffine ψ),
        specAlgebraHom_appLE]
    have hψg : ψ (g j) ≠ 0 := by
      intro h0
      apply hj
      have : g j = 0 := hψ (h0.trans (map_zero ψ).symm)
      change Y.germToFunctionField c.U (g j) = 0
      rw [this, map_zero]
    have hV0 : V ≠ 0 := fun h0 => hV (h0 ▸ 𝔓.zero_mem)
    have hr0 : r ≠ 0 := fun h0 => mul_ne_zero hψg hV0 (by rw [hr, h0, mul_zero])
    have hord : (Spec (CommRingCat.of B)).ord ((dominantFunctionFieldMap
        (specAlgebraHom c.isAffine ψ)).hom (Y.germToFunctionField c.U (g j))) (eC : _) =
        a + (Spec (CommRingCat.of B)).ord (ι r) (eC : _) := by
      change (Spec (CommRingCat.of B)).ord (dominantFunctionFieldAlgHom (K := K)
        (specAlgebraHom c.isAffine ψ) (Y.germToFunctionField c.U (g j))) _ = _
      rw [hgj]
      have h1 : (Spec (CommRingCat.of B)).ord (ι (ψ (g j) * V)) (eC : _) =
          (Spec (CommRingCat.of B)).ord (ι (v (MvPolynomial.X l) ^ a * r)) (eC : _) := by
        rw [hr]
      rw [hιmul, hιmul, hιpow, Scheme.ord_mul (hι0 _ hψg) (hι0 _ hV0),
        Scheme.ord_mul (pow_ne_zero _ (hι0 _ hvl0)) (hι0 _ hr0), scheme_ord_pow (hι0 _ hvl0), hordl,
        mul_one, hunit V (fun h => hV (h𝔮le h)), add_zero] at h1
      exact h1
    change (M : ℝ) * ((((1 : ℕ) : ℝ) + ((((κ l : ℤ) - η l : ℤ)) : ℝ)) / ((1 : ℕ) : ℝ)) ≤
      (((Spec (CommRingCat.of B)).ord ((dominantFunctionFieldMap
        (specAlgebraHom c.isAffine ψ)).hom (Y.germToFunctionField c.U (g j))) (eC : _) : ℤ) : ℝ)
    rw [hord]
    have h1 := hregular r
    have h2 : (M : ℤ) * (1 + ((κ l : ℤ) - η l)) ≤
        (a : ℤ) + (Spec (CommRingCat.of B)).ord (ι r) (eC : _) := by
      linarith
    have h3 : (((M : ℤ) * (1 + ((κ l : ℤ) - η l)) : ℤ) : ℝ) ≤
        (((a : ℤ) + (Spec (CommRingCat.of B)).ord (ι r) (eC : _) : ℤ) : ℝ) := by
      exact_mod_cast h2
    simp only [Nat.cast_one, div_one]
    push_cast at h3 ⊢
    linarith

end AffineModel

section Spec

variable {K : Type u} [Field K] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra
  functionFieldBaseAlgebra specAlgebraOver

variable {R : Type u} [CommRing R] [IsDomain R] [Algebra K R]
  [SmoothOfRelativeDimension n (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of K))]

/-- A bad point of the spectrum of a domain with étale coordinates x from an affine model over
it, with the Jacobian known as a quotient of monomials up to units at the point. -/
theorem modelThresholdBadAt_spec_of_affine_model_of_monomials (cY : EtaleChart K (Spec (CommRingCat.of R)) n)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (hx : x.toRingHom.FormallyEtale) {B : Type u}
    [CommRing B] [IsDomain B] [Algebra K B] (ψ : R →ₐ[K] B) (hψ : Function.Injective ψ)
    (hbir : ∀ b : B, ∃ r s : R, s ≠ 0 ∧ ψ s * b = ψ r)
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.Etale)
    (hvfe : v.toRingHom.FormallyEtale) (χ : R →ₐ[K] K) (𝔓 : Ideal B) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap ψ = RingHom.ker χ.toRingHom) (l : Fin n) (hl : v (MvPolynomial.X l) ∈ 𝔓)
    (κ η : Fin n → ℕ) (J' J'' : B) (hJ' : J' ∉ 𝔓) (hJ'' : J'' ∉ 𝔓)
    (hJ : (etaleRelativeJacobian ψ x v hvfe).det * J'' * (∏ s, v (MvPolynomial.X s) ^ η s) =
      (∏ s, v (MvPolynomial.X s) ^ κ s) * J')
    {ι : Type*} (g : ι → R) (a : ℕ)
    (hg : ∀ j, ∃ r V : B, V ∉ 𝔓 ∧ ψ (g j) * V = v (MvPolynomial.X l) ^ a * r)
    (M : ℕ) (hM : (M : ℤ) * (1 + ((κ l : ℤ) - η l)) ≤ a) :
    ModelThresholdBadAt cY (1 : (Spec (CommRingCat.of R)).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor (Spec (CommRingCat.of R))
        (1 : (Spec (CommRingCat.of R)).functionFieldˣ))) (specAlgHomPoint χ)
      (fun j => (Spec (CommRingCat.of R)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (g j))) M := by
  let e := specTopAlgEquiv (K := K) R
  let c := specAlgebraEtaleChart (K := K) x hx
  let ψ₀ : Γ(Spec (CommRingCat.of R), c.U) →ₐ[K] B := ψ.comp e.symm.toAlgHom
  have hψ₀ : ∀ r, ψ₀ (e r) = ψ r := fun r => by
    change ψ (e.symm (e r)) = ψ r
    rw [AlgEquiv.symm_apply_apply]
  have hinj : Function.Injective ψ₀ := hψ.comp e.symm.injective
  have hbir₀ : ∀ b : B, ∃ r s : Γ(Spec (CommRingCat.of R), c.U), s ≠ 0 ∧ ψ₀ s * b = ψ₀ r := by
    intro b
    obtain ⟨r, s, hs, h⟩ := hbir b
    refine ⟨e r, e s, fun h0 => hs (e.injective (h0.trans (map_zero e).symm)), ?_⟩
    rw [hψ₀, hψ₀, h]
  have h𝔓₀ : 𝔓.comap ψ₀ = (c.isAffine.primeIdealOf ⟨specAlgHomPoint χ, trivial⟩).asIdeal := by
    ext r
    have h1 := specTopAlgEquiv_point_iff (K := K) χ r
    have h2 : r ∈ 𝔓.comap ψ₀ ↔ (χ.comp e.symm.toAlgHom) r = 0 := by
      rw [Ideal.mem_comap]
      change ψ (e.symm r) ∈ 𝔓 ↔ χ (e.symm r) = 0
      rw [← Ideal.mem_comap, h𝔓, RingHom.mem_ker]
      rfl
    exact h2.trans h1
  have hjac : etaleRelativeJacobian ψ₀ c.coords v hvfe = etaleRelativeJacobian ψ x v hvfe := by
    ext i j
    change etaleCoordinateDerivation v hvfe j
        (ψ (e.symm ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (x (MvPolynomial.X i))))) =
      etaleCoordinateDerivation v hvfe j (ψ (x (MvPolynomial.X i)))
    rw [← specTopAlgEquiv_apply (K := K), AlgEquiv.symm_apply_apply]
  exact modelThresholdBadAt_of_affine_model_of_monomials cY c ψ₀ hinj hbir₀ v hv hvfe
    (specAlgHomPoint χ) trivial 𝔓 h𝔓₀ l hl κ η J' J'' hJ' hJ'' (by rw [hjac]; exact hJ)
    (fun j => e (g j)) a (fun j => by
      obtain ⟨r, V, hV, hr⟩ := hg j
      exact ⟨r, V, hV, by rw [hψ₀, hr]⟩) M hM

end Spec

section StrictTransform

variable {K : Type u} [Field K] {N : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra
  functionFieldBaseAlgebra specAlgebraOver

variable {A C : Type u} [CommRing A] [Algebra K A] [CommRing C] [Algebra K C]

/-- The strict transform of the coordinate hyperplane as a model, with the factorizations of
det J(μ), of w = μ(x_0)/y_0 and of the functions in B up to factors not in the prime of the point
and no comparison of the exponents: the discrepancy along the l-th coordinate is κ_l − η_l. -/
theorem modelThresholdBadAt_hyperplane_of_strictTransform_of_monomials
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    [IsDomain (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})]
    [SmoothOfRelativeDimension N
      (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})) ↘ Spec (CommRingCat.of K))]
    (cZ : EtaleChart K (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))) N)
    (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] C) (hy : y.toRingHom.FormallyEtale)
    (μ : A →ₐ[K] C) (w : C) (hw : μ (φ (MvPolynomial.X 0)) = y (MvPolynomial.X 0) * w)
    {B : Type u} [CommRing B] [IsDomain B] [Algebra K B]
    (ρ : C ⧸ Ideal.span {y (MvPolynomial.X 0)} →ₐ[K] B)
    (hv : (ρ.comp (hyperplaneCoords y)).toRingHom.Etale)
    (hvfe : (ρ.comp (hyperplaneCoords y)).toRingHom.FormallyEtale)
    (hψ : Function.Injective (ρ.comp (strictTransformHyperplaneMap φ y μ w hw)))
    (hbir : ∀ b : B, ∃ r s : A ⧸ Ideal.span {φ (MvPolynomial.X 0)}, s ≠ 0 ∧
      ρ (strictTransformHyperplaneMap φ y μ w hw s) * b =
        ρ (strictTransformHyperplaneMap φ y μ w hw r))
    (χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K) (𝔓 : Ideal B) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (ρ.comp (strictTransformHyperplaneMap φ y μ w hw)) = RingHom.ker χ.toRingHom)
    (l : Fin N) (hl : (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X l) ∈ 𝔓)
    (κ η : Fin N → ℕ) (J₁ J₂ W₁ W₂ : B)
    (hJ₁ : J₁ ∉ 𝔓) (hJ₂ : J₂ ∉ 𝔓) (hW₁ : W₁ ∉ 𝔓) (hW₂ : W₂ ∉ 𝔓)
    (hJμ : ρ (Ideal.Quotient.mk _ (etaleRelativeJacobian μ φ y hy).det) * J₁ =
      (∏ s, (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X s) ^ κ s) * J₂)
    (hwfac : ρ (Ideal.Quotient.mk _ w) * W₁ =
      (∏ s, (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X s) ^ η s) * W₂)
    {ι : Type*} (g : ι → A) (a : ℕ)
    (hg : ∀ j, ∃ r V : B, V ∉ 𝔓 ∧ ρ (Ideal.Quotient.mk _ (μ (g j))) * V =
      (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X l) ^ a * r) (M : ℕ)
    (hM : (M : ℤ) * (1 + ((κ l : ℤ) - η l)) ≤ a) :
    ModelThresholdBadAt cZ (1 : (Spec (CommRingCat.of
        (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cZ + principalCartierDivisor _ 1)) (specAlgHomPoint χ)
      (fun j => (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).germToFunctionField
        ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).inv
          (Ideal.Quotient.mk _ (g j)))) M := by
  classical
  let I : Ideal C := Ideal.span {y (MvPolynomial.X 0)}
  let μbar := strictTransformHyperplaneMap φ y μ w hw
  let v := ρ.comp (hyperplaneCoords y)
  have hdet : (etaleRelativeJacobian (ρ.comp μbar) (hyperplaneCoords φ) v hvfe).det =
      ρ (etaleRelativeJacobian μbar (hyperplaneCoords φ) (hyperplaneCoords y)
        (hyperplaneCoords_formallyEtale y hy)).det :=
    etaleRelativeJacobian_det_comp_coords μbar ρ (hyperplaneCoords φ) (hyperplaneCoords y)
      (hyperplaneCoords_formallyEtale y hy) hvfe
  have hadj : Ideal.Quotient.mk I (etaleRelativeJacobian μ φ y hy).det =
      Ideal.Quotient.mk I w * (etaleRelativeJacobian μbar (hyperplaneCoords φ) (hyperplaneCoords y)
        (hyperplaneCoords_formallyEtale y hy)).det :=
    etaleRelativeJacobian_det_quotient μ φ y hy w hw (span_le_comap_of_eq_mul φ y μ w hw)
  have hkey : ρ (Ideal.Quotient.mk I (etaleRelativeJacobian μ φ y hy).det) =
      ρ (Ideal.Quotient.mk I w) *
        (etaleRelativeJacobian (ρ.comp μbar) (hyperplaneCoords φ) v hvfe).det := by
    rw [hadj, map_mul, hdet]
  have hJ : (etaleRelativeJacobian (ρ.comp μbar) (hyperplaneCoords φ) v hvfe).det * (J₁ * W₂) *
      (∏ s, v (MvPolynomial.X s) ^ η s) = (∏ s, v (MvPolynomial.X s) ^ κ s) * (J₂ * W₁) := by
    have h1 : (∏ s, v (MvPolynomial.X s) ^ κ s) * J₂ * W₁ = ρ (Ideal.Quotient.mk I w) * W₁ *
        (etaleRelativeJacobian (ρ.comp μbar) (hyperplaneCoords φ) v hvfe).det * J₁ := by
      rw [← hJμ, hkey]
      ring
    rw [hwfac] at h1
    linear_combination -h1
  have hJ₁W₂ : J₁ * W₂ ∉ 𝔓 := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hJ₁ hW₂
  have hJ₂W₁ : J₂ * W₁ ∉ 𝔓 := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hJ₂ hW₁
  exact modelThresholdBadAt_spec_of_affine_model_of_monomials cZ (hyperplaneCoords φ)
    (hyperplaneCoords_formallyEtale φ hφ) (ρ.comp μbar) hψ hbir v hv hvfe χ 𝔓 h𝔓 l hl κ η
    (J₂ * W₁) (J₁ * W₂) hJ₂W₁ hJ₁W₂ hJ (fun j => Ideal.Quotient.mk _ (g j)) a (fun j => hg j) M hM

end StrictTransform

section Charts

variable (K : Type u) [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- Strict transform charts with the factorizations in B up to units and no comparison of the
exponents of det J(μ) and w: the weakening of `StrictTransformUnitChartStatement` in which only
the adjunction inequality M (1 + κ_l − η_l) ≤ a along the meeting component is asked. -/
def StrictTransformMonomialChartStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra K A] (N : ℕ)
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A), φ.toRingHom.FormallyEtale →
    ∀ [IsDomain (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})]
      {J : Type} [Finite J] (g : J → A) (M : ℕ), 1 ≤ N → 1 ≤ M →
      ∀ χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K,
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
          (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
        (specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))))
        (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
      ∃ (C : Type u) (_ : CommRing C) (_ : IsDomain C) (_ : Algebra K C)
        (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] C) (hy : y.toRingHom.FormallyEtale)
        (μ : A →ₐ[K] C) (_ : Function.Injective μ)
        (_ : ∀ c : C, ∃ r s : A, s ≠ 0 ∧ μ s * c = μ r) (w : C)
        (hw : μ (φ (MvPolynomial.X 0)) = y (MvPolynomial.X 0) * w)
        (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra K B)
        (ρ : C ⧸ Ideal.span {y (MvPolynomial.X 0)} →ₐ[K] B)
        (_ : (ρ.comp (hyperplaneCoords y)).toRingHom.Etale)
        (_ : (ρ.comp (hyperplaneCoords y)).toRingHom.FormallyEtale)
        (_ : ∀ a : A, ρ (Ideal.Quotient.mk _ (μ a)) = 0 ↔ a ∈ Ideal.span {φ (MvPolynomial.X 0)})
        (_ : ∀ b : B, ∃ c d : C, ρ (Ideal.Quotient.mk _ d) ≠ 0 ∧
          ρ (Ideal.Quotient.mk _ d) * b = ρ (Ideal.Quotient.mk _ c))
        (𝔓 : Ideal B) (_ : 𝔓.IsPrime)
        (_ : 𝔓.comap (ρ.comp (strictTransformHyperplaneMap φ y μ w hw)) =
          RingHom.ker χ.toRingHom)
        (l : Fin N) (_ : (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X l) ∈ 𝔓)
        (κ η : Fin N → ℕ) (J₁ J₂ W₁ W₂ : B)
        (_ : J₁ ∉ 𝔓) (_ : J₂ ∉ 𝔓) (_ : W₁ ∉ 𝔓) (_ : W₂ ∉ 𝔓)
        (_ : ρ (Ideal.Quotient.mk _ (etaleRelativeJacobian μ φ y hy).det) * J₁ =
          (∏ s, (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X s) ^ κ s) * J₂)
        (_ : ρ (Ideal.Quotient.mk _ w) * W₁ =
          (∏ s, (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X s) ^ η s) * W₂) (a : ℕ),
        (∀ j, ∃ r V : B, V ∉ 𝔓 ∧ ρ (Ideal.Quotient.mk _ (μ (g j))) * V =
          (ρ.comp (hyperplaneCoords y)) (MvPolynomial.X l) ^ a * r) ∧
          (M : ℤ) * (1 + ((κ l : ℤ) - η l)) ≤ a

variable {K}

/-- Strict transform charts with factorizations up to units give charts with factorizations as
quotients of monomials: `StrictTransformMonomialChartStatement` is the weaker statement. -/
theorem strictTransformMonomialChartStatement_of_strictTransformUnitChartStatement
    (h : StrictTransformUnitChartStatement K) : StrictTransformMonomialChartStatement K := by
  intro A _ _ _ N _ cX φ hφ _ J _ g M hN hM χ hbad
  obtain ⟨C, i1, i2, i3, y, hy, μ, hμ, hbirμ, w, hw, B, j1, j2, j3, ρ, hv, hvfe, hker, hρ, 𝔓, h𝔓p,
    h𝔓, l, hl, κ, η, hηκ, J₁, J₂, W₁, W₂, hJ₁, hJ₂, hW₁, hW₂, hJμ, hwfac, a, hg, hMa⟩ :=
    h A N cX φ hφ g M hN hM χ hbad
  refine ⟨C, i1, i2, i3, y, hy, μ, hμ, hbirμ, w, hw, B, j1, j2, j3, ρ, hv, hvfe, hker, hρ, 𝔓, h𝔓p,
    h𝔓, l, hl, κ, η, J₁, J₂, W₁, W₂, hJ₁, hJ₂, hW₁, hW₂, hJμ, hwfac, a, hg, ?_⟩
  have h1 : ((M * (1 + (κ l - η l)) : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast hMa
  have h2 : ((κ l - η l : ℕ) : ℤ) = (κ l : ℤ) - η l := Nat.cast_sub (hηκ l)
  push_cast [h2] at h1
  exact h1

/-- The restriction theorem for the coordinate hyperplane as a quotient from strict transform
charts with factorizations as quotients of monomials. -/
theorem coordinateHyperplaneQuotientRestriction_of_strictTransformMonomialCharts
    (h : StrictTransformMonomialChartStatement K) : CoordinateHyperplaneQuotientRestriction K := by
  classical
  intro A _ _ _ N _ cX φ hφ _ _ cZ J _ g M hN hM χ hbad
  obtain ⟨C, _, _, _, y, hy, μ, hμ, hbirμ, w, hw, B, _, _, _, ρ, hv, hvfe, hker, hρ, 𝔓, h𝔓p,
    h𝔓, l, hl, κ, η, J₁, J₂, W₁, W₂, hJ₁, hJ₂, hW₁, hW₂, hJμ, hwfac, a, hg, hMa⟩ :=
    h A N cX φ hφ g M hN hM χ hbad
  haveI := h𝔓p
  haveI : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := N + 1)
  haveI : (Ideal.span {φ (MvPolynomial.X 0)}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  haveI := valuationRing_localization_span_of_smooth (K := K) A (φ (MvPolynomial.X 0))
    (etaleCoordinate_ne_zero φ hφ 0)
  obtain ⟨hψ, hbir⟩ := strictTransformHyperplaneMap_injective_birational φ y μ hμ hbirμ w hw ρ
    hker hρ
  exact modelThresholdBadAt_hyperplane_of_strictTransform_of_monomials φ hφ cZ y hy μ w hw ρ hv
    hvfe hψ hbir χ 𝔓 h𝔓 l hl κ η J₁ J₂ W₁ W₂ hJ₁ hJ₂ hW₁ hW₂ hJμ hwfac g a hg M hMa

/-- F1 from sum KV and strict transform charts with factorizations as quotients of monomials. -/
theorem mixedFujitaFreeness_of_kvSum_of_strictTransformMonomialCharts
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hST : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      StrictTransformMonomialChartStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_coordinateHyperplaneQuotientRestriction hKV
    (fun K _ _ _ => coordinateHyperplaneQuotientRestriction_of_strictTransformMonomialCharts (hST K))

end Charts

end MixedFujita
