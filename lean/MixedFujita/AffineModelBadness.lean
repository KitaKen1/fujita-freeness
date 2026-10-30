/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateHyperplaneJacobian

/-!
Bad points from affine models with étale coordinates (step 9, toward the restriction theorem).

Let c be an étale chart of an integral scheme Y over K and ψ : Γ(Y, c.U) → B an injective birational
K-algebra map to a domain B with étale coordinates v. On the model Spec B → Y (the affine models of
step 12) the chart Jacobian is the image of the relative Jacobian det J(ψ) of the algebra map in
the coordinates of c and v (`chartRelativeJacobianDet_specAlgebraHom`). If the coordinate v_l lies
in a prime 𝔓 over a point y, det J(ψ) = (∏ v_s^{κ_s}) J' with J' ∉ 𝔓, and every ψ(g_j) is
divisible by v_l^a with M (1 + κ_l) ≤ a, then y is a bad point of the g_j
(`modelThresholdBadAt_of_affine_model`): at the codimension-one point e of the model where v_l
vanishes, a minimal prime of v_l inside 𝔓, the log discrepancy is 1 + ord_e(det J) = 1 + κ_l
(v_l is a uniformizer at e, the other coordinates and J' are units there) and ord_e(g_j) ≥ a.
With the Jacobian on coordinate hyperplanes (check-326) this is the model of the strict transform
in the restriction theorem.
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

/-- The étale chart of the spectrum of a domain given by global étale coordinates. -/
noncomputable def specAlgebraEtaleChart {B : Type u} [CommRing B] [IsDomain B] [Algebra K B]
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.FormallyEtale) :
    EtaleChart K (Spec (CommRingCat.of B)) n :=
  ⟨⊤, isAffineOpen_top _, ⟨⟨genericPoint _, trivial⟩⟩, specAlgebraCoords v,
    specAlgebraCoords_formallyEtale v hv⟩

variable {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]

/-- The chart Jacobian of the morphism from the spectrum of an algebra is the image of the
relative Jacobian of the algebra map. -/
theorem chartRelativeJacobianDet_specAlgebraHom (c : EtaleChart K Y n) {B : Type u} [CommRing B]
    [IsDomain B] [Algebra K B] (ψ : Γ(Y, c.U) →ₐ[K] B)
    [IsDominant (specAlgebraHom c.isAffine ψ)]
    [(specAlgebraHom c.isAffine ψ).IsOver (Spec (CommRingCat.of K))]
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.FormallyEtale) :
    chartRelativeJacobianDet (specAlgebraHom c.isAffine ψ) c (specAlgebraEtaleChart v hv) =
      (Spec (CommRingCat.of B)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (etaleRelativeJacobian ψ c.coords v hv).det) := by
  have : Nonempty c.U := c.nonempty
  let ι : B →ₐ[K] (Spec (CommRingCat.of B)).functionField :=
    (sectionGermAlgHom (X := Spec (CommRingCat.of B)) ⊤).comp
      (specTopAlgEquiv (K := K) B).toAlgHom
  have hB : etaleChartFunctionFieldCoords (specAlgebraEtaleChart v hv) = ι.comp v :=
    AlgHom.ext fun p => rfl
  have hιv : (ι.comp v).toRingHom.FormallyEtale :=
    hB ▸ etaleChartFunctionFieldCoords_formallyEtale (specAlgebraEtaleChart v hv)
  have hcoords : ∀ p, dominantFunctionFieldAlgHom (K := K) (specAlgebraHom c.isAffine ψ)
      (etaleChartFunctionFieldCoords c p) = ι (ψ (c.coords p)) := by
    intro p
    change (dominantFunctionFieldMap (specAlgebraHom c.isAffine ψ)).hom
        (Y.germToFunctionField c.U (c.coords p)) = _
    rw [dominantFunctionFieldMap_germ _ c.U ⊤ (specAlgebraHom_top_le c.isAffine ψ),
      specAlgebraHom_appLE]
    rfl
  have hmat : etaleRelativeJacobian
      (dominantFunctionFieldAlgHom (K := K) (specAlgebraHom c.isAffine ψ))
      (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords (specAlgebraEtaleChart v hv))
      (etaleChartFunctionFieldCoords_formallyEtale _) =
      etaleRelativeJacobian (ι.comp ψ) c.coords (ι.comp v) hιv := by
    ext i j
    change etaleCoordinateDerivation (etaleChartFunctionFieldCoords (specAlgebraEtaleChart v hv))
        (etaleChartFunctionFieldCoords_formallyEtale _) j
        (dominantFunctionFieldAlgHom (K := K) (specAlgebraHom c.isAffine ψ)
          (etaleChartFunctionFieldCoords c (MvPolynomial.X i))) =
      etaleCoordinateDerivation (ι.comp v) hιv j (ι (ψ (c.coords (MvPolynomial.X i))))
    rw [hcoords, etaleCoordinateDerivation_congr hB]
  unfold chartRelativeJacobianDet
  rw [hmat, etaleRelativeJacobian_det_comp_coords ψ ι c.coords v hv hιv]
  rfl

variable [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- A bad point from an affine model: if a coordinate v_l of the model lies in a prime 𝔓 over y,
det J(ψ) = (∏ v_s^{κ_s}) J' with J' ∉ 𝔓, and every ψ(g_j) is divisible by v_l^a with
M (1 + κ_l) ≤ a, then y is a bad point of the g_j. -/
theorem modelThresholdBadAt_of_affine_model (cY c : EtaleChart K Y n) {B : Type u} [CommRing B]
    [IsDomain B] [Algebra K B] (ψ : Γ(Y, c.U) →ₐ[K] B) (hψ : Function.Injective ψ)
    (hbir : ∀ b : B, ∃ r s : Γ(Y, c.U), s ≠ 0 ∧ ψ s * b = ψ r)
    (v : MvPolynomial (Fin n) K →ₐ[K] B) (hv : v.toRingHom.Etale)
    (hvfe : v.toRingHom.FormallyEtale) (y : Y) (hy : y ∈ c.U) (𝔓 : Ideal B) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap ψ = (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal) (l : Fin n)
    (hl : v (MvPolynomial.X l) ∈ 𝔓) (κ : Fin n → ℕ) (J' : B) (hJ' : J' ∉ 𝔓)
    (hJ : (etaleRelativeJacobian ψ c.coords v hvfe).det =
      (∏ s, v (MvPolynomial.X s) ^ κ s) * J')
    {ι : Type*} (g : ι → Γ(Y, c.U)) (a : ℕ)
    (hg : ∀ j, ∃ r : B, ψ (g j) = v (MvPolynomial.X l) ^ a * r) (M : ℕ)
    (hM : M * (1 + κ l) ≤ a) :
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
  have hmono : (Spec (CommRingCat.of B)).ord (ι (∏ s, v (MvPolynomial.X s) ^ κ s)) (eC : _) =
      κ l := by
    have h := etaleChart_coordinate_prod_pow_ord cB eC trivial l hnu κ
    have hprod : ι (∏ s, v (MvPolynomial.X s) ^ κ s) =
        ∏ s, etaleChartFunctionFieldCoords cB (MvPolynomial.X s) ^ κ s := by
      simp only [ι, map_prod, map_pow]
      rfl
    rw [hprod, h]
  have hordl : (Spec (CommRingCat.of B)).ord (ι (v (MvPolynomial.X l))) (eC : _) = 1 := by
    have h := etaleChart_coordinate_ord_of_not_isUnit cB eC trivial l hnu l
    rw [ite_eq_left rfl, ← etaleChartFunctionFieldCoords_X] at h
    exact h
  -- the log discrepancy of e is 1 + κ_l
  have hJ0 : (∏ s, v (MvPolynomial.X s) ^ κ s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ fun h0 =>
      etaleChart_coordinate_ne_zero cB s (by
        change (Scheme.ΓSpecIso (CommRingCat.of B)).inv (v (MvPolynomial.X s)) = 0
        rw [h0, map_zero])
  have hJ'0 : J' ≠ 0 := fun h0 => hJ' (h0 ▸ 𝔓.zero_mem)
  have hcoef : cartierCoefficient (logDiscrepancyDivisor n (specAlgebraHom c.isAffine ψ) hσ cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) cB
      etaleCharts_cover) (eC : _) = κ l := by
    rw [logDiscrepancyDivisor_boundary_zero (specAlgebraHom c.isAffine ψ) hσ cY 1 1 cB, one_nsmul]
    unfold birationalRelativeCanonicalDivisor
    rw [cartierCoefficient_eq_ord (relativeCanonicalDivisor_isLocalEquationAt
      (specAlgebraHom c.isAffine ψ) cY etaleCharts_cover cB etaleCharts_cover
      (isUnit_chartRelativeJacobianDet_of_bijective (specAlgebraHom c.isAffine ψ) hσ cY cB)
      (eC : _) c hσe cB trivial), IsUnit.unit_spec, chartRelativeJacobianDet_specAlgebraHom c ψ v hvfe]
    change (Spec (CommRingCat.of B)).ord (ι (etaleRelativeJacobian ψ c.coords v hvfe).det) _ = _
    rw [hJ, hιmul, Scheme.ord_mul (hι0 _ hJ0) (hι0 _ hJ'0), hmono,
      hunit J' (fun h => hJ' (h𝔮le h)), add_zero]
  refine ⟨Spec (CommRingCat.of B), inferInstance, inferInstance, specAlgebraOver B, hrel,
    specAlgebraHom c.isAffine ψ, hdom, hover, hσ, cB, eC, hcentre, ?_, ?_⟩
  · rw [hcoef]
    positivity
  · intro j hj
    rw [hcoef]
    obtain ⟨r, hr⟩ := hg j
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
    have hr0 : r ≠ 0 := fun h0 => hψg (by rw [hr, h0, mul_zero])
    have hord : (Spec (CommRingCat.of B)).ord ((dominantFunctionFieldMap
        (specAlgebraHom c.isAffine ψ)).hom (Y.germToFunctionField c.U (g j))) (eC : _) =
        a + (Spec (CommRingCat.of B)).ord (ι r) (eC : _) := by
      change (Spec (CommRingCat.of B)).ord (dominantFunctionFieldAlgHom (K := K)
        (specAlgebraHom c.isAffine ψ) (Y.germToFunctionField c.U (g j))) _ = _
      rw [hgj, hr, hιmul, hιpow, Scheme.ord_mul (pow_ne_zero _ (hι0 _ hvl0)) (hι0 _ hr0),
        scheme_ord_pow (hι0 _ hvl0), hordl, mul_one]
    change (M : ℝ) * ((((1 : ℕ) : ℝ) + (((κ l : ℕ) : ℤ) : ℝ)) / ((1 : ℕ) : ℝ)) ≤
      (((Spec (CommRingCat.of B)).ord ((dominantFunctionFieldMap
        (specAlgebraHom c.isAffine ψ)).hom (Y.germToFunctionField c.U (g j))) (eC : _) : ℤ) : ℝ)
    rw [hord]
    have h1 := hregular r
    have h2 : (M : ℤ) * (1 + (κ l : ℤ)) ≤ (a : ℤ) + (Spec (CommRingCat.of B)).ord (ι r) (eC : _) := by
      have : ((M * (1 + κ l) : ℕ) : ℤ) ≤ (a : ℤ) := by exact_mod_cast hM
      push_cast at this
      linarith
    have h3 : (((M : ℤ) * (1 + (κ l : ℤ)) : ℤ) : ℝ) ≤
        (((a : ℤ) + (Spec (CommRingCat.of B)).ord (ι r) (eC : _) : ℤ) : ℝ) := by
      exact_mod_cast h2
    simp only [Nat.cast_one, div_one]
    push_cast at h3 ⊢
    linarith

end AffineModel

end MixedFujita
