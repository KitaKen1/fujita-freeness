/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FormalTestModelCenter
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.ProjectiveSNCModelPrincipalization
public import MixedFujita.PrincipalizedGlobalGeneration
public import MixedFujita.SNCModelPrimeOrders
public import MixedFujita.ActualSNCJacobianBound
public import MixedFujita.LogPairDenominatorScaling
public import MixedFujita.SNCBoundaryDiscrepancy
public import MixedFujita.RealizationThresholdReduction
public import MixedFujita.RelativeCanonicalEffectivity

/-!
A formal threshold test that fails at a point of affine space is computed by a prime divisor of
one principalized simple normal crossing model: the comparison of formal tests with actual
divisors, in every dimension. Let g_ℓ be polynomials, not all zero, and ψ a formal test at p with
weights w such that ord_w ψ(g_ℓ(p + X)) ≥ h (Σ w + ord_w det J_ψ) for all ℓ. Principalize the ideal
of the g_ℓ on a smooth projective model T with a simple normal crossing family ξ. The valuation of
the test has a centre t₀ on T; in a simple normal crossing chart at t₀ the generator of the
principalized ideal, the relative Jacobian and the components have local products, and the
formal Jacobian inequality gives Σ_i a_i o_i ≥ h Σ_i (1 + k_i) o_i with o_i the values of the
components through t₀, a_i the coefficients of the principalized divisor and k_i those of the
relative canonical divisor. Some component ξ_i through t₀ has a_i ≥ h (1 + k_i): it is a prime
divisor of a smooth birational model with centre containing p, positive log discrepancy 1 + k_i
and ord_{ξ_i}(g_ℓ) ≥ h (1 + k_i) for every nonzero g_ℓ.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPowerSeries WithZero
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

section Bad

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The model form of lct_x ≤ 1/M for rational functions g_j: some prime divisor e of a smooth
birational test model, with centre containing x and positive log discrepancy A(e), has
ord_e(g_j) ≥ M A(e) for every nonzero g_j. -/
def ModelThresholdBadAt (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ : CartierDivisor Y) (x : Y) {J : Type*} (g : J → Y.functionField) (M : ℕ) : Prop :=
  ∃ (U : Scheme.{u}) (_ : IsIntegral U) (_ : IsLocallyNoetherian U)
    (_ : U.Over (Spec (CommRingCat.of K)))
    (_ : SmoothOfRelativeDimension n (U ↘ Spec (CommRingCat.of K)))
    (σ : U ⟶ Y) (_ : IsDominant σ) (_ : σ.IsOver (Spec (CommRingCat.of K)))
    (hσ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) σ))
    (cU : EtaleChart K U n) (e : CodimensionOnePoint U),
    x ∈ closure ({σ (e : U)} : Set Y) ∧
    0 < ((d : ℝ) + cartierCoefficient
      (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d ∧
    ∀ j, g j ≠ 0 → (M : ℝ) * (((d : ℝ) + cartierCoefficient
        (logDiscrepancyDivisor n σ hσ cY fY d D₀ cU etaleCharts_cover) (e : U)) / d) ≤
      ((U.ord ((dominantFunctionFieldMap σ).hom (g j)) (e : U) : ℤ) : ℝ)

end Bad

section Arithmetic

/-- If Σ a_i o_i ≥ h Σ (1 + k_i) o_i ≥ 0 with o ≥ 0 and Σ a_i o_i > 0, some o_i > 0 has
a_i ≥ h (1 + k_i). -/
theorem exists_index_ge_of_weighted_sum_ge {τ : Type*} [Fintype τ] {o a k : τ → ℤ} {h : ℤ}
    (ho : ∀ s, 0 ≤ o s) (hsum : h * ∑ s, (1 + k s) * o s ≤ ∑ s, a s * o s)
    (hpos : 0 < ∑ s, a s * o s) : ∃ s, 0 < o s ∧ h * (1 + k s) ≤ a s := by
  by_contra hno
  push Not at hno
  have hterm : ∀ s, a s * o s ≤ h * (1 + k s) * o s := by
    intro s
    rcases (ho s).lt_or_eq with hs | hs
    · exact mul_le_mul_of_nonneg_right (hno s hs).le (ho s)
    · rw [← hs, mul_zero, mul_zero]
  have hstrict : ∃ s, a s * o s < h * (1 + k s) * o s := by
    obtain ⟨s, hs⟩ : ∃ s, a s * o s ≠ 0 := by
      by_contra hall
      push Not at hall
      rw [Finset.sum_eq_zero fun s _ => hall s] at hpos
      exact lt_irrefl 0 hpos
    have hos : o s ≠ 0 := fun h0 => hs (by rw [h0, mul_zero])
    have hpos' : 0 < o s := lt_of_le_of_ne (ho s) (Ne.symm hos)
    exact ⟨s, mul_lt_mul_of_pos_right (hno s hpos') hpos'⟩
  obtain ⟨s₀, hs₀⟩ := hstrict
  have hlt : ∑ s, a s * o s < ∑ s, h * (1 + k s) * o s :=
    Finset.sum_lt_sum (fun s _ => hterm s) ⟨s₀, Finset.mem_univ _, hs₀⟩
  have heq : ∑ s, h * (1 + k s) * o s = h * ∑ s, (1 + k s) * o s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith

end Arithmetic

section AffineInstances

variable (K : Type u) [Field K] (m : ℕ)

attribute [local instance] specAlgebraOver

instance mvPolynomial_fin_algebraSmooth : Algebra.Smooth K (MvPolynomial (Fin m) K) := {}

theorem affineSpace_smoothOfRelativeDimension :
    SmoothOfRelativeDimension m (affineSpace K m ↘ Spec (CommRingCat.of K)) :=
  specAlgebraOver_smoothOfRelativeDimension (MvPolynomial (Fin m) K) (AlgHom.id K _)
    (mvPolynomial_id_formallyEtale K m)

theorem affineSpace_locallyOfFiniteType :
    LocallyOfFiniteType (affineSpace K m ↘ Spec (CommRingCat.of K)) := by
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K))))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

theorem affineSpace_quasiCompact :
    QuasiCompact (affineSpace K m ↘ Spec (CommRingCat.of K)) := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K))))
  infer_instance

theorem affineSpace_isSeparated :
    IsSeparated (affineSpace K m ↘ Spec (CommRingCat.of K)) := by
  change IsSeparated (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K))))
  infer_instance

end AffineInstances

section Main

variable {K : Type u} [Field K] [CharZero K] {m : ℕ}

attribute [local instance] specAlgebraOver affineSpace_smoothOfRelativeDimension

/-- A formal threshold test failing at p is computed by a prime divisor of a principalized model:
the threshold condition fails at p in the model form. -/
theorem affineSpace_modelThresholdBadAt_of_formalTest
    {J : Type} [Finite J] (g : J → MvPolynomial (Fin m) K) (hg : ∃ ℓ, g ℓ ≠ 0)
    (p : Fin m → K) (h : ℕ) (hh : 1 ≤ h)
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (hJ : (powerSeriesJacobian ψ).det ≠ 0) (w : Fin m → ℕ) (hw : w ≠ 0)
    (hbad : ∀ ℓ, (h : ℕ∞) * (((∑ i, w i : ℕ) : ℕ∞) + (powerSeriesJacobian ψ).det.weightedOrder w) ≤
        (shiftedFormalTestMap ψ p (g ℓ)).weightedOrder w) :
    ModelThresholdBadAt (affineSpaceEtaleChart K m) 1 1
      (1 • (smoothCanonicalDivisor (affineSpaceEtaleChart K m) +
        principalCartierDivisor (affineSpace K m) 1))
      (affineSpacePoint K m p)
      (fun ℓ => etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) (g ℓ)) h := by
  classical
  have := affineSpace_locallyOfFiniteType K m
  have := affineSpace_quasiCompact K m
  have := affineSpace_isSeparated K m
  set c := affineSpaceEtaleChart K m with hc
  set y := etaleChartFunctionFieldCoords c with hy
  obtain ⟨ℓ₁, hℓ₁⟩ := hg
  have : Nonempty {ℓ : J // g ℓ ≠ 0} := ⟨⟨ℓ₁, hℓ₁⟩⟩
  have hyne : ∀ ℓ : {ℓ : J // g ℓ ≠ 0}, y (g ℓ) ≠ 0 := fun ℓ h0 =>
    ℓ.2 (affineSpaceEtaleChart_functionFieldCoords_injective K m (by rw [← hy, h0, map_zero]))
  let A : {ℓ : J // g ℓ ≠ 0} → CartierDivisor (affineSpace K m) := fun ℓ =>
    principalCartierDivisor (affineSpace K m) (Units.mk0 (y (g ℓ)) (hyne ℓ))
  have hA : ∀ ℓ, (A ℓ).IsEffective := fun ℓ =>
    (CartierDivisor.isEffective_principalCartierDivisor_iff _).mpr ⟨c.coords (g ℓ), rfl⟩
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hρd, hρo, hρp, -, hρ, cT, r, ξ, hinj, hcoh, hsnc, hbd, -, -,
      -, hall⟩ :=
    exists_projective_snc_model_principalizing (ι := PEmpty.{1}) (κ := Unit) c 1 1
      (1 • (smoothCanonicalDivisor c + principalCartierDivisor (affineSpace K m) 1))
      (fun i => PEmpty.elim i) (fun _ => ⨆ ℓ, effectiveCartierIdealSheaf (A ℓ) (hA ℓ))
      (fun _ => genericPoint_notMem_support_iSup_effectiveCartierIdealSheaf A hA)
  obtain ⟨-, -, Gc, hGc, hGcI, hGcs⟩ := hall ()
  obtain ⟨t₀, hpt, hle1, hlt1⟩ := exists_formalTest_center ρ hρ ψ hJ p w
  set v := formalTestModelValuation ρ hρ ψ hJ p w with hv
  -- units of the local ring at t₀ have valuation one
  have hunit : ∀ u : (T.presheaf.stalk t₀)ˣ,
      v (algebraMap (T.presheaf.stalk t₀) T.functionField (u : T.presheaf.stalk t₀)) = 1 := by
    intro u
    have h1 := hle1 u
    have h2 := hle1 ((u⁻¹ : (T.presheaf.stalk t₀)ˣ) : T.presheaf.stalk t₀)
    have h3 : v (algebraMap _ T.functionField (u : T.presheaf.stalk t₀)) *
        v (algebraMap _ T.functionField ((u⁻¹ : (T.presheaf.stalk t₀)ˣ) :
          T.presheaf.stalk t₀)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = _ := h3.symm
      _ ≤ v (algebraMap _ T.functionField (u : T.presheaf.stalk t₀)) * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  -- two local equations of one divisor at t₀ have the same valuation
  have hloceq : ∀ {D : CartierDivisor T} {f f' : T.functionFieldˣ},
      D.IsLocalEquationAt t₀ f → D.IsLocalEquationAt t₀ f' →
        v (f : T.functionField) = v (f' : T.functionField) := by
    intro D f f' hf hf'
    obtain ⟨u, hu⟩ := hf.exists_unit_mul_eq hf'
    rw [← hu, map_mul, hunit, one_mul]
  -- the simple normal crossing chart at t₀ and the local products there
  obtain ⟨cS, σ, hcS, hcsnc⟩ := hsnc t₀
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hnorm := isSNCFamily_stalk_isIntegrallyClosed hsnc
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  set comp : Fin r → T.functionField :=
    fun i => ((sncChartComponentEquation cS σ i : T.functionFieldˣ) : T.functionField) with hcomp
  have hprod : ∀ B : CartierDivisor T, (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient B (z : T) = 0) → ∀ f : T.functionFieldˣ, B.IsLocalEquationAt t₀ f →
        v (f : T.functionField) = ∏ i, v (comp i) ^ cartierCoefficient B (ξ i) := by
    intro B hB f hf
    obtain ⟨f', hf', u, hu⟩ :=
      normal_isSNCChart_boundary_local_product hnorm B cS ξ hinj hcoh σ hcsnc hB t₀ hcS
    rw [hloceq hf hf', hu, map_mul, hunit, one_mul, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀]
  -- coordinates of the chart: valuation at most one, less than one only on the zero locus
  have hcoord_le : ∀ a, v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a)) ≤ 1 := by
    intro a
    have h := hle1 (T.presheaf.germ cS.U t₀ hcS (cS.coords (MvPolynomial.X a)))
    rwa [Scheme.algebraMap_germ_eq_germToFunctionField] at h
  have hcoord_lt : ∀ a, v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a)) < 1 →
      t₀ ∈ T.zeroLocus ({cS.coords (MvPolynomial.X a)} : Set Γ(T, cS.U)) := by
    intro a ha
    rw [Scheme.zeroLocus_singleton]
    intro hb
    have hu : IsUnit (T.presheaf.germ cS.U t₀ hcS (cS.coords (MvPolynomial.X a))) :=
      (T.mem_basicOpen _ t₀ hcS).mp hb
    have h1 := hunit hu.unit
    rw [IsUnit.unit_spec, Scheme.algebraMap_germ_eq_germToFunctionField] at h1
    exact (ne_of_lt ha) h1
  have hcomp_eq : ∀ i, comp i = (σ i).elim 1
      (fun a => etaleChartFunctionFieldCoords cS (MvPolynomial.X a)) := by
    intro i
    cases hσ : σ i with
    | none => simp only [hcomp, sncChartComponentEquation, hσ, Option.elim_none, Units.val_one]
    | some a =>
      simp only [hcomp, sncChartComponentEquation, hσ, Option.elim_some,
        etaleChartCoordinateRationalUnit, regularEquationRationalUnit_val]
      rfl
  -- integer orders of the components and of the coordinates
  have hcompne : ∀ i, v (comp i) ≠ 0 := fun i =>
    (Valuation.ne_zero_iff v).mpr (Units.ne_zero _)
  set o : Fin r → ℤ := fun i => -WithZero.log (v (comp i)) with ho
  have hvo : ∀ i, v (comp i) = exp (-o i) := fun i => by
    simp only [ho, neg_neg]
    exact (exp_log (hcompne i)).symm
  have hcoordne : ∀ a, v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a)) ≠ 0 := fun a =>
    (Valuation.ne_zero_iff v).mpr (etaleChartCoordinateRationalUnit cS a).ne_zero
  set ν : Fin m → ℤ := fun a =>
    -WithZero.log (v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a))) with hν
  have hvν : ∀ a, v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a)) = exp (-ν a) :=
    fun a => by
      simp only [hν, neg_neg]
      exact (exp_log (hcoordne a)).symm
  have hν0 : ∀ a, 0 ≤ ν a := fun a => by
    have h := hcoord_le a
    rw [hvν a, ← exp_zero, exp_le_exp] at h
    omega
  have hoν : ∀ i, o i = (σ i).elim 0 ν := by
    intro i
    have h := hcomp_eq i
    cases hσ : σ i with
    | none =>
      rw [hσ, Option.elim_none] at h
      simp only [ho, h, map_one, WithZero.log_one, neg_zero, Option.elim_none]
    | some a =>
      rw [hσ, Option.elim_some] at h
      simp only [ho, hν, h, Option.elim_some]
  have ho0 : ∀ i, 0 ≤ o i := fun i => by
    rw [hoν i]
    cases σ i with
    | none => exact le_rfl
    | some a => exact hν0 a
  have hosum : ∑ i, o i ≤ ∑ a, ν a := by
    simp_rw [hoν]
    exact option_selected_sum_le σ hcsnc.1 ν hν0
  have hprodexp : ∀ q : Fin r → ℤ, ∏ i, v (comp i) ^ q i = exp (-(∑ i, q i * o i)) := by
    intro q
    simp_rw [hvo, ← exp_zsmul]
    rw [prod_exp_eq_exp_sum, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    ring
  -- the components through t₀
  have hthrough : ∀ i, 0 < o i → t₀ ∈ closure ({ξ i} : Set T) := by
    intro i hi
    rw [hoν i] at hi
    cases hσ : σ i with
    | none => rw [hσ, Option.elim_none] at hi; exact absurd hi (lt_irrefl 0)
    | some a =>
      rw [hσ, Option.elim_some] at hi
      have hlt : v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a)) < 1 := by
        rw [hvν a, ← exp_zero, exp_lt_exp]
        omega
      have hz := hcoord_lt a hlt
      have hset := hcsnc.2 i
      rw [hσ, Option.elim_some] at hset
      have hmem : t₀ ∈ T.zeroLocus ({cS.coords (MvPolynomial.X a)} : Set Γ(T, cS.U)) ∩ cS.U :=
        ⟨hz, hcS⟩
      rw [← hset] at hmem
      exact hmem.1
  -- the relative canonical divisor: supported on the family, with local equation the Jacobian
  have hlog : logDiscrepancyDivisor m ρ hρ c 1 1
      (1 • (smoothCanonicalDivisor c + principalCartierDivisor (affineSpace K m) 1)) cT
      etaleCharts_cover =
      birationalRelativeCanonicalDivisor m ρ hρ c etaleCharts_cover cT etaleCharts_cover := by
    have h := logDiscrepancyDivisor_boundary_add ρ hρ c 1 1 0 cT
    rw [add_zero, cartierPullback_zero, sub_zero] at h
    rw [h, one_smul]
  have hrelsupp : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (birationalRelativeCanonicalDivisor m ρ hρ c etaleCharts_cover cT
        etaleCharts_cover) (z : T) = 0 := by
    intro z hz
    have h := hbd z hz
    rw [crepantBoundaryCartier_eq_neg_discrepancy, cartierCoefficient_neg, hlog,
      neg_eq_zero] at h
    exact h
  set k : Fin r → ℤ := fun i => cartierCoefficient (birationalRelativeCanonicalDivisor m ρ hρ c
    etaleCharts_cover cT etaleCharts_cover) (ξ i) with hk
  have hR := isUnit_chartRelativeJacobianDet_of_bijective ρ hρ c cT
  have hJloc := relativeCanonicalDivisor_isLocalEquationAt ρ c etaleCharts_cover cT
    etaleCharts_cover hR t₀ c (show ρ t₀ ∈ c.U from trivial) cS hcS
  have hvJ : v (chartRelativeJacobianDet ρ c cS) = exp (-(∑ i, k i * o i)) := by
    have h := hprod _ hrelsupp _ hJloc
    rw [IsUnit.unit_spec] at h
    rw [h, hprodexp]
  -- the formal Jacobian inequality on the model
  set yT := (dominantFunctionFieldAlgHom (K := K) ρ).comp y with hyT
  have hyTe : yT.toRingHom.FormallyEtale := by
    have hiso : (dominantFunctionFieldAlgHom (K := K) ρ).toRingHom.FormallyEtale := by
      let _ : Algebra (affineSpace K m).functionField T.functionField :=
        (dominantFunctionFieldAlgHom (K := K) ρ).toRingHom.toAlgebra
      let e : (affineSpace K m).functionField ≃ₐ[(affineSpace K m).functionField]
          T.functionField :=
        AlgEquiv.ofBijective (Algebra.ofId _ _) hρ
      exact Algebra.FormallyEtale.of_equiv e
    exact formallyEtale_comp _ hiso _ (etaleChartFunctionFieldCoords_formallyEtale c)
  have hφT : ∀ P, formalTestModelFieldMap ρ hρ ψ hJ p (yT P) =
      algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (shiftedFormalTestMap ψ p P) :=
    fun P => (formalTestModelFieldMap_pullback ρ hρ ψ hJ p (y P)).trans
      (affineFormalTestFieldMap_coords ψ hJ p P)
  have hfracT : ∀ f : T.functionField, ∃ P Q : MvPolynomial (Fin m) K,
      yT Q ≠ 0 ∧ f * yT Q = yT P := by
    intro f
    obtain ⟨P, Q, hQ, hPQ⟩ := affineSpaceEtaleChart_exists_fraction K m
      ((RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm f)
    refine ⟨P, Q, ?_, ?_⟩
    · show (dominantFunctionFieldMap ρ).hom (y Q) ≠ 0
      exact (map_ne_zero (dominantFunctionFieldMap ρ).hom).mpr hQ
    · show f * (dominantFunctionFieldMap ρ).hom (y Q) = (dominantFunctionFieldMap ρ).hom (y P)
      rw [← hPQ, map_mul]
      congr 1
      exact ((RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).apply_symm_apply f).symm
  have hcore := weightedFieldValuation_jacobian_le yT hyTe (shiftedFormalTestMap ψ p)
    (formalTestModelFieldMap ρ hρ ψ hJ p) hφT hfracT w (etaleChartFunctionFieldCoords cS)
    (etaleChartFunctionFieldCoords_formallyEtale cS)
  rw [shiftedFormalTestMap_jacobian_det, weightedFieldValuation_algebraMap] at hcore
  change weightedValuation w (powerSeriesJacobian ψ).det ≤
    exp ((∑ i, w i : ℕ) : ℤ) * (∏ a, v (etaleChartFunctionFieldCoords cS (MvPolynomial.X a))) *
      v (chartRelativeJacobianDet ρ c cS) at hcore
  -- the core inequality in integers: Σ ν + Σ k o ≤ Σ w + ord det J
  set Dd := ((powerSeriesJacobian ψ).det.weightedOrder w).toNat with hDd
  have hcoreZ : ∑ a, ν a + ∑ i, k i * o i ≤ ((∑ i, w i : ℕ) : ℤ) + Dd := by
    rw [weightedValuation_of_ne_zero w hJ, hvJ] at hcore
    simp_rw [hvν] at hcore
    rw [prod_exp_eq_exp_sum, ← exp_add, ← exp_add, exp_le_exp] at hcore
    simp only [Finset.sum_neg_distrib] at hcore
    linarith
  -- the principalized divisor at t₀ and the failure of the test
  obtain ⟨ℓ₀, f, hGf, hAf⟩ :=
    exists_common_isLocalEquationAt_of_effectiveCartierIdealSheaf_eq_comap_iSup ρ A hA Gc hGc
      hGcI t₀
  have hAf' := cartierPullback_isLocalEquationAt ρ (A ℓ₀) t₀
    (CartierDivisor.isLocalEquationAt_principalCartierDivisor (ρ t₀)
      (Units.mk0 (y (g ℓ₀)) (hyne ℓ₀)))
  have hvf : v (f : T.functionField) = weightedValuation w (shiftedFormalTestMap ψ p (g ℓ₀)) := by
    rw [hloceq hAf hAf']
    exact formalTestModelValuation_pullback_coords ρ hρ ψ hJ p w (g ℓ₀)
  set a : Fin r → ℤ := fun i => cartierCoefficient Gc (ξ i) with ha
  have hvG : v (f : T.functionField) = exp (-(∑ i, a i * o i)) := by
    rw [hprod Gc hGcs f hGf, hprodexp]
  have hθne : shiftedFormalTestMap ψ p (g ℓ₀) ≠ 0 := fun h0 =>
    ℓ₀.2 (shiftedFormalTestMap_injective ψ hJ p (h0.trans (map_zero _).symm))
  have hbadZ : (h : ℤ) * (((∑ i, w i : ℕ) : ℤ) + Dd) ≤ ∑ i, a i * o i := by
    have hE := weightedValuation_of_ne_zero w hθne
    rw [← hvf, hvG, exp_inj, neg_inj] at hE
    have h1 := hbad ℓ₀
    rw [← (ne_zero_iff_weightedOrder_finite w).mp hJ,
      ← (ne_zero_iff_weightedOrder_finite w).mp hθne] at h1
    have h2 : h * ((∑ i, w i) + Dd) ≤ ((shiftedFormalTestMap ψ p (g ℓ₀)).weightedOrder w).toNat := by
      exact_mod_cast h1
    rw [hE]
    exact_mod_cast h2
  -- some component through t₀ satisfies a_i ≥ h (1 + k_i)
  have hwpos : 1 ≤ ∑ i, w i := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    exact (Nat.one_le_iff_ne_zero.mpr hi).trans
      (Finset.single_le_sum (fun j _ => Nat.zero_le (w j)) (Finset.mem_univ i))
  have hsum1 : (h : ℤ) * ∑ i, (1 + k i) * o i ≤ ∑ i, a i * o i := by
    have h3 : ∑ i, (1 + k i) * o i ≤ ((∑ i, w i : ℕ) : ℤ) + Dd := by
      have hsplit : ∑ i, (1 + k i) * o i = ∑ i, o i + ∑ i, k i * o i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit]
      linarith [hosum, hcoreZ]
    calc (h : ℤ) * ∑ i, (1 + k i) * o i ≤ h * (((∑ i, w i : ℕ) : ℤ) + Dd) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ _ := hbadZ
  have hpos : 0 < ∑ i, a i * o i := by
    have h4 : (1 : ℤ) ≤ h := by exact_mod_cast hh
    have h5 : (1 : ℤ) ≤ ((∑ i, w i : ℕ) : ℤ) + Dd := by
      have : (1 : ℤ) ≤ ((∑ i, w i : ℕ) : ℤ) := by exact_mod_cast hwpos
      have : (0 : ℤ) ≤ Dd := by positivity
      linarith
    nlinarith [hbadZ]
  obtain ⟨i, hoi, hai⟩ := exists_index_ge_of_weighted_sum_ge ho0 hsum1 hpos
  -- the component ξ_i is the required prime divisor
  refine ⟨T, hTi, inferInstance, hTo, hTs, ρ, hρd, hρo, hρ, cT, ⟨ξ i, hcoh i⟩, ?_, ?_, ?_⟩
  · have h1 : ξ i ⤳ t₀ := specializes_iff_mem_closure.mpr (hthrough i hoi)
    have h2 : ρ (ξ i) ⤳ ρ t₀ := h1.map ρ.continuous
    have h3 : ρ t₀ ⤳ affineSpacePoint K m p := specializes_iff_mem_closure.mpr hpt
    exact specializes_iff_mem_closure.mp (h2.trans h3)
  · rw [hlog]
    have hk0 : 0 ≤ k i := cartierCoefficient_nonneg_of_isEffective _
      (birationalRelativeCanonicalDivisor_isEffective ρ hρ c etaleCharts_cover cT
        etaleCharts_cover) (ξ i)
    have hk0' : (0 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast hk0
    simp only [Nat.cast_one, div_one]
    change (0 : ℝ) < 1 + (k i : ℝ)
    linarith
  · intro ℓ hℓ
    have hgℓ : g ℓ ≠ 0 := fun h0 => hℓ (by simp only [h0, map_zero])
    let ℓ' : {ℓ : J // g ℓ ≠ 0} := ⟨ℓ, hgℓ⟩
    have hloc := cartierPullback_isLocalEquationAt ρ (A ℓ') (ξ i)
      (CartierDivisor.isLocalEquationAt_principalCartierDivisor (ρ (ξ i))
        (Units.mk0 (y (g ℓ)) (hyne ℓ')))
    have hord := cartierCoefficient_eq_ord hloc
    have hle : effectiveCartierIdealSheaf (cartierPullback ρ (A ℓ'))
        (cartierPullback_isEffective ρ (A ℓ') (hA ℓ')) ≤ effectiveCartierIdealSheaf Gc hGc := by
      rw [hGcI, effectiveCartierIdealSheaf_cartierPullback ρ (A ℓ') (hA ℓ')]
      exact Scheme.IdealSheafData.comap_mono ρ
        (le_iSup (fun ℓ => effectiveCartierIdealSheaf (A ℓ) (hA ℓ)) ℓ')
    have hdiff := cartierCoefficient_nonneg_of_isEffective _
      (cartier_sub_isEffective_of_effectiveCartierIdealSheaf_le _ _
        (cartierPullback_isEffective ρ (A ℓ') (hA ℓ')) hGc hle) (ξ i)
    rw [cartierCoefficient_sub] at hdiff
    rw [hlog]
    simp only [Nat.cast_one, div_one]
    show (h : ℝ) * (1 + (k i : ℝ)) ≤
      ((T.ord ((dominantFunctionFieldMap ρ).hom (y (g ℓ))) (ξ i) : ℤ) : ℝ)
    have hval : (((Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
        (Units.mk0 (y (g ℓ)) (hyne ℓ')) : T.functionFieldˣ) : T.functionField)) =
        (dominantFunctionFieldMap ρ).hom (y (g ℓ)) := rfl
    rw [hval] at hord
    rw [← hord]
    have hfin : (h : ℤ) * (1 + k i) ≤ cartierCoefficient (cartierPullback ρ (A ℓ')) (ξ i) := by
      have : cartierCoefficient Gc (ξ i) = a i := rfl
      linarith [hai, hdiff]
    exact_mod_cast hfin

end Main

end MixedFujita
