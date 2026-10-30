/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.OpenImmersionModelRestriction
public import MixedFujita.AffineClosureHyperplaneModels
public import MixedFujita.StrictTransformChartsFromCompactification
public import MixedFujita.CrepantKltDescent
public import MixedFujita.FixedIdealLemmaThree
public import MixedFujita.ProjectiveAllDimensionSectionBounds
public import MixedFujita.SNCWeightDiscrepancyInterval
public import MixedFujita.CartierPositivityPullback
public import MixedFujita.SmoothRestrictionInduction

/-!
Compactified principalizing models, and F1 from sum Kawamata–Viehweg vanishing (step 9).

Let `A` be smooth over a field `K` of characteristic zero, with the data of
`CompactifiedStrictTransformModelStatement`: an étale chart, an étale map `φ` to affine space and a
nondegenerate finite family of functions `g_j`. Choose generators of `A` that include `φ(X₀)` and
the nonzero `g_j` (check-392), and let `X̄₀` be the projective closure of `Spec A` for them
(check-390). Then:

* the divisors of `φ(X₀)` and of the `g_j` are restrictions of hyperplane sections `H̄` and `Ā_j`
  of `X̄₀`, each differing from the hyperplane at infinity `D_∞` by a principal divisor, and `D_∞`
  restricts to zero;
* the crepant boundary data on `Spec A` (reference chart `cX`, form `1`, divisor `K_{cX}`) are the
  restriction of data on `X̄₀`: the image chart, a form compensating the chart Jacobian, and the
  principal divisor of the transported canonical equation of `cX` relative to the global chart of
  `φ`.

The sum-principalizing SNC model `ρ̄ : T̄ → X̄₀` of these data (`exists_projective_snc_model_principalizing_sum`,
which resolves the singular locus of `X̄₀` itself) is smooth and proper over `K`, and on it
`ρ̄^* D_∞ - Ḡ` is globally generated, where `Ḡ` principalizes the sum of the ideals of the `Ā_j`.
Its open part `T = ρ̄⁻¹(Spec A)` over `Spec A` has every property of
`exists_nondegenerate_function_snc_model` (check-391: the SNC family restricts, and all
coefficients, including those of the crepant boundary, are read off on `T̄`), and `T` is the
complement in `T̄` of the effective, nef and big divisor `ρ̄^* D_∞`
(`compactifiedStrictTransformModelStatement_of_charZero`). With check-389 this proves F1 from sum
Kawamata–Viehweg vanishing alone (`mixedFujitaFreeness_of_kvSum`). The compactifications are
projective (check-394), so the compactified part of the argument uses the vanishing theorem only on
smooth projective varieties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

section Congr

/-- The ideal sheaf of an effective Cartier divisor depends only on the divisor. -/
theorem effectiveCartierIdealSheaf_congr {X : Scheme.{u}} [IsIntegral X] {D E : CartierDivisor X}
    (h : D = E) (hD : D.IsEffective) (hE : E.IsEffective) :
    effectiveCartierIdealSheaf D hD = effectiveCartierIdealSheaf E hE := by
  subst h
  rfl

/-- The rational unit of a nonzero function depends only on the function. -/
theorem specFunctionRationalUnit_congr {A : Type u} [CommRing A] [IsDomain A] {a b : A}
    (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) :
    specFunctionRationalUnit a ha = specFunctionRationalUnit b hb := by
  subst h
  rfl

/-- Units are transported along a bijective ring homomorphism. -/
theorem exists_units_map_eq_of_bijective {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S)
    (hφ : Function.Bijective φ) (w : Sˣ) : ∃ v : Rˣ, Units.map φ.toMonoidHom v = w :=
  ⟨Units.map (RingEquiv.ofBijective φ hφ).symm.toRingHom.toMonoidHom w, by
    ext
    simp only [Units.coe_map]
    exact (RingEquiv.ofBijective φ hφ).apply_symm_apply (w : S)⟩

end Congr

section Model

variable {K : Type u} [Field K] [CharZero K]

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra cartierGlobalStalkAlgebra
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra functionFieldBaseAlgebra

set_option maxHeartbeats 3200000 in
/-- **Compactified principalizing models.** Over a field of characteristic zero, the principalizing
SNC models of the original nondegenerate family can be chosen as open parts of SNC
compactifications: the open part over `Spec A` of the sum-principalizing model of the projective
closure through hyperplane sections. -/
theorem compactifiedStrictTransformModelStatement_of_charZero :
    CompactifiedStrictTransformModelStatement K := by
  classical
  intro A _ _ _ _ N _ cX φ hφ _ J _ g hnd
  have : Smooth (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth (N + 1) _
  have : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := N + 1)
  obtain ⟨k₀, hk₀⟩ := hnd
  have hgk₀ : g k₀ ≠ 0 := fun h => hk₀ (h ▸ Ideal.zero_mem _)
  haveI : Nonempty {j : J // g j ≠ 0} := ⟨⟨k₀, hgk₀⟩⟩
  have hφ0 : φ (MvPolynomial.X 0) ≠ 0 := by
    intro h
    apply etaleChart_coordinate_ne_zero (specAlgebraEtaleChart φ hφ) 0
    change (Scheme.ΓSpecIso (CommRingCat.of A)).inv (φ (MvPolynomial.X 0)) = 0
    rw [h, map_zero]
  -- generators of `A` through `φ(X₀)` and the nonzero `g_j`, and the projective closure
  obtain ⟨r, π, idx, hπ, hidx⟩ := exists_surjective_mvPolynomial_with_values (K := K)
    (fun o : Option {j : J // g j ≠ 0} => o.elim (φ (MvPolynomial.X 0)) (fun j => g j.1))
  have hiH : π (MvPolynomial.X (idx none)) ≠ 0 := by rw [hidx]; exact hφ0
  have hig : ∀ j : {j : J // g j ≠ 0}, π (MvPolynomial.X (idx (some j))) ≠ 0 := fun j => by
    rw [hidx]; exact j.2
  haveI := affineClosure_toImage_isOpenImmersion π hπ
  haveI := affineClosureToImage_isOver π
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) (affineClosureToImage π)) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion _
  let cb : EtaleChart K (affineClosure π) (N + 1) :=
    etaleChartImageOfOpenImmersion (affineClosureToImage π) cX
  -- the crepant data on the closure
  obtain ⟨fb, hfb⟩ := exists_units_map_eq_of_bijective
    (dominantFunctionFieldMap (affineClosureToImage π)).hom hj
    (isUnit_chartRelativeJacobianDet_of_bijective (affineClosureToImage π) hj cb cX).unit⁻¹
  have hfb1 : crepantPullbackFormUnit (affineClosureToImage π) hj cb fb cX = 1 := by
    rw [crepantPullbackFormUnit, hfb, inv_mul_cancel]
  obtain ⟨wb, hwb⟩ := exists_units_map_eq_of_bijective
    (dominantFunctionFieldMap (affineClosureToImage π)).hom hj
    (etaleChartCanonicalEquation cX (specAlgebraEtaleChart φ hφ))
  let Db := principalCartierDivisor (affineClosure π) wb
  have hDb : cartierPullback (affineClosureToImage π) Db =
      1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1) := by
    rw [cartierPullback_principal, hwb, principalCartierDivisor_one, add_zero, one_nsmul,
      smoothCanonicalDivisor_eq_principal_of_top (specAlgebraEtaleChart φ hφ) cX rfl]
  -- the hyperplane sections
  let Hb := affineClosureHyperplane π (idx none) hiH
  let Ab : {j : J // g j ≠ 0} → CartierDivisor (affineClosure π) :=
    fun j => affineClosureHyperplane π (idx (some j)) (hig j)
  have hAb : ∀ j, (Ab j).IsEffective := fun j => affineClosureHyperplane_isEffective π _ (hig j)
  -- the sum-principalizing model of the closure
  obtain ⟨Tb, hTbi, hTbo, hTbN, hTbs, ρb, hdom, hover, hprop, -, hρb, cTb, rb, ξb, hinjb, hcohb,
      hsncb, hcrepb, hGb, hAsupp, hemb, -, -, Gb, hGbeff, hGbI, hGb0, -, hnefb⟩ :=
    exists_projective_snc_model_principalizing_sum (K := K) (n := N + 1) cb fb 1 Db
      (fun _ : Unit => Hb) Ab hAb (Empty.elim : Empty → (affineClosure π).IdealSheafData)
      (fun e => e.elim)
  -- its open part over `Spec A`
  let U := affineClosureChartPart π
  haveI := affineClosureChartPart_nonempty π
  have hηU : ρb (genericPoint Tb) ∈ U := by
    rw [dominant_map_genericPoint]
    exact genericPoint_mem U
  let V : Tb.Opens := ρb ⁻¹ᵁ U
  haveI : Nonempty V := ⟨⟨genericPoint Tb, hηU⟩⟩
  letI instTo : V.toScheme.Over (Spec (CommRingCat.of K)) :=
    ⟨V.ι ≫ (Tb ↘ Spec (CommRingCat.of K))⟩
  haveI : V.ι.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  haveI : IsDominant V.ι := ⟨V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  haveI hTs : SmoothOfRelativeDimension (N + 1) (V.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := V.ι) (S := Spec (CommRingCat.of K))]
    have h : SmoothOfRelativeDimension (0 + (N + 1)) (V.ι ≫ (Tb ↘ Spec (CommRingCat.of K))) :=
      inferInstance
    simpa only [Nat.zero_add] using h
  haveI hTN : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (V : Set Tb)) }
  haveI := affineClosureChartLift_isIso π hπ
  let ρ : V.toScheme ⟶ Spec (CommRingCat.of A) := (ρb ∣_ U) ≫ inv (affineClosureChartLift π)
  have hcomm : ρ ≫ affineClosureToImage π = V.ι ≫ ρb := by
    simp only [ρ, Category.assoc]
    rw [← affineClosureChartLift_fac π, IsIso.inv_hom_id_assoc, morphismRestrict_ι]
  haveI : IsDominant (ρ ≫ affineClosureToImage π) := by rw [hcomm]; infer_instance
  haveI hρdom : IsDominant ρ := IsDominant.of_comp_of_isOpenImmersion ρ (affineClosureToImage π)
  haveI hρover : ρ.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    rw [← HomIsOver.comp_over (f := affineClosureToImage π) (S := Spec (CommRingCat.of K)),
      ← Category.assoc, hcomm, Category.assoc,
      HomIsOver.comp_over (f := ρb) (S := Spec (CommRingCat.of K))]
    rfl
  haveI hρprop : IsProper ρ := by
    have : IsProper (ρb ∣_ U) := IsZariskiLocalAtTarget.restrict hprop U
    infer_instance
  have hιb : Function.Bijective (dominantFunctionFieldAlgHom (K := K) V.ι) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion V.ι
  have hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ) := by
    have h1 : Function.Bijective
        (dominantFunctionFieldAlgHom (K := K) (ρ ≫ affineClosureToImage π)) := by
      rw [dominantFunctionFieldAlgHom_congr_hom hcomm]
      exact dominantFunctionFieldAlgHom_comp_bijective ρb V.ι hρb hιb
    rw [dominantFunctionFieldAlgHom_comp] at h1
    exact (Function.Bijective.of_comp_iff _ hj).mp h1
  obtain ⟨cT⟩ := exists_etaleChart_on_integral_open_immersion V.ι cTb
  -- the restricted SNC family
  obtain ⟨r', ξ, hinj, hcoh, hsnc, -, hξall⟩ :=
    exists_isSNCFamily_of_isOpenImmersion V.ι ξb hinjb hcohb hsncb
  have hout : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      V.ι (z : V.toScheme) ∉ Set.range ξb := fun z hz h => hz (hξall _ h)
  let zb : CodimensionOnePoint V.toScheme → CodimensionOnePoint Tb := fun z =>
    ⟨V.ι (z : V.toScheme), (coheight_eq_of_isOpenImmersion V.ι (z : V.toScheme)).trans z.2⟩
  have hcoef : ∀ (B : CartierDivisor Tb) (z : CodimensionOnePoint V.toScheme),
      cartierCoefficient (cartierPullback V.ι B) (z : V.toScheme) =
        cartierCoefficient B (V.ι (z : V.toScheme)) := fun B z =>
    cartierCoefficient_cartierPullback_of_isOpenImmersion (K := K) (n := N + 1) V.ι B z
  have hpull : ∀ B : CartierDivisor (affineClosure π),
      cartierPullback ρ (cartierPullback (affineClosureToImage π) B) =
        cartierPullback V.ι (cartierPullback ρb B) := by
    intro B
    rw [← cartierPullback_comp, ← cartierPullback_comp]
    exact cartierPullback_congr_hom hcomm B
  -- the crepant boundary
  have hcrep : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
        cT etaleCharts_cover) (z : V.toScheme) = 0 := by
    intro z hz
    have h1 : crepantBoundaryCartier ρ hρ cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
        cT etaleCharts_cover =
        crepantBoundaryCartier (V.ι ≫ ρb) (dominantFunctionFieldAlgHom_comp_bijective ρb V.ι hρb hιb)
          cb fb 1 Db cT etaleCharts_cover := by
      rw [← hDb, ← hfb1, ← crepantBoundaryCartier_comp (affineClosureToImage π) ρ hj hρ cb fb 1 Db cX
        cT etaleCharts_cover]
      exact crepantBoundaryCartier_congr_hom hcomm _ _ cb fb 1 Db cT etaleCharts_cover
    rw [h1, crepantBoundaryCartier_coefficient_comp_of_stalkMap_bijective ρb V.ι hρb hιb _ cb fb 1
      Db cTb cT z ((coheight_eq_of_isOpenImmersion V.ι (z : V.toScheme)).trans z.2)
      (ConcreteCategory.bijective_of_isIso _)]
    exact hcrepb (zb z) (hout z hz)
  -- the hyperplane and the functions
  have hHeq : principalCartierDivisor (Spec (CommRingCat.of A))
      (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0) =
        cartierPullback (affineClosureToImage π) Hb := by
    rw [cartierPullback_affineClosureHyperplane]
    congr 1
    apply Units.ext
    change (Spec (CommRingCat.of A)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (φ (MvPolynomial.X 0))) =
      (Spec (CommRingCat.of A)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (π (MvPolynomial.X (idx none))))
    rw [hidx]
    rfl
  have hH : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
        (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (z : V.toScheme) = 0 := by
    intro z hz
    rw [hHeq, hpull, hcoef]
    exact hGb () (zb z) (hout z hz)
  have hgeq : ∀ j : {j : J // g j ≠ 0}, principalCartierDivisor (Spec (CommRingCat.of A))
      (specFunctionRationalUnit (g j.1) j.2) = cartierPullback (affineClosureToImage π) (Ab j) := by
    intro j
    rw [cartierPullback_affineClosureHyperplane]
    congr 1
    exact specFunctionRationalUnit_congr (hidx (some j)).symm _ _
  have hgsupp : ∀ (j : {j : J // g j ≠ 0}) (z : CodimensionOnePoint V.toScheme),
      (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit (g j.1) j.2))) (z : V.toScheme) = 0 := by
    intro j z hz
    rw [hgeq, hpull, hcoef]
    exact hAsupp j (zb z) (hout z hz)
  -- the principalized divisor
  let Gc := cartierPullback V.ι Gb
  have hGc : Gc.IsEffective := cartierPullback_isEffective V.ι Gb hGbeff
  have hGc0 : ∀ z : CodimensionOnePoint V.toScheme, (z : V.toScheme) ∉ Set.range ξ →
      cartierCoefficient Gc (z : V.toScheme) = 0 := fun z hz => by
    rw [hcoef]
    exact hGb0 (zb z) (hout z hz)
  have hGcI : effectiveCartierIdealSheaf Gc hGc = (⨆ j : {j : J // g j ≠ 0},
      effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit (g j.1) j.2)) (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ := by
    rw [effectiveCartierIdealSheaf_cartierPullback V.ι Gb hGbeff, hGbI,
      ← Scheme.IdealSheafData.comap_comp, ← hcomm, Scheme.IdealSheafData.comap_comp,
      (Scheme.IdealSheafData.map_gc (affineClosureToImage π)).l_iSup]
    congr 1
    apply iSup_congr
    intro j
    rw [← effectiveCartierIdealSheaf_cartierPullback (affineClosureToImage π) (Ab j) (hAb j)]
    exact effectiveCartierIdealSheaf_congr (hgeq j).symm _ _
  have hmin := fun t => cartierCoefficient_le_and_exists_eq_of_effectiveCartierIdealSheaf_eq_comap_iSup
    ρ (fun j : {j : J // g j ≠ 0} => principalCartierDivisor (Spec (CommRingCat.of A))
      (specFunctionRationalUnit (g j.1) j.2)) (fun j => specFunctionRationalUnit_effective (g j.1) j.2)
    Gc hGc hGcI t
  have hs₀ := exists_strictTransform_member_coefficients ρ hρ cX cT φ hφ ξ hcoh hH
    (g k₀) (specFunctionRationalUnit (g k₀) hgk₀) rfl hk₀ Gc hGc (fun t => (hmin t).1 ⟨k₀, hgk₀⟩)
  -- the compactification
  have hcomp : HasSNCCompactification K (N + 1) V.toScheme Gc := by
    have hTbprop : IsProper (Tb ↘ Spec (CommRingCat.of K)) := by
      rw [← HomIsOver.comp_over (f := ρb) (S := Spec (CommRingCat.of K))]
      infer_instance
    have hdiag := isAffineHom_diagonal_terminal_of_isSeparated (K := K) Tb
    have hDteff : (cartierPullback ρb (affineClosureInfinity π)).IsEffective :=
      cartierPullback_isEffective ρb _ (affineClosureInfinity_isEffective π)
    have hDtnef : CartierIsNef K (cartierPullback ρb (affineClosureInfinity π)) :=
      cartierIsNef_cartierPullback_of_isGloballyGenerated_nsmul ρb _ 1 le_rfl
        (by rw [one_nsmul]; exact affineClosureInfinity_globallyGenerated π)
    have hdimTb : topologicalKrullDim Tb = (N + 1 : ℕ) := etaleChart_topologicalKrullDim cTb
    have hdimXb : topologicalKrullDim (affineClosure π) = (N + 1 : ℕ) :=
      affineClosure_topologicalKrullDim π hπ cX
    obtain ⟨M, e', he', hcompe⟩ := hemb (r + 1) (affineClosureι π) inferInstance rfl
    haveI := he'
    obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart M K (e' (genericPoint Tb))
    have hProj : ∃ H : CartierDivisor Tb, CartierIsAmpleProj K H :=
      ⟨_, projectiveHyperplaneCartier_isAmpleProj e' (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) hi hcompe⟩
    have hDtbig : CartierIsBig K (cartierPullback ρb (affineClosureInfinity π)) :=
      cartierIsBig_cartierPullback_of_finiteDimensional ρb (hdimTb.trans hdimXb.symm)
        (fun m => cartier_finiteDimensional_sections_of_projective_all_dimensions hdimTb hProj _)
        (affineClosureInfinity_isBig π hπ cX (by omega))
    have hGnef : CartierIsNef K (1 • cartierPullback ρb (affineClosureInfinity π) - Gb) := by
      rw [one_nsmul]
      exact (hnefb (affineClosureInfinity π)
        (fun k => cartierIsGloballyGenerated_affineClosureInfinity_sub_hyperplane π _ (hig k))).2
    refine ⟨Tb, hTbi, hTbN, hTbo, hTbs, hTbprop, hdiag, hProj, rb, ξb, Gb,
      cartierPullback ρb (affineClosureInfinity π), 1, V.ι, inferInstance, inferInstance,
      inferInstance, hinjb, hcohb, hsncb, hGb0, hDteff, hDtnef, hDtbig, hGnef, hιb, ?_, rfl⟩
    intro x
    rw [Scheme.Opens.opensRange_ι,
      cartierPullback_isLocalEquationAt_one_iff ρb (affineClosureInfinity_isEffective π),
      affineClosureInfinity_isLocalEquationAt_one_iff]
    rfl
  -- bad points give bad members
  have hbadmem : ∀ (x : Spec (CommRingCat.of A)) (M : ℕ), 1 ≤ M →
      ModelThresholdBadAt cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1)) x
        (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
      ∃ s₁ : Fin r',
        (M : ℤ) * (1 - cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
          cT etaleCharts_cover) (ξ s₁)) ≤ cartierCoefficient Gc (ξ s₁) ∧
        x ∈ ρ '' closure ({ξ s₁} : Set V.toScheme) := by
    intro x M hM hbad
    have hbad' : ModelThresholdBadAt cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1)) x
        (fun j : {j : J // g j ≠ 0} => ((specFunctionRationalUnit (g j.1) j.2 :
          (Spec (CommRingCat.of A)).functionFieldˣ) : (Spec (CommRingCat.of A)).functionField)) M := by
      obtain ⟨U', hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxe, hpos, hineq⟩ := hbad
      exact ⟨U', hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxe, hpos,
        fun j hj => hineq j.1 hj⟩
    exact exists_bad_snc_member_of_modelThresholdBadAt cX
      (fun j : {j : J // g j ≠ 0} => specFunctionRationalUnit (g j.1) j.2)
      (fun j => specFunctionRationalUnit_effective (g j.1) j.2) M hM ρ hρ cT ξ hinj hcoh hsnc
      hcrep Gc hGc hGc0 hGcI x hbad'
  exact ⟨V.toScheme, inferInstance, instTo, hTN, hTs, ρ, hρdom, hρover, hρprop, hρ, cT, r', ξ,
    Gc, hGc, hinj, hcoh, hsnc, hcrep, hH, hgsupp, hGc0, hGcI, hmin, hs₀, hcomp, hbadmem⟩

end Model

/-- **F1 from sum Kawamata–Viehweg vanishing.** The mixed Fujita freeness statement F1 follows
from sum Kawamata–Viehweg vanishing on smooth projective varieties over algebraically closed
fields of characteristic zero. -/
theorem mixedFujitaFreeness_of_kvSum
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_compactifiedModels hKV
    (fun K _ _ _ => compactifiedStrictTransformModelStatement_of_charZero (K := K))

end MixedFujita
