/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantCartierPullback
public import MixedFujita.EtaleChartTaylorCoordinates

/-!
The relative canonical divisor K_{T/X} as a Cartier divisor (step 6). For a dominant morphism
ρ : T → X over K of smooth integral schemes and étale charts c on X and c' on T, let J(c, c') be
the determinant of the relative Jacobian of the function field map φ in the chart coordinates.
Changing the charts gives φ(g_c) J(c, c') = J(c₀, c') = J(c₀, c'₀) g'_{c'}, where g_c and g'_{c'}
are the local equations of K_X and K_T for the reference charts c₀ and c'₀. If R = J(c₀, c'₀) is
nonzero (ρ*ω₀ ≠ 0, for instance ρ birational), then K_{T/X} = K_T - ρ*K_X + div R has the local
equation J(c, c') at every point of c' over c, and K_T = ρ*K_X + K_{T/X} - div R. Coordinate
derivations commute with maps sending coordinates to coordinates, and φ composed with the germ
map of X at ρ(t) is the germ map of T at t composed with the stalk map, so J(c, c') is the image
of the determinant of the relative Jacobian of the stalk map at t: the local equation of K_{T/X}
at t is regular, and it is the Jacobian determinant whose Taylor expansion computes the log
discrepancy of test valuations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {n : ℕ}

section Algebra

variable {K R S S' : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
  [CommRing S'] [Algebra K S']

/-- Coordinate derivations commute with maps sending coordinates to coordinates. -/
theorem etaleCoordinateDerivation_comp (σ : S →ₐ[K] S') (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hσy : (σ.comp y).toRingHom.FormallyEtale) (j : Fin n)
    (s : S) :
    etaleCoordinateDerivation (σ.comp y) hσy j (σ s) = σ (etaleCoordinateDerivation y hy j s) := by
  rw [etaleCoordinateDerivation_chainRule σ y hy (σ.comp y) hσy j s,
    Finset.sum_eq_single j
      (fun k _ hkj => by
        rw [show σ (y (MvPolynomial.X k)) = (σ.comp y) (MvPolynomial.X k) from rfl,
          etaleCoordinateDerivation_coordinate, ite_eq_right hkj, mul_zero])
      (fun hj => absurd (Finset.mem_univ j) hj),
    show σ (y (MvPolynomial.X j)) = (σ.comp y) (MvPolynomial.X j) from rfl,
    etaleCoordinateDerivation_coordinate, ite_eq_left rfl, mul_one]

/-- The relative Jacobian of σ ∘ ψ in the coordinates σ ∘ y is the image of that of ψ. -/
theorem etaleRelativeJacobian_comp_coords (ψ : R →ₐ[K] S) (σ : S →ₐ[K] S')
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hσy : (σ.comp y).toRingHom.FormallyEtale) :
    etaleRelativeJacobian (σ.comp ψ) x (σ.comp y) hσy =
      (σ : S →+* S').mapMatrix (etaleRelativeJacobian ψ x y hy) := by
  refine Matrix.ext fun i j => ?_
  exact etaleCoordinateDerivation_comp σ y hy hσy j (ψ (x (MvPolynomial.X i)))

theorem etaleRelativeJacobian_det_comp_coords (ψ : R →ₐ[K] S) (σ : S →ₐ[K] S')
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hσy : (σ.comp y).toRingHom.FormallyEtale) :
    (etaleRelativeJacobian (σ.comp ψ) x (σ.comp y) hσy).det =
      σ (etaleRelativeJacobian ψ x y hy).det := by
  rw [etaleRelativeJacobian_comp_coords ψ σ x y hy hσy]
  exact (RingHom.map_det (σ : S →+* S') _).symm

/-- The relative Jacobian only depends on the coordinates. -/
theorem etaleRelativeJacobian_congr (ψ : R →ₐ[K] S) {x x' : MvPolynomial (Fin n) K →ₐ[K] R}
    (hxx : x = x') {y y' : MvPolynomial (Fin n) K →ₐ[K] S} (hyy : y = y')
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale) :
    etaleRelativeJacobian ψ x y hy = etaleRelativeJacobian ψ x' y' hy' := by
  subst hxx
  subst hyy
  rfl

end Algebra

section Scheme

universe u

variable {K : Type u} [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The function field map of a dominant morphism over K, as a K-algebra map. -/
noncomputable def dominantFunctionFieldAlgHom (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))] : X.functionField →ₐ[K] T.functionField where
  toRingHom := (dominantFunctionFieldMap ρ).hom
  commutes' k := by
    change ρ.stalkMap (genericPoint T) (X.presheaf.stalkSpecializes _
        (X.presheaf.germ ⊤ (genericPoint X) _ (Scheme.Modules.baseRingToGlobalSections K X k))) =
      T.presheaf.germ ⊤ (genericPoint T) _ (Scheme.Modules.baseRingToGlobalSections K T k)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply,
      ← scheme_appTop_baseRingToGlobalSections K ρ k]
    rfl

variable (ρ : T ⟶ X) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]

/-- J(c, c'): the determinant of the relative Jacobian of the function field map in the chart
coordinates. -/
noncomputable def chartRelativeJacobianDet (c : EtaleChart K X n) (c' : EtaleChart K T n) :
    T.functionField :=
  (etaleRelativeJacobian (dominantFunctionFieldAlgHom ρ) (etaleChartFunctionFieldCoords c)
    (etaleChartFunctionFieldCoords c') (etaleChartFunctionFieldCoords_formallyEtale c')).det

/-- φ(g_c) J(c, c') = J(c₀, c'₀) g'_{c'}. -/
theorem chartRelativeJacobianDet_change (c₀ c : EtaleChart K X n) (c'₀ c' : EtaleChart K T n) :
    dominantFunctionFieldAlgHom (K := K) ρ (etaleChartCanonicalEquation c₀ c : X.functionField) *
        chartRelativeJacobianDet ρ c c' =
      chartRelativeJacobianDet ρ c₀ c'₀ *
        (etaleChartCanonicalEquation c'₀ c' : T.functionField) := by
  rw [etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val]
  have h1 := etaleRelativeJacobian_det_change_source (dominantFunctionFieldAlgHom ρ)
    (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords c₀)
    (etaleChartFunctionFieldCoords_formallyEtale c)
    (etaleChartFunctionFieldCoords_formallyEtale c₀)
    (etaleChartFunctionFieldCoords c') (etaleChartFunctionFieldCoords_formallyEtale c')
  have h2 := etaleRelativeJacobian_det_change_target (dominantFunctionFieldAlgHom ρ)
    (etaleChartFunctionFieldCoords c₀) (etaleChartFunctionFieldCoords c'₀)
    (etaleChartFunctionFieldCoords c') (etaleChartFunctionFieldCoords_formallyEtale c'₀)
    (etaleChartFunctionFieldCoords_formallyEtale c')
  exact h1.symm.trans h2

/-- If J(c₀, c'₀) is a unit, so is every J(c, c'). -/
theorem isUnit_chartRelativeJacobianDet (c₀ : EtaleChart K X n) (c'₀ : EtaleChart K T n)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (c : EtaleChart K X n)
    (c' : EtaleChart K T n) : IsUnit (chartRelativeJacobianDet ρ c c') := by
  have h := chartRelativeJacobianDet_change ρ c₀ c c'₀ c'
  have hu : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀ *
      (etaleChartCanonicalEquation c'₀ c' : T.functionField)) := hR.mul (Units.isUnit _)
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_right hu

variable (n) in
/-- The relative canonical divisor K_{T/X} = K_T - ρ*K_X + div J(c₀, c'₀). -/
noncomputable def relativeCanonicalDivisor (c₀ : EtaleChart K X n)
    (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) : CartierDivisor T :=
  canonicalDivisor n c'₀ hT - cartierPullback ρ (canonicalDivisor n c₀ hX) +
    principalCartierDivisor T hR.unit

/-- K_T = ρ*K_X + K_{T/X} - div J(c₀, c'₀). -/
theorem canonicalDivisor_eq_pullback_add_relative (c₀ : EtaleChart K X n)
    (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) :
    canonicalDivisor n c'₀ hT = cartierPullback ρ (canonicalDivisor n c₀ hX) +
      relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR - principalCartierDivisor T hR.unit := by
  unfold relativeCanonicalDivisor
  abel

/-- The local equation of K_{T/X} at t is J(c, c') for charts c at ρ(t) and c' at t. -/
theorem relativeCanonicalDivisor_isLocalEquationAt (c₀ : EtaleChart K X n)
    (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : T) (c : EtaleChart K X n)
    (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U) :
    (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR).IsLocalEquationAt t
      (isUnit_chartRelativeJacobianDet ρ c₀ c'₀ hR c c').unit := by
  have h1 := canonicalDivisor_isLocalEquationAt c'₀ hT c' hc'
  have h2 := (cartierPullback_isLocalEquationAt ρ (canonicalDivisor n c₀ hX) t
    (canonicalDivisor_isLocalEquationAt c₀ hX c hc)).inv
  have h3 := CartierDivisor.isLocalEquationAt_principalCartierDivisor t hR.unit
  have h := (h1.mul h2).mul h3
  rw [← sub_eq_add_neg] at h
  unfold relativeCanonicalDivisor
  convert h using 1
  apply Units.ext
  have hJ := chartRelativeJacobianDet_change ρ c₀ c c'₀ c'
  have hφg : dominantFunctionFieldAlgHom (K := K) ρ
      (etaleChartCanonicalEquation c₀ c : X.functionField) ≠ 0 :=
    (map_ne_zero _).mpr (Units.ne_zero _)
  have hval : ((Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
      (etaleChartCanonicalEquation c₀ c) : T.functionFieldˣ) : T.functionField) =
        dominantFunctionFieldAlgHom (K := K) ρ
          (etaleChartCanonicalEquation c₀ c : X.functionField) := rfl
  rw [IsUnit.unit_spec, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, hval,
    IsUnit.unit_spec]
  field_simp
  linear_combination hJ

/-- φ composed with the germ map of X at ρ(t) is the germ map of T at t composed with the stalk
map. -/
theorem dominantFunctionFieldAlgHom_comp_stalk (t : T) :
    (dominantFunctionFieldAlgHom (K := K) ρ).comp (stalkFunctionFieldAlgHom (K := K) (ρ t)) =
      (stalkFunctionFieldAlgHom (K := K) t).comp (schemeStalkMapAlgHom (K := K) ρ t) := by
  apply AlgHom.ext
  intro a
  obtain ⟨V, hV, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty V := ⟨⟨ρ t, hV⟩⟩
  have : Nonempty (ρ ⁻¹ᵁ V) := ⟨⟨t, hV⟩⟩
  change (dominantFunctionFieldMap ρ).hom (algebraMap (X.presheaf.stalk (ρ t)) X.functionField
      (X.presheaf.germ V (ρ t) hV s)) =
    algebraMap (T.presheaf.stalk t) T.functionField (ρ.stalkMap t (X.presheaf.germ V (ρ t) hV s))
  rw [Scheme.algebraMap_germ_eq_germToFunctionField,
    dominantFunctionFieldMap_germ ρ V (ρ ⁻¹ᵁ V) le_rfl, Scheme.Hom.germ_stalkMap_apply,
    Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.Hom.appLE_eq_app]

/-- J(c, c') is the image in the function field of the determinant of the relative Jacobian of
the stalk map at t in the chart coordinates. -/
theorem chartRelativeJacobianDet_eq_stalk (t : T) (c : EtaleChart K X n) (hc : ρ t ∈ c.U)
    (c' : EtaleChart K T n) (hc' : t ∈ c'.U) :
    chartRelativeJacobianDet ρ c c' = stalkFunctionFieldAlgHom (K := K) t
      (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ t)
        (etaleChartStalkCoords c (ρ t) hc) (etaleChartStalkCoords c' t hc')
        (etaleChartStalkCoords_formallyEtale c' t hc')).det := by
  have hσy := formallyEtale_comp (stalkFunctionFieldAlgHom (K := K) t)
    (stalkFunctionFieldAlgHom_formallyEtale t) (etaleChartStalkCoords c' t hc')
    (etaleChartStalkCoords_formallyEtale c' t hc')
  rw [← etaleRelativeJacobian_det_comp_coords (schemeStalkMapAlgHom (K := K) ρ t)
    (stalkFunctionFieldAlgHom (K := K) t) _ _ (etaleChartStalkCoords_formallyEtale c' t hc') hσy,
    ← dominantFunctionFieldAlgHom_comp_stalk ρ t]
  unfold chartRelativeJacobianDet
  rw [etaleRelativeJacobian_congr (dominantFunctionFieldAlgHom ρ)
    (etaleChart_stalkFunctionField_comp_stalkCoords c (ρ t) hc).symm
    (etaleChart_stalkFunctionField_comp_stalkCoords c' t hc').symm
    (etaleChartFunctionFieldCoords_formallyEtale c') hσy]
  rfl

/-- The local equation of K_{T/X} at t is regular at t. -/
theorem relativeCanonicalDivisor_localEquation_mem_stalk (c₀ : EtaleChart K X n)
    (c'₀ : EtaleChart K T n) (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : T)
    (c : EtaleChart K X n) (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U) :
    (((isUnit_chartRelativeJacobianDet ρ c₀ c'₀ hR c c').unit : T.functionFieldˣ) :
      T.functionField) ∈ (algebraMap (T.presheaf.stalk t) T.functionField).range := by
  rw [IsUnit.unit_spec, chartRelativeJacobianDet_eq_stalk ρ t c hc c' hc']
  exact ⟨_, rfl⟩

/-- The log discrepancy of chart test valuations is the value of the local equation of K_{T/X}:
the local equation J(c, c') of K_{T/X} at t is the image of a germ a at t, and in the Taylor
coordinates of the centred chart c' the value v(det J) of the map of completed local rings, for
any completion coordinates at ρ(t), is the weighted order of the Taylor expansion of a. -/
theorem relativeCanonicalDivisor_testValuation [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
    (hX : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c'₀ : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤)
    (hR : IsUnit (chartRelativeJacobianDet ρ c₀ c'₀)) (t : T) (c : EtaleChart K X n)
    (hc : ρ t ∈ c.U) (c' : EtaleChart K T n) (hc' : t ∈ c'.U)
    (β : X.presheaf.stalk (ρ t) →ₐ[K] K) (β' : T.presheaf.stalk t →ₐ[K] K) :
    ∃ a : T.presheaf.stalk t,
      (relativeCanonicalDivisor n ρ c₀ hX c'₀ hT hR).IsLocalEquationAt t
        (isUnit_chartRelativeJacobianDet ρ c₀ c'₀ hR c c').unit ∧
      stalkFunctionFieldAlgHom (K := K) t a = chartRelativeJacobianDet ρ c c' ∧
      ∃ ep : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk t))
          (T.presheaf.stalk t) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ i, stalkTaylorExpansion t ep
          (etaleChartCenteredStalkCoords c' t hc' β' (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
        ∀ (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk (ρ t)))
            (X.presheaf.stalk (ρ t)) ≃ₐ[K] MvPowerSeries (Fin n) K) (w : Fin n → ℕ),
          (powerSeriesJacobian (schemeCompletedStalkMap ρ t ez ep)).det.weightedOrder w =
            (stalkTaylorExpansion t ep a).weightedOrder w := by
  obtain ⟨ep, hep, hv⟩ := etaleChart_testValuation_jacobian_weightedOrder ρ t c hc c' hc' β β'
  exact ⟨_, relativeCanonicalDivisor_isLocalEquationAt ρ c₀ hX c'₀ hT hR t c hc c' hc',
    (chartRelativeJacobianDet_eq_stalk ρ t c hc c' hc').symm, ep, hep, hv⟩

end Scheme

end MixedFujita
