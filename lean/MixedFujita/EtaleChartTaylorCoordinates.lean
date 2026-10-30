/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleRelativeJacobian
public import MixedFujita.CanonicalDivisor
public import MixedFujita.SmoothSchemeCoordinates
public import MixedFujita.SmoothAffineCompletion

/-!
Taylor coordinates of étale charts and the log discrepancy of chart test valuations (step 6).
Coordinates differing by constants have the same differentials, hence the same coordinate basis
and the same relative Jacobian. The coordinates of an étale chart on a scheme locally of finite
type over K are étale, since a finite type algebra over the Noetherian polynomial ring is finitely
presented. At a point with a K-valued stalk point, the chart coordinates centred at the point give
completion coordinates of the stalk in which the Taylor expansion sends them to the variables.
Hence for a morphism ρ : T' → T over K, étale charts at ρ(p) and at p and K-points of the stalks,
the log discrepancy Σ w + v(det J) of the monomial test valuation in the centred chart coordinates
at p is Σ w + v(det J_ρ), the value of the local equation det(∂ρ^♯x_i/∂y_j) of K_{T'/T} in the two
charts, for any completion coordinates at ρ(p).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

variable {n : ℕ}

section Translation

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

/-- Coordinates differing by constants have the same coordinate basis. -/
theorem etaleCoordinateBasis_eq_of_sub_const (y y' : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale) (c : Fin n → K)
    (h : ∀ i, y' (MvPolynomial.X i) = y (MvPolynomial.X i) - algebraMap K S (c i)) :
    etaleCoordinateBasis y' hy' = etaleCoordinateBasis y hy := by
  apply Module.Basis.eq_of_apply_eq
  intro i
  rw [etaleCoordinateBasis_apply, etaleCoordinateBasis_apply, h i, map_sub,
    Derivation.map_algebraMap, sub_zero]

/-- Coordinates differing by constants give the same relative Jacobian. -/
theorem etaleRelativeJacobian_eq_of_sub_const (ψ : R →ₐ[K] S)
    (x x' : MvPolynomial (Fin n) K →ₐ[K] R) (c : Fin n → K)
    (hx : ∀ i, x' (MvPolynomial.X i) = x (MvPolynomial.X i) - algebraMap K R (c i))
    (y y' : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
    (hy' : y'.toRingHom.FormallyEtale) (d : Fin n → K)
    (hyd : ∀ i, y' (MvPolynomial.X i) = y (MvPolynomial.X i) - algebraMap K S (d i)) :
    etaleRelativeJacobian ψ x' y' hy' = etaleRelativeJacobian ψ x y hy := by
  refine Matrix.ext fun i j => ?_
  change (etaleCoordinateBasis y' hy').repr (D K S (ψ (x' (MvPolynomial.X i)))) j =
    (etaleCoordinateBasis y hy).repr (D K S (ψ (x (MvPolynomial.X i)))) j
  rw [etaleCoordinateBasis_eq_of_sub_const y y' hy hy' d hyd, hx i, map_sub, AlgHom.commutes,
    map_sub, Derivation.map_algebraMap, sub_zero]

end Translation

section Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra

/-- The coordinates of an étale chart on a scheme locally of finite type over K are étale. -/
theorem etaleChart_coords_etale [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) : c.coords.Etale := by
  have h1 : (algebraMap K Γ(X, c.U)).FiniteType := by
    change ((X.baseRingToStructurePresheaf K).app (op c.U)).hom.FiniteType
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
    have h1 : ((X ↘ Spec (CommRingCat.of K)).appLE ⊤ c.U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨c.U, c.isAffine⟩ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  have hcomp : c.coords.toRingHom.comp (algebraMap K (MvPolynomial (Fin n) K)) =
      algebraMap K Γ(X, c.U) := c.coords.comp_algebraMap
  have h2 : c.coords.toRingHom.FiniteType := by
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap K (MvPolynomial (Fin n) K))
    rw [hcomp]
    exact h1
  have h3 : c.coords.toRingHom.FinitePresentation := RingHom.FinitePresentation.of_finiteType.mp h2
  let _ := c.coords.toRingHom.toAlgebra
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) K) Γ(X, c.U) := c.formallyEtale
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) K) Γ(X, c.U) := h3
  change Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, c.U)
  exact ⟨‹_›, ‹_›⟩

/-- The chart coordinates centred at a point with a K-valued stalk point, in the stalk. -/
noncomputable def etaleChartCenteredStalkCoords (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (β : X.presheaf.stalk x →ₐ[K] K) : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x :=
  (sectionStalkAlgHom c.U x hx).comp
    (centeredPolynomialChart c.coords (rationalAffineGermPoint x hx β))

theorem etaleChartCenteredStalkCoords_variable (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (β : X.presheaf.stalk x →ₐ[K] K) (i : Fin n) :
    etaleChartCenteredStalkCoords c x hx β (MvPolynomial.X i) =
      etaleChartStalkCoords c x hx (MvPolynomial.X i) - algebraMap K (X.presheaf.stalk x)
        (rationalAffineGermPoint x hx β (c.coords (MvPolynomial.X i))) := by
  rw [etaleChartCenteredStalkCoords, AlgHom.comp_apply, centeredPolynomialChart_variable,
    map_sub, AlgHom.commutes]
  rfl

theorem etaleChartCenteredStalkCoords_formallyEtale
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] (c : EtaleChart K X n) (x : X)
    (hx : x ∈ c.U) (β : X.presheaf.stalk x →ₐ[K] K) :
    (etaleChartCenteredStalkCoords c x hx β).toRingHom.FormallyEtale := by
  have hg := centeredPolynomialChart_etale c.coords (rationalAffineGermPoint x hx β)
    (etaleChart_coords_etale c)
  have hfe : (centeredPolynomialChart c.coords
      (rationalAffineGermPoint x hx β)).toRingHom.FormallyEtale := by
    let _ := (centeredPolynomialChart c.coords (rationalAffineGermPoint x hx β)).toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, c.U) := hg
    exact Algebra.Etale.formallyEtale
  exact formallyEtale_comp _ (sectionStalkAlgHom_formallyEtale c.U c.isAffine x hx) _ hfe

/-- Centring does not change the coordinate basis of Ω. -/
theorem etaleChartCenteredStalkCoords_basis [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (β : X.presheaf.stalk x →ₐ[K] K) :
    etaleCoordinateBasis (etaleChartCenteredStalkCoords c x hx β)
        (etaleChartCenteredStalkCoords_formallyEtale c x hx β) =
      etaleCoordinateBasis (etaleChartStalkCoords c x hx)
        (etaleChartStalkCoords_formallyEtale c x hx) :=
  etaleCoordinateBasis_eq_of_sub_const _ _ _ _ _ (etaleChartCenteredStalkCoords_variable c x hx β)

/-- Completion coordinates at x in which the Taylor expansion sends the centred chart coordinates
to the variables; they compute the order of germs. -/
theorem etaleChart_exists_taylorCoordinates [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (β : X.presheaf.stalk x →ₐ[K] K) :
    ∃ e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[K]
      MvPowerSeries (Fin n) K,
      (∀ i, stalkTaylorExpansion x e (etaleChartCenteredStalkCoords c x hx β (MvPolynomial.X i)) =
        MvPowerSeries.X i) ∧
      ∀ s, (e (AdicCompletion.of (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (X.presheaf.stalk x) s)).order = localAdicOrder (X.presheaf.stalk x) s := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : c.U)
  let := cartierBaseOpenLocalScalarTower (K := K) x hx
  let α := rationalAffineGermPoint x hx β
  have hα : RingHom.ker α.toRingHom = (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal :=
    rationalAffineGermPoint_ker x hx β c.isAffine
  let : (RingHom.ker α.toRingHom).IsMaximal := rationalPoint_ker_isMaximal α
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (RingHom.ker α.toRingHom) := by
    have H := c.isAffine.isLocalization_stalk (⟨x, hx⟩ : c.U)
    simpa only [hα] using H
  obtain ⟨e, he, hord⟩ := centeredEtaleChart_exists_completionCoordinates
    (centeredPolynomialChart c.coords α)
    (centeredPolynomialChart_etale c.coords α (etaleChart_coords_etale c)) α
    (centeredPolynomialChart_constantCoeff c.coords α) (X.presheaf.stalk x)
  refine ⟨e, fun i => ?_, hord⟩
  have h := he (MvPolynomial.X i)
  rw [MvPolynomial.coe_X] at h
  exact h

section Morphism

variable {T T' : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [T'.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T' ↘ Spec (CommRingCat.of K))]

/-- The log discrepancy of chart test valuations. For étale charts c at ρ(p) and c' at p and
K-points of the stalks, there are completion coordinates at p in which the centred coordinates of
c' are the variables, such that for all completion coordinates at ρ(p) and all weights, v(det J) of
the map of completions is the value of the Taylor expansion of det(∂ρ^♯x_i/∂y_j), the local
equation of K_{T'/T} in the two charts. -/
theorem etaleChart_testValuation_jacobian_weightedOrder [CharZero K] (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T') (c : EtaleChart K T n) (hc : ρ p ∈ c.U)
    (c' : EtaleChart K T' n) (hc' : p ∈ c'.U) (β : T.presheaf.stalk (ρ p) →ₐ[K] K)
    (β' : T'.presheaf.stalk p →ₐ[K] K) :
    ∃ ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
        (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K,
      (∀ i, stalkTaylorExpansion p ep
        (etaleChartCenteredStalkCoords c' p hc' β' (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
      ∀ (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
          (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K) (w : Fin n → ℕ),
        (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w =
          (stalkTaylorExpansion p ep (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ p)
            (etaleChartStalkCoords c (ρ p) hc) (etaleChartStalkCoords c' p hc')
            (etaleChartStalkCoords_formallyEtale c' p hc')).det).weightedOrder w := by
  obtain ⟨ez₀, hez₀, -⟩ := etaleChart_exists_taylorCoordinates c (ρ p) hc β
  obtain ⟨ep, hep, -⟩ := etaleChart_exists_taylorCoordinates c' p hc' β'
  refine ⟨ep, hep, fun ez w => ?_⟩
  rw [schemeTestValuation_jacobian_weightedOrder_eq_relative ρ p ez ez₀ ep
      (etaleChartCenteredStalkCoords c (ρ p) hc β) (etaleChartCenteredStalkCoords c' p hc' β')
      (etaleChartCenteredStalkCoords_formallyEtale c' p hc' β') hez₀ hep w,
    etaleRelativeJacobian_eq_of_sub_const _ (etaleChartStalkCoords c (ρ p) hc) _ _
      (etaleChartCenteredStalkCoords_variable c (ρ p) hc β) (etaleChartStalkCoords c' p hc') _
      (etaleChartStalkCoords_formallyEtale c' p hc') _ _
      (etaleChartCenteredStalkCoords_variable c' p hc' β')]

end Morphism

end Scheme

end MixedFujita
