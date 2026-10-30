/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PointedAffineBertini
public import MixedFujita.PointIdealGeneratorDifferentials
public import MixedFujita.EtaleChartBertini
public import MixedFujita.SmoothClosedPoints

@[expose] public section
namespace MixedFujita
open AlgebraicGeometry CategoryTheory TopologicalSpace
open KaehlerDifferential
open OAI.MaximalSeshadri.LinearBertini (specializedSection)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Etale coordinates supply the first-jet hypothesis of pointed Bertini internally. -/
theorem etale_pointed_bertini_regular_equations
    {K R ι : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] [Fintype ι] {n : ℕ}
    (σ : MvPolynomial (Fin n) K →ₐ[K] R) (hσ : σ.toRingHom.FormallyEtale)
    (j : Fin n) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      specializedSection v t ≠ 0 ∧ β (specializedSection v t) = 0 ∧
        Algebra.Smooth K (R ⧸ Ideal.span ({specializedSection v t} : Set R)) := by
  let P := MvPolynomial (Fin n) K
  letI : Algebra P R := σ.toRingHom.toAlgebra
  let : IsScalarTower K P R := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  have : Algebra.FormallyEtale P R := hσ
  have : Algebra.FormallySmooth K R := Algebra.FormallySmooth.comp K P R
  let : Algebra.Smooth K R := ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact affine_pointed_bertini_regular_equations
    (differentialFrameOfBasis (etaleCoordinateBasis σ hσ)) β v hspan
    (etale_pointIdealGenerators_nonzero_frame_coefficient σ hσ j β v hspan)

/-- A smooth affine hypersurface through a rational point, with its nonzero equation constructed. -/
theorem etale_rationalPoint_exists_nonzero_smooth_equation
    {K R : Type*} [Field K] [CharZero K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] {n : ℕ}
    (σ : MvPolynomial (Fin n) K →ₐ[K] R) (hσ : σ.toRingHom.FormallyEtale)
    (j : Fin n) (β : R →ₐ[K] K) :
    ∃ g : R, g ≠ 0 ∧ β g = 0 ∧ Algebra.Smooth K (R ⧸ Ideal.span {g}) := by
  classical
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  obtain ⟨s, hs⟩ := (RingHom.ker β.toRingHom).fg_of_isNoetherianRing
  let ι := {r : R // r ∈ s}
  let v : ι → R := Subtype.val
  have hrange : Set.range v = (s : Set R) := by ext r; simp [v, ι]
  have hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom := by
    simpa only [hrange] using hs
  obtain ⟨p, hp, hcut⟩ := etale_pointed_bertini_regular_equations σ hσ j β v hspan
  have hex : ∃ t : ι → K, MvPolynomial.aeval t p ≠ 0 := by
    by_contra! ht
    apply hp
    apply MvPolynomial.funext
    intro t
    simpa only [MvPolynomial.aeval_eq_eval, map_zero] using ht t
  obtain ⟨t, ht⟩ := hex
  exact ⟨specializedSection v t, hcut t ht⟩

universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- The actual closed point supplies its evaluation; the entire affine cut is smooth. -/
theorem smoothScheme_etaleChart_closedPoint_exists_smooth_equation
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] [Smooth (X ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (c : EtaleChart K X n) (hn : 0 < n)
    (x : X) (hx : x ∈ c.U) (hclosed : IsClosed {x}) :
    ∃ g : Γ(X, c.U), g ≠ 0 ∧
      rationalAffineGermPoint (K := K) x hx (smoothAffineClosedPointEvaluation (K := K) c.isAffine x hx hclosed) g = 0 ∧
      Algebra.Smooth K (Γ(X, c.U) ⧸ Ideal.span {g}) := by
  have : Algebra.Smooth K Γ(X, c.U) := etaleChart_smooth c
  exact etale_rationalPoint_exists_nonzero_smooth_equation c.coords c.formallyEtale ⟨0, hn⟩
    (rationalAffineGermPoint (K := K) x hx (smoothAffineClosedPointEvaluation (K := K) c.isAffine x hx hclosed))

end MixedFujita