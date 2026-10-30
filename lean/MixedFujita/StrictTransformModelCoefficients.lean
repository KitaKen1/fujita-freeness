/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ConnectedStrictTransformQuotientChart

/-!
The coefficients h = 1, k = 0 and a = 0 on the strict transform, obtained from actual divisors.
The vanishing of a uses one original generator not in the hyperplane prime and the coefficient
bound of the principalized sum. It does not require a chosen local equation of the fixed part.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Nonvanishing

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- A regular function outside a prime has coefficient zero in its actual principal divisor. -/
theorem principal_coefficient_spec_eq_zero_of_notMem (g : A)
    (u : (Spec (CommRingCat.of A)).functionFieldˣ)
    (hu : (u : (Spec (CommRingCat.of A)).functionField) =
      (Spec (CommRingCat.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))
    (p : Spec (CommRingCat.of A)) (hg : g ∉ p.asIdeal) :
    cartierCoefficient (principalCartierDivisor (Spec (CommRingCat.of A)) u) p = 0 := by
  have hunit := (spec_germ_isUnit_iff (CommRingCat.of A) p g).mpr hg
  have h := scheme_ord_stalk_unit p hunit.unit
  rw [IsUnit.unit_spec, Scheme.algebraMap_germ_eq_germToFunctionField] at h
  rw [cartierCoefficient_principal, hu]
  exact h

end Nonvanishing

section Model

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [IsNoetherianRing A] {n : ℕ}
  [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
  {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

include K n in
/-- The effective principalized divisor has coefficient zero at a prime lift where one original
generator is a unit. The inequality is the minimum formula for the principalized sum. -/
theorem principalized_coefficient_eq_zero_at_lift
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ]
    (z : CodimensionOnePoint T) (hz : Order.coheight (ρ (z : T)) = 1)
    (hbij : Function.Bijective (ρ.stalkMap (z : T)))
    (g : A) (u : (Spec (CommRingCat.of A)).functionFieldˣ)
    (hu : (u : (Spec (CommRingCat.of A)).functionField) =
      (Spec (CommRingCat.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))
    (hg : g ∉ (ρ (z : T)).asIdeal) (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hle : cartierCoefficient Gc (z : T) ≤ cartierCoefficient
      (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A)) u)) (z : T)) :
    cartierCoefficient Gc (z : T) = 0 := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Smooth (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth n _
  have := smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have := smoothOverField_codimensionOne_stalk_DVR (K := K)
    (⟨ρ (z : T), hz⟩ : CodimensionOnePoint (Spec (CommRingCat.of A)))
  rw [cartierCoefficient_pullback_of_stalkMap_bijective ρ z hz hbij,
    principal_coefficient_spec_eq_zero_of_notMem g u hu _ hg] at hle
  exact le_antisymm hle (cartierCoefficient_nonneg_of_isEffective Gc hGc _)

end Model

section Member

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [IsNoetherianRing A] {N r : ℕ}
  [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
  {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

/-- The strict-transform member and its three coefficients are constructed from the image
hyperplane and one original nondegenerate generator. No h = 1, k = 0 or a = 0 is supplied. -/
theorem exists_strictTransform_member_coefficients
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [IsProper ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1)) (cT : EtaleChart K T (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    (ξ : Fin r → T) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (hH : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
        (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (z : T) = 0)
    (g : A) (u : (Spec (CommRingCat.of A)).functionFieldˣ)
    (hu : (u : (Spec (CommRingCat.of A)).functionField) =
      (Spec (CommRingCat.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))
    (hg : g ∉ Ideal.span {φ (MvPolynomial.X 0)}) (Gc : CartierDivisor T) (hGc : Gc.IsEffective)
    (hle : ∀ t : T, cartierCoefficient Gc t ≤ cartierCoefficient
      (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A)) u)) t) :
    ∃ s₀ : Fin r,
      (ρ (ξ s₀)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)} ∧
      Function.Bijective (ρ.stalkMap (ξ s₀)) ∧
      cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
        (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (ξ s₀) = 1 ∧
      cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
        cT etaleCharts_cover) (ξ s₀) = 0 ∧
      cartierCoefficient Gc (ξ s₀) = 0 := by
  obtain ⟨b, hb, hord⟩ := exists_hyperplane_generic_point A φ hφ
  have hcoef : cartierCoefficient (principalCartierDivisor (Spec (CommRingCat.of A))
      (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0)) (b : _) = 1 := by
    rw [cartierCoefficient_principal]
    exact hord
  obtain ⟨s₀, hs₀, hbij, hcoeff⟩ := exists_snc_member_over_prime (K := K) (n := N + 1)
    ρ hρ ξ b _ (hcoef ▸ one_ne_zero) hH
  have himage : (ρ (ξ s₀)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)} := by rw [hs₀, hb]
  have hz : Order.coheight (ρ (ξ s₀)) = 1 := hs₀ ▸ b.property
  exact ⟨s₀, himage, hbij, hcoeff.trans hcoef,
    crepantBoundaryCartier_coefficient_eq_zero_of_stalkMap_bijective ρ hρ cX cT
      ⟨ξ s₀, hξ s₀⟩ hz hbij,
    principalized_coefficient_eq_zero_at_lift (K := K) (n := N + 1) ρ ⟨ξ s₀, hξ s₀⟩ hz hbij
      g u hu (himage.symm ▸ hg) Gc hGc (hle _)⟩

end Member

end MixedFujita
