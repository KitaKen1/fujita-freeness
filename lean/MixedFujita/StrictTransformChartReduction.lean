/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateHyperplaneQuotient

/-!
The restriction theorem for coordinate hyperplanes from strict transform charts (step 9).

`StrictTransformChartStatement` asks, for a bad point x of a family g on Spec A in the situation of
`CoordinateHyperplaneQuotientRestriction`, for a chart of the strict transform where a component
meets it over x with the adjunction inequality: a domain C with étale coordinates y_0, …, y_N and
an injective birational μ : A → C with μ(x_0) = y_0 w (a chart of a principalized model where
y_0 = 0 is the strict transform H'), a formally étale ρ : C/(y_0) → B to a domain birational over
C/(y_0) whose kernel contracts to (x_0) (H' maps onto H generically), a prime of B over x
containing y_{l+1} (the meeting point on the component E = {y_{l+1} = 0}), monomial
factorizations det J(μ) = (∏ y_s^{κ_s}) u and w = (∏ y_s^{η_s}) u' with κ_0 = η_0 = 0, η ≤ κ and
u, u' units at the prime, and μ(g_j) divisible by y_{l+1}^a with M (1 + κ_{l+1} − η_{l+1}) ≤ a.
This is what a principalized simple normal crossing model gives at a point of H' ∩ E over x for a
component E which is non-klt for the pair (X, H + 𝔞/M), and the connectedness lemma
(Kollár–Shokurov, from relative vanishing) provides such a component meeting H' over x. The
statement implies the quotient case (`coordinateHyperplaneQuotientRestriction_of_strictTransformCharts`):
the local ring of A at x_0 is a valuation ring (check-330), so A/(x_0) → B is injective and
birational (check-329) and the strict transform model applies (check-328). Hence F1 follows from
sum KV and strict transform charts (`mixedFujitaFreeness_of_kvSum_of_strictTransformCharts`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Charts

variable (K : Type u) [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- Strict transform charts: at a bad point of a family on Spec A, in the situation of
`CoordinateHyperplaneQuotientRestriction`, a chart of the strict transform of x_0 = 0 meets a
component over the point with the adjunction inequality M (1 + κ − η) ≤ a. -/
def StrictTransformChartStatement : Prop :=
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
        (l : Fin N) (_ : ρ (Ideal.Quotient.mk _ (y (MvPolynomial.X l.succ))) ∈ 𝔓)
        (κ η : Fin (N + 1) → ℕ) (_ : κ 0 = 0) (_ : η 0 = 0) (_ : ∀ s, η s ≤ κ s) (u u' : C)
        (_ : ρ (Ideal.Quotient.mk _ u) ∉ 𝔓) (_ : ρ (Ideal.Quotient.mk _ u') ∉ 𝔓)
        (_ : (etaleRelativeJacobian μ φ y hy).det = (∏ s, y (MvPolynomial.X s) ^ κ s) * u)
        (_ : w = (∏ s, y (MvPolynomial.X s) ^ η s) * u') (a : ℕ),
        (∀ j, ∃ r : C, μ (g j) = y (MvPolynomial.X l.succ) ^ a * r) ∧
          M * (1 + (κ l.succ - η l.succ)) ≤ a

variable {K}

/-- The restriction theorem for the coordinate hyperplane as a quotient from strict transform
charts. -/
theorem coordinateHyperplaneQuotientRestriction_of_strictTransformCharts
    (h : StrictTransformChartStatement K) : CoordinateHyperplaneQuotientRestriction K := by
  classical
  intro A _ _ _ N _ cX φ hφ _ _ cZ J _ g M hN hM χ hbad
  obtain ⟨C, _, _, _, y, hy, μ, hμ, hbirμ, w, hw, B, _, _, _, ρ, hv, hvfe, hker, hρ, 𝔓, h𝔓p,
    h𝔓, l, hl, κ, η, hκ0, hη0, hηκ, u, u', hu, hu', hJμ, hwfac, a, hg, hMa⟩ :=
    h A N cX φ hφ g M hN hM χ hbad
  haveI := h𝔓p
  -- the local ring of A along x_0 = 0 is a valuation ring
  haveI : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := N + 1)
  haveI : (Ideal.span {φ (MvPolynomial.X 0)}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  haveI := valuationRing_localization_span_of_smooth (K := K) A (φ (MvPolynomial.X 0))
    (etaleCoordinate_ne_zero φ hφ 0)
  -- the strict transform is injective and birational over the hyperplane
  obtain ⟨hψ, hbir⟩ := strictTransformHyperplaneMap_injective_birational φ y μ hμ hbirμ w hw ρ
    hker hρ
  exact modelThresholdBadAt_hyperplane_of_strictTransform φ hφ cZ y hy μ w hw ρ hv hvfe hψ hbir χ
    𝔓 h𝔓 l hl κ η hκ0 hη0 hηκ u u' hu hu' hJμ hwfac g a hg M hMa

/-- F1 from sum KV and strict transform charts. -/
theorem mixedFujitaFreeness_of_kvSum_of_strictTransformCharts
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hST : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      StrictTransformChartStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_coordinateHyperplaneQuotientRestriction hKV
    (fun K _ _ _ => coordinateHyperplaneQuotientRestriction_of_strictTransformCharts (hST K))

end Charts

end MixedFujita
