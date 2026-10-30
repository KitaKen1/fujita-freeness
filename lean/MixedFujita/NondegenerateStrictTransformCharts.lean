/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformMonomialCharts

/-!
Strict transform charts only in the nondegenerate case (step 9).

If every member of the family vanishes on the hyperplane x_0 = 0, the restriction to the
hyperplane is the zero family, and every closed point of the hyperplane is bad for it
(`modelThresholdBadAt_of_forall_eq_zero`, in positive dimension). So the strict transform charts
need only be produced when some g_j does not lie in (x_0)
(`NondegenerateStrictTransformChartStatement`); this is the case in which the strict transform H'
has a = 0 in the connectedness argument. It implies the quotient case over an algebraically closed
field (`coordinateHyperplaneQuotientRestriction_of_nondegenerateCharts`), follows from the charts of
check-342 (`nondegenerateStrictTransformChartStatement_of_monomialCharts`), and F1 follows from sum
KV and the nondegenerate charts (`mixedFujitaFreeness_of_kvSum_of_nondegenerateCharts`).
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

section Charts

variable (K : Type u) [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- Strict transform charts with the factorizations as quotients of monomials, asked only when
some member of the family does not vanish on the hyperplane x_0 = 0. -/
def NondegenerateStrictTransformChartStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra K A] (N : ℕ)
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A), φ.toRingHom.FormallyEtale →
    ∀ [IsDomain (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})]
      {J : Type} [Finite J] (g : J → A) (M : ℕ), 1 ≤ N → 1 ≤ M →
      ∀ χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K,
      (∃ j, g j ∉ Ideal.span {φ (MvPolynomial.X 0)}) →
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

/-- The charts of check-342 are in particular nondegenerate charts. -/
theorem nondegenerateStrictTransformChartStatement_of_monomialCharts
    (h : StrictTransformMonomialChartStatement K) : NondegenerateStrictTransformChartStatement K := by
  intro A _ _ _ N _ cX φ hφ _ J _ g M hN hM χ _ hbad
  exact h A N cX φ hφ g M hN hM χ hbad

/-- The restriction theorem for the coordinate hyperplane as a quotient from the nondegenerate
strict transform charts, over an algebraically closed field. -/
theorem coordinateHyperplaneQuotientRestriction_of_nondegenerateCharts [IsAlgClosed K]
    (h : NondegenerateStrictTransformChartStatement K) :
    CoordinateHyperplaneQuotientRestriction K := by
  classical
  intro A _ _ _ N _ cX φ hφ _ _ cZ J _ g M hN hM χ hbad
  by_cases hnd : ∃ j, g j ∉ Ideal.span {φ (MvPolynomial.X 0)}
  · obtain ⟨C, _, _, _, y, hy, μ, hμ, hbirμ, w, hw, B, _, _, _, ρ, hv, hvfe, hker, hρ, 𝔓, h𝔓p,
      h𝔓, l, hl, κ, η, J₁, J₂, W₁, W₂, hJ₁, hJ₂, hW₁, hW₂, hJμ, hwfac, a, hg, hMa⟩ :=
      h A N cX φ hφ g M hN hM χ hnd hbad
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
  · push Not at hnd
    have : Smooth (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})) ↘
        Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth N _
    refine modelThresholdBadAt_of_forall_eq_zero hN cZ (specAlgHomPoint χ)
      (specAlgHomPoint_isClosed χ) _ (fun j => ?_) M
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hnd j), map_zero, map_zero]

/-- F1 from sum KV and the nondegenerate strict transform charts. -/
theorem mixedFujitaFreeness_of_kvSum_of_nondegenerateCharts
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hST : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      NondegenerateStrictTransformChartStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_coordinateHyperplaneQuotientRestriction hKV
    (fun K _ _ _ => coordinateHyperplaneQuotientRestriction_of_nondegenerateCharts (hST K))

end Charts

end MixedFujita
