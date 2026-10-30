/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalLeadingJet
public import MixedFujita.LocalPointBlowupCoordinates

/-!
Exceptional leading-form restriction for every element of the actual local ring.
The chart is the actual algebra R[m/x_k], not a supplied polynomial model map.
The centre extension and coordinate substitution compatibility are derived, and
the strict-transform representative is unique because x_k is a nonzerodivisor.
The calculation also transports along arbitrary ring maps, including localization.
-/

@[expose] public section
open AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K R B : Type*} [Field K] [CommRing R] [Algebra K R] [IsLocalRing R]
  [CommRing B] {n : ℕ}

theorem localPointBlowup_germ_exceptional_restriction
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r)
    (k : Fin n) (s : R) (m : ℕ) (hs : (m : ℕ∞) ≤ (T s).order) :
    let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
    let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
    ∃! q : affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k)),
      algebraMap R _ s = τ (MvPolynomial.X k) ^ m * q ∧
        Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
          pointBlowupExceptionalEvaluation τ k
            (projectiveDehomogenize K k (homogeneousTaylorForm m (T s))) := by
  dsimp only
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
  obtain ⟨q, hq, hres⟩ := localLeadingJet_strictTransform_exceptional ψ T hX hord
    (algebraMap R _) τ k (localPointBlowupPolynomialMap_exceptionalIdeal _ ψ hψ k)
    (fun g => (localPointBlowupPolynomialMap_substitution _ ψ hψ k g).symm) s m hs
  refine ⟨q, ⟨hq, hres⟩, ?_⟩
  intro r hr
  exact localPointBlowupStrictTransform_unique _ ψ hψ k m s r q hr.1 hq

theorem localPointBlowup_germ_exceptional_restriction_afterMap
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r) (k : Fin n)
    (ν : affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k)) →+* B)
    (s : R) (m : ℕ) (hs : (m : ℕ∞) ≤ (T s).order) :
    let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
    let τ := ν.comp (localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k)
    ∃ q : B, ν (algebraMap R _ s) = τ (MvPolynomial.X k) ^ m * q ∧
      Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
        pointBlowupExceptionalEvaluation τ k
          (projectiveDehomogenize K k (homogeneousTaylorForm m (T s))) := by
  dsimp only
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let τ₀ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
  have hI : (IsLocalRing.maximalIdeal R).map (ν.comp (algebraMap R _)) =
      Ideal.span {(ν.comp τ₀) (MvPolynomial.X k)} := by
    rw [← Ideal.map_map, localPointBlowupPolynomialMap_exceptionalIdeal _ ψ hψ k,
      Ideal.map_span, Set.image_singleton]
    rfl
  exact localLeadingJet_strictTransform_exceptional ψ T hX hord
    (ν.comp (algebraMap R _)) (ν.comp τ₀) k hI
    (fun g => congrArg ν (localPointBlowupPolynomialMap_substitution _ ψ hψ k g).symm) s m hs

end MixedFujita
