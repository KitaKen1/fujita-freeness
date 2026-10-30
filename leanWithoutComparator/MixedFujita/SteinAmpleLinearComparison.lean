/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinCartierLinearReflection
public import MixedFujita.LinearEffectiveFreenessReduction

/-!
The ample condition on the eventual descent of D itself follows from the already constructed
ample descent of qD. Positive multiples reflect the actual projective Cartier ample predicate.
If D ~ g*A and qD ~ g*H along the same surjective Stein-type map, reflection of actual linear
equivalence proves qA ~ H, and ampleness of H therefore proves ampleness of A. No supplied
principal relation downstairs or extra ample hypothesis on A is needed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The projective Cartier ample predicate is reflected by a positive multiple. -/
theorem cartierIsAmpleProj_of_positive_nsmul {A : CartierDivisor Y} {q : ℕ}
    (hq : 0 < q) (hA : CartierIsAmpleProj K (q • A)) : CartierIsAmpleProj K A := by
  obtain ⟨m, hm, n, e, he, hbase, F, hF, hFgen, φ, hdiv⟩ := hA
  refine ⟨m * q, by nlinarith, n, e, he, hbase, F, hF, hFgen, φ, ?_⟩
  rw [mul_nsmul', hdiv]

/-- Positive multiples are equivalent for actual projective Cartier ampleness. -/
theorem cartierIsAmpleProj_positive_nsmul_iff {A : CartierDivisor Y} {q : ℕ} (hq : 0 < q) :
    CartierIsAmpleProj K (q • A) ↔ CartierIsAmpleProj K A :=
  ⟨cartierIsAmpleProj_of_positive_nsmul hq, fun h => cartierIsAmpleProj_nsmul h hq⟩

/-- Once D itself descends to the same Stein target as qD, its descended divisor is ample
by the already proved ample descent of qD. -/
theorem stein_descended_divisor_isAmple_of_ample_multiple
    {X : Scheme.{u}} [IsIntegral X] (g : X ⟶ Y) [IsDominant g]
    (happ : ∀ U : Y.Opens, Function.Surjective (g.app U).hom)
    (hsurj : Function.Surjective g) (D : CartierDivisor X) (A H : CartierDivisor Y)
    {q : ℕ} (hq : 0 < q) (φ ψ : X.functionFieldˣ)
    (hD : D = cartierPullback g A + principalCartierDivisor X ψ)
    (hqD : q • D = cartierPullback g H + principalCartierDivisor X φ)
    (hH : CartierIsAmpleProj K H) : CartierIsAmpleProj K A := by
  have hscale : cartierPullback g (q • A) + principalCartierDivisor X (ψ ^ q) =
      cartierPullback g H + principalCartierDivisor X φ := by
    rw [← hqD, hD, nsmul_add, ← cartierPullback_nsmul, ← principalCartierDivisor_power]
  have hcomp : cartierPullback g (q • A) = cartierPullback g H +
      principalCartierDivisor X (φ * (ψ ^ q)⁻¹) := by
    calc
      _ = (cartierPullback g (q • A) + principalCartierDivisor X (ψ ^ q)) -
          principalCartierDivisor X (ψ ^ q) := by abel
      _ = (cartierPullback g H + principalCartierDivisor X φ) -
          principalCartierDivisor X (ψ ^ q) := congrArg (fun E => E - _) hscale
      _ = _ := by rw [principalCartierDivisor_mul, principalCartierDivisor_inv]; abel
  obtain ⟨ζ, hζ, hmap⟩ := stein_cartier_linear_equivalence_reflection g happ hsurj (q • A) H _ hcomp
  apply cartierIsAmpleProj_of_positive_nsmul hq
  rw [hζ]
  exact cartierIsAmpleProj_add_principal hH ζ

end MixedFujita
