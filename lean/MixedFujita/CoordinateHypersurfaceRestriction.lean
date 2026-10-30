/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothRestrictionInduction

/-!
The restriction theorem for coordinate hyperplanes (step 9).

`CoordinateHypersurfaceRestriction` is the restriction theorem for smooth hypersurfaces in normal
form: A has global étale coordinates x_0, …, x_N (a formally étale K[X_0, …, X_N] → A) and the
surjection π : A → A' kills x_0, so Spec A' is (an open part of) the coordinate hyperplane x_0 = 0.
It implies the hypersurface case `SmoothRestrictionCodim K 1`
(`smoothRestrictionCodim_one_of_coordinate`): for a surjection of codimension one, a kernel element
t is the first of étale coordinates on a basic open A_b of the point (check-323), and the
restriction situation localizes to A_b → A'_{π b} (check-324). Hence F1 follows from sum KV and the
restriction theorem for coordinate hyperplanes
(`mixedFujitaFreeness_of_kvSum_of_coordinateHypersurfaceRestriction`).
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

section Coordinate

variable (K : Type u) [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- The restriction theorem for a coordinate hyperplane of global étale coordinates: for a smooth
K-domain A of relative dimension N + 1 with étale coordinates φ : K[X_0, …, X_N] → A and a
surjection π onto a smooth K-domain A' of relative dimension N ≥ 1 killing x_0 = φ X_0, a bad point
χ ∘ π of a family g on Spec A gives the bad point χ of π ∘ g on Spec A'. -/
def CoordinateHypersurfaceRestriction : Prop :=
  ∀ (A A' : Type u) [CommRing A] [IsDomain A] [Algebra K A] [CommRing A'] [IsDomain A']
    [Algebra K A'] (N : ℕ)
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension N (Spec (CommRingCat.of A') ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (cZ : EtaleChart K (Spec (CommRingCat.of A')) N)
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A), φ.toRingHom.FormallyEtale →
    ∀ π : A →ₐ[K] A', Function.Surjective π → π (φ (MvPolynomial.X 0)) = 0 →
    ∀ {J : Type} [Finite J] (g : J → A) (M : ℕ), 1 ≤ N → 1 ≤ M → ∀ χ : A' →ₐ[K] K,
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
          (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
        (specAlgHomPoint (χ.comp π))
        (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
      ModelThresholdBadAt cZ (1 : (Spec (CommRingCat.of A')).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cZ + principalCartierDivisor (Spec (CommRingCat.of A'))
          (1 : (Spec (CommRingCat.of A')).functionFieldˣ)))
        (specAlgHomPoint (χ))
        (fun j => (Spec (CommRingCat.of A')).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (π (g j)))) M

variable {K}

/-- The restriction theorem for smooth hypersurfaces from the case of coordinate hyperplanes. -/
theorem smoothRestrictionCodim_one_of_coordinate (hC : CoordinateHypersurfaceRestriction K) :
    SmoothRestrictionCodim K 1 := by
  classical
  intro A A' _ _ _ _ _ _ N _ _ cX cZ π hπ J _ g M hN hM χ hbad
  haveI : SmoothOfRelativeDimension (N + 0 + 1)
      (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    ‹SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))›
  obtain ⟨t, b, u, ht, hb, hφ⟩ := exists_away_etale_coordinates_through_kernel (N := N) (d := 0)
    π hπ χ
  have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
  have hπb0 : π b ≠ 0 := fun h0 => hb (by change χ (π b) = 0; rw [h0, map_zero])
  haveI : IsDomain (Localization.Away b) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hb0)
  haveI : IsDomain (Localization.Away (π b)) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hπb0)
  haveI := smoothOfRelativeDimension_spec_away (K := K) (n := N + 1) b
  haveI := smoothOfRelativeDimension_spec_away (K := K) (n := N) (π b)
  obtain ⟨cXb⟩ := nonempty_etaleChart_spec (K := K) (A := Localization.Away b) (n := N + 1)
  obtain ⟨cZb⟩ := nonempty_etaleChart_spec (K := K) (A := Localization.Away (π b)) (n := N)
  refine modelThresholdBad_restrict_of_away π χ b hb cX cZ cXb cZb g M ?_ hbad
  intro hbadb
  let πb := IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b
  have hπb : Function.Surjective πb := IsLocalization.Away.mapₐ_surjective_of_surjective b hπ
  let φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] Localization.Away b :=
    MvPolynomial.aeval (R := K) (fun l => algebraMap A (Localization.Away b)
      ((Fin.cons t u : Fin (N + 0 + 1) → A) l))
  have hφ0 : πb (φ (MvPolynomial.X 0)) = 0 := by
    change IsLocalization.Away.map (Localization.Away b) (Localization.Away (π b)) π.toRingHom b
      (φ (MvPolynomial.X 0)) = 0
    simp only [φ, MvPolynomial.aeval_X, Fin.cons_zero, IsLocalization.Away.map,
      IsLocalization.map_eq]
    change algebraMap A' (Localization.Away (π b)) (π t) = 0
    rw [ht, map_zero]
  exact hC (Localization.Away b) (Localization.Away (π b)) N cXb cZb φ hφ πb hπb hφ0
    (fun j => algebraMap A (Localization.Away b) (g j)) M hN hM (awayPoint χ (π b) hb) hbadb

/-- F1 from sum KV and the restriction theorem for coordinate hyperplanes. -/
theorem mixedFujitaFreeness_of_kvSum_of_coordinateHypersurfaceRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hC : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      CoordinateHypersurfaceRestriction K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_hypersurfaceRestriction hKV
    (fun _ _ _ _ => smoothRestrictionCodim_one_of_coordinate (hC _))

end Coordinate

end MixedFujita
