/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HyperplaneLocalValuation

/-!
The restriction theorem for coordinate hyperplanes, with the hyperplane as a quotient (step 9).

`CoordinateHyperplaneQuotientRestriction` is `CoordinateHypersurfaceRestriction` for A' = A/(x_0)
itself, assumed to be a smooth domain: this is the target of the strict transform model (checks
328–330). It implies the general case (`coordinateHypersurfaceRestriction_of_quotient`): for a
surjection π : A → A' killing x_0 and a K-point of A', the hyperplane A/(x_0) has the étale
coordinates x_1, …, x_N (check-320), so near the point some localization (A/(x_0))_c is a smooth
domain (check-321). Lifting c to b, the quotient A_b/(x_0) is a localization of A/(x_0) away from
c (Mathlib's localization of quotients), hence a smooth domain; the quotient case for A_b gives the
bad point on A_b/(x_0), the surjection A_b/(x_0) → A'_{π b} of smooth domains of the same
dimension transfers it (check-322), and the restriction situation localizes (check-324). Hence F1
follows from sum KV and the quotient case
(`mixedFujitaFreeness_of_kvSum_of_coordinateHyperplaneQuotientRestriction`).
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

section Quotient

variable (K : Type u) [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- The restriction theorem for the coordinate hyperplane x_0 = 0 of global étale coordinates,
with the hyperplane the quotient A/(x_0), assumed to be a smooth domain of relative dimension
N ≥ 1. -/
def CoordinateHyperplaneQuotientRestriction : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [Algebra K A] (N : ℕ)
    [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A), φ.toRingHom.FormallyEtale →
    ∀ [IsDomain (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})]
      [SmoothOfRelativeDimension N (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))
        ↘ Spec (CommRingCat.of K))]
      (cZ : EtaleChart K (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))) N)
      {J : Type} [Finite J] (g : J → A) (M : ℕ), 1 ≤ N → 1 ≤ M →
      ∀ χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K,
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
          (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
        (specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))))
        (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
      ModelThresholdBadAt cZ
        (1 : (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cZ + principalCartierDivisor
          (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)})))
          (1 : (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).functionFieldˣ)))
        (specAlgHomPoint χ)
        (fun j => (Spec (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).germToFunctionField
          ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}))).inv
            (Ideal.Quotient.mk _ (g j)))) M

variable {K}

/-- A quotient of a localization by an extended ideal is a domain when the localization of the
quotient is. -/
theorem isDomain_away_quotient {R : Type u} [CommRing R] (I : Ideal R) (b : R)
    [IsDomain (Localization.Away (Ideal.Quotient.mk I b))] :
    IsDomain (Localization.Away b ⧸ I.map (algebraMap R (Localization.Away b))) := by
  have h : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers b))
      (Localization.Away b ⧸ I.map (algebraMap R (Localization.Away b))) := inferInstance
  have hsub : Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers b) =
      Submonoid.powers (Ideal.Quotient.mk I b) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    rfl
  rw [hsub] at h
  exact MulEquiv.isDomain (Localization.Away (Ideal.Quotient.mk I b))
    (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I b))
      (Localization.Away (Ideal.Quotient.mk I b))
      (Localization.Away b ⧸ I.map (algebraMap R (Localization.Away b)))).symm.toRingEquiv.toMulEquiv

/-- The restriction theorem for coordinate hyperplanes from the case where the hyperplane is the
quotient A/(x_0). -/
theorem coordinateHypersurfaceRestriction_of_quotient
    (hQ : CoordinateHyperplaneQuotientRestriction K) : CoordinateHypersurfaceRestriction K := by
  classical
  intro A A' _ _ _ _ _ _ N _ _ cX cZ φ hφ π hπ hx₀ J _ g M hN hM χ hbad
  -- the hyperplane and the induced surjection
  have hI : ∀ a ∈ Ideal.span {φ (MvPolynomial.X 0)}, π a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx₀, mul_zero]
  let πbar : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] A' :=
    Ideal.Quotient.liftₐ (Ideal.span {φ (MvPolynomial.X 0)}) π hI
  -- a smooth domain neighbourhood of the point on the hyperplane
  haveI : Algebra.Smooth K A := algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := N + 1)
  haveI : Algebra.FinitePresentation K (A ⧸ Ideal.span {φ (MvPolynomial.X 0)}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  obtain ⟨c, hc, hdomc, -⟩ := exists_away_isDomain_smoothOfRelativeDimension (K := K)
    (C := A ⧸ Ideal.span {φ (MvPolynomial.X 0)}) (hyperplaneCoords φ)
    (hyperplaneCoords_formallyEtale φ hφ) (χ.comp πbar)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  have hb : χ (π b) ≠ 0 := hc
  have hb0 : b ≠ 0 := fun h0 => hb (by rw [h0, map_zero, map_zero])
  have hπb0 : π b ≠ 0 := fun h0 => hb (by rw [h0, map_zero])
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
  -- coordinates on A_b and its hyperplane
  let φ₁ : MvPolynomial (Fin (N + 1)) K →ₐ[K] Localization.Away b :=
    (IsScalarTower.toAlgHom K A (Localization.Away b)).comp φ
  have hloc : (IsScalarTower.toAlgHom K A (Localization.Away b)).toRingHom.FormallyEtale := by
    change (algebraMap A (Localization.Away b)).FormallyEtale
    exact RingHom.formallyEtale_algebraMap.mpr
      (Algebra.FormallyEtale.of_isLocalization (Submonoid.powers b))
  have hφ₁ : φ₁.toRingHom.FormallyEtale := RingHom.FormallyEtale.comp hφ hloc
  have hI₁ : Ideal.span {φ₁ (MvPolynomial.X 0)} =
      (Ideal.span {φ (MvPolynomial.X 0)}).map (algebraMap A (Localization.Away b)) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  haveI : IsDomain (Localization.Away
      (Ideal.Quotient.mk (Ideal.span {φ (MvPolynomial.X 0)}) b)) := hdomc
  haveI : IsDomain (Localization.Away b ⧸
      (Ideal.span {φ (MvPolynomial.X 0)}).map (algebraMap A (Localization.Away b))) :=
    isDomain_away_quotient _ b
  haveI : IsDomain (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) :=
    MulEquiv.isDomain (Localization.Away b ⧸
      (Ideal.span {φ (MvPolynomial.X 0)}).map (algebraMap A (Localization.Away b)))
      (Ideal.quotEquivOfEq hI₁).toMulEquiv
  -- the hyperplane of A_b is smooth of relative dimension N
  haveI : Algebra.Smooth K (Localization.Away b) :=
    algebraSmooth_of_smoothOfRelativeDimension (K := K) (n := N + 1)
  haveI : Algebra.FinitePresentation K (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  have hv₁ := hyperplaneCoords_formallyEtale φ₁ hφ₁
  haveI : Algebra.FormallySmooth K (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) := by
    letI := (hyperplaneCoords φ₁).toRingHom.toAlgebra
    haveI : Algebra.FormallyEtale (MvPolynomial (Fin N) K)
        (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) := hv₁
    haveI : IsScalarTower K (MvPolynomial (Fin N) K)
        (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) :=
      IsScalarTower.of_algebraMap_eq fun k => ((hyperplaneCoords φ₁).commutes k).symm
    exact Algebra.FormallySmooth.comp K (MvPolynomial (Fin N) K) _
  haveI : Algebra.Smooth K (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) :=
    ⟨inferInstance, inferInstance⟩
  haveI hsm₁ := specAlgebraOver_smoothOfRelativeDimension (K := K)
    (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) (hyperplaneCoords φ₁) hv₁
  obtain ⟨cZ₁⟩ := nonempty_etaleChart_spec (K := K)
    (A := Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)}) (n := N)
  -- the induced surjection of the hyperplane of A_b onto A'_{π b}
  let πb := IsLocalization.Away.mapₐ (Localization.Away b) (Localization.Away (π b)) π b
  have hπbx : πb (φ₁ (MvPolynomial.X 0)) = 0 := by
    change IsLocalization.Away.map (Localization.Away b) (Localization.Away (π b)) π.toRingHom b
      (algebraMap A (Localization.Away b) (φ (MvPolynomial.X 0))) = 0
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
    change algebraMap A' (Localization.Away (π b)) (π (φ (MvPolynomial.X 0))) = 0
    rw [hx₀, map_zero]
  have hI₁π : ∀ a ∈ Ideal.span {φ₁ (MvPolynomial.X 0)}, πb a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hπbx, mul_zero]
  let π₁ : Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)} →ₐ[K] Localization.Away (π b) :=
    Ideal.Quotient.liftₐ _ πb hI₁π
  have hπbs : Function.Surjective πb := IsLocalization.Away.mapₐ_surjective_of_surjective b hπ
  have hπ₁s : Function.Surjective π₁ := by
    intro z
    obtain ⟨a, rfl⟩ := hπbs z
    exact ⟨Ideal.Quotient.mk _ a, rfl⟩
  let χ' := awayPoint χ (π b) hb
  -- the quotient case on A_b
  have hpt : (χ'.comp π₁).comp (Ideal.Quotient.mkₐ K (Ideal.span {φ₁ (MvPolynomial.X 0)})) =
      χ'.comp πb := AlgHom.ext fun a => rfl
  have hQb := hQ (Localization.Away b) N cXb φ₁ hφ₁ cZ₁
    (fun j => algebraMap A (Localization.Away b) (g j)) M hN hM (χ'.comp π₁) (by rw [hpt]; exact hbadb)
  -- transfer along the surjection of smooth domains of the same dimension
  haveI : SmoothOfRelativeDimension (N + 0)
      (Spec (CommRingCat.of (Localization.Away b ⧸ Ideal.span {φ₁ (MvPolynomial.X 0)})) ↘
        Spec (CommRingCat.of K)) := hsm₁
  exact smoothRestriction_codim_zero (K := K) (N := N) cZ₁ cZb π₁ hπ₁s
    (fun j => Ideal.Quotient.mk _ (algebraMap A (Localization.Away b) (g j))) M χ' hQb

/-- F1 from sum KV and the restriction theorem for the coordinate hyperplane as a quotient. -/
theorem mixedFujitaFreeness_of_kvSum_of_coordinateHyperplaneQuotientRestriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hQ : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      CoordinateHyperplaneQuotientRestriction K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_coordinateHypersurfaceRestriction hKV
    (fun K _ _ _ => coordinateHypersurfaceRestriction_of_quotient (hQ K))

end Quotient

end MixedFujita
