/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineFormalTestValuation
public import MixedFujita.ValuationSubringCenter
public import MixedFujita.BirationalLocalExtension

/-!
The centre of a formal test on a proper birational model of affine space. The formal test ψ at
p defines a valuation of the function field of affine space, nonnegative on polynomials; through
the birational identification it is a valuation of the function field of a proper birational
model T, and its valuation ring forms a valuative square with the generic point of T. The
valuative criterion gives a centre t₀: the local ring at t₀ has valuation at most one, its units
valuation one and its maximal ideal valuation less than one, and the image of t₀ in affine space
specializes to the point p, since a polynomial not vanishing at p has valuation one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPowerSeries WithZero

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [CharZero K] {m : ℕ}

/-- Affine space over K as a scheme. -/
@[reducible]
noncomputable def affineSpace (K : Type u) [Field K] (m : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (MvPolynomial (Fin m) K))

/-- The formal test at p as a map of the function field of affine space. -/
noncomputable def affineFormalTestFieldMap
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (hJ : (powerSeriesJacobian ψ).det ≠ 0) (p : Fin m → K) :
    (affineSpace K m).functionField →+* FractionRing (MvPowerSeries (Fin m) K) :=
  letI := instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (MvPolynomial (Fin m) K))
  haveI := functionField_isFractionRing_of_affine (CommRingCat.of (MvPolynomial (Fin m) K))
  IsFractionRing.lift (A := CommRingCat.of (MvPolynomial (Fin m) K))
    (g := (algebraMap (MvPowerSeries (Fin m) K) (FractionRing (MvPowerSeries (Fin m) K))).comp
      (shiftedFormalTestMap ψ p).toRingHom)
    ((IsFractionRing.injective (MvPowerSeries (Fin m) K) _).comp
      (shiftedFormalTestMap_injective ψ hJ p))

theorem affineFormalTestFieldMap_coords
    (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
    (hJ : (powerSeriesJacobian ψ).det ≠ 0) (p : Fin m → K) (P : MvPolynomial (Fin m) K) :
    affineFormalTestFieldMap ψ hJ p
        (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P) =
      algebraMap _ (FractionRing (MvPowerSeries (Fin m) K)) (shiftedFormalTestMap ψ p P) := by
  let := instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (MvPolynomial (Fin m) K))
  have := functionField_isFractionRing_of_affine (CommRingCat.of (MvPolynomial (Fin m) K))
  rw [affineSpaceEtaleChart_functionFieldCoords]
  exact IsFractionRing.lift_algebraMap _ _

/-- An element of a valuation subring of valuation one is a unit of the subring. -/
theorem valuationSubring_isUnit_of_valuation_eq_one {F : Type*} [Field F] {v : Valuation F ℤᵐ⁰}
    (x : v.valuationSubring) (hx : v (x : F) = 1) : IsUnit x := by
  have hx0 : (x : F) ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have hinv : (x : F)⁻¹ ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, map_inv₀, hx, inv_one]
  exact ⟨⟨x, ⟨(x : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩,
    rfl⟩

section Center

variable {T : Scheme.{u}} [IsIntegral T] (ρ : T ⟶ affineSpace K m) [IsDominant ρ]
  (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
  (ψ : MvPowerSeries (Fin m) K →ₐ[K] MvPowerSeries (Fin m) K)
  (hJ : (powerSeriesJacobian ψ).det ≠ 0) (p : Fin m → K)

/-- The formal test as a map of the function field of the model. -/
noncomputable def formalTestModelFieldMap :
    T.functionField →+* FractionRing (MvPowerSeries (Fin m) K) :=
  (affineFormalTestFieldMap ψ hJ p).comp
    (RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm.toRingHom

theorem formalTestModelFieldMap_pullback (f : (affineSpace K m).functionField) :
    formalTestModelFieldMap ρ hρ ψ hJ p ((dominantFunctionFieldMap ρ).hom f) =
      affineFormalTestFieldMap ψ hJ p f := by
  unfold formalTestModelFieldMap
  rw [RingHom.comp_apply]
  congr 1
  exact (RingEquiv.ofBijective (dominantFunctionFieldMap ρ).hom hρ).symm_apply_apply f

/-- The valuation of the formal test on the function field of the model. -/
noncomputable def formalTestModelValuation (w : Fin m → ℕ) : Valuation T.functionField ℤᵐ⁰ :=
  (weightedFieldValuation w).comap (formalTestModelFieldMap ρ hρ ψ hJ p)

theorem formalTestModelValuation_pullback_coords (w : Fin m → ℕ) (P : MvPolynomial (Fin m) K) :
    formalTestModelValuation ρ hρ ψ hJ p w ((dominantFunctionFieldMap ρ).hom
        (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P)) =
      weightedValuation w (shiftedFormalTestMap ψ p P) := by
  unfold formalTestModelValuation
  rw [Valuation.comap_apply, formalTestModelFieldMap_pullback, affineFormalTestFieldMap_coords,
    weightedFieldValuation_algebraMap]

/-- The centre of the formal test on a proper birational model of affine space. -/
theorem exists_formalTest_center [IsProper ρ] (w : Fin m → ℕ) :
    ∃ t₀ : T, affineSpacePoint K m p ∈ closure ({ρ t₀} : Set (affineSpace K m)) ∧
      (∀ g : T.presheaf.stalk t₀, formalTestModelValuation ρ hρ ψ hJ p w
          (algebraMap (T.presheaf.stalk t₀) T.functionField g) ≤ 1) ∧
      (∀ g : T.presheaf.stalk t₀, g ∈ IsLocalRing.maximalIdeal (T.presheaf.stalk t₀) →
        formalTestModelValuation ρ hρ ψ hJ p w
          (algebraMap (T.presheaf.stalk t₀) T.functionField g) < 1) := by
  set v := formalTestModelValuation ρ hρ ψ hJ p w
  set R := v.valuationSubring
  have hle : ∀ P : MvPolynomial (Fin m) K, v ((dominantFunctionFieldMap ρ).hom
      (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P)) ≤ 1 := fun P => by
    rw [formalTestModelValuation_pullback_coords]
    exact weightedValuation_le_one w _
  let lam : MvPolynomial (Fin m) K →+* R :=
    { toFun := fun P => ⟨(dominantFunctionFieldMap ρ).hom
        (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P), hle P⟩
      map_one' := by ext; simp only [map_one, OneMemClass.coe_one]
      map_mul' := fun P Q => by ext; simp only [map_mul, MulMemClass.coe_mul]
      map_zero' := by ext; simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := fun P Q => by ext; simp only [map_add, AddMemClass.coe_add] }
  let i₂ : Spec (CommRingCat.of R) ⟶ affineSpace K m := Spec.map (CommRingCat.ofHom lam)
  have hsq : T.fromSpecStalk (genericPoint T) ≫ ρ =
      Spec.map (CommRingCat.ofHom (algebraMap R T.functionField)) ≫ i₂ := by
    rw [← dominantFunctionFieldMap_fromSpecStalk ρ, Spec.fromSpecStalk_eq', ← Spec.map_comp,
      ← Spec.map_comp]
    congr 1
  obtain ⟨t₀, φ₀, hloc, hρt, hcompat⟩ := exists_center_of_valuationSubring ρ R i₂ hsq
  have hmemR : ∀ g, v (algebraMap (T.presheaf.stalk t₀) T.functionField g) ≤ 1 := fun g => by
    rw [← hcompat g]
    exact (φ₀ g).2
  refine ⟨t₀, ?_, hmemR, ?_⟩
  · rw [← specializes_iff_mem_closure, hρt]
    change PrimeSpectrum.comap lam (IsLocalRing.closedPoint R) ⤳ affineSpacePoint K m p
    rw [← PrimeSpectrum.le_iff_specializes]
    intro P hP
    rw [affineSpacePoint_mem_iff]
    by_contra hPp
    apply (IsLocalRing.mem_maximalIdeal _).mp hP
    have h1 : v ((lam P : R) : T.functionField) = 1 := by
      change v ((dominantFunctionFieldMap ρ).hom
        (etaleChartFunctionFieldCoords (affineSpaceEtaleChart K m) P)) = 1
      rw [formalTestModelValuation_pullback_coords]
      exact weightedValuation_shiftedFormalTestMap_eq_one ψ p w hPp
    exact valuationSubring_isUnit_of_valuation_eq_one (lam P) h1
  · intro g hg
    rcases lt_or_eq_of_le (hmemR g) with h | h
    · exact h
    · exfalso
      apply (IsLocalRing.mem_maximalIdeal _).mp hg
      have hu : IsUnit (φ₀ g) := by
        apply valuationSubring_isUnit_of_valuation_eq_one
        change v (algebraMap R T.functionField (φ₀ g)) = 1
        rw [hcompat g]
        exact h
      exact isUnit_of_map_unit φ₀.hom g hu

end Center

end MixedFujita
