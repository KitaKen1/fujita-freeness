/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ReducedCartierSectionCoefficients

/-!
General Cartier cuts in SNC position have actual prime components of multiplicity one.
The coefficient formula at every codimension-one point is the indicator of the enumerated
component generic points. Thus denominator-cleared Cartier perturbations have explicit
coefficients, including unchanged coefficients outside the new prime-component family.
The geometric klt inequality on all birational models, resolution and pointed cuts remain
separate inputs; the statements here concern actual Cartier divisors on the ambient scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- Smooth schemes over a field are reduced, by their domain stalks. -/
theorem smoothScheme_isReduced {K : Type u} [Field K] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) [Smooth g] : IsReduced Y := by
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := fun y => by
    have := smoothScheme_stalk_isDomain g y
    infer_instance
  exact isReduced_of_isReduced_stalk Y

/-- Distinct codimension-one points cannot specialize to each other. -/
theorem scheme_codimensionOne_mem_closure_iff_eq {X : Scheme.{u}} (x y : X)
    (hx : Order.coheight x = 1) (hy : Order.coheight y = 1) :
    x ∈ closure ({y} : Set X) ↔ x = y := by
  constructor
  · intro h
    have hxy : x ≤ y := Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr h)
    by_contra hne
    have hstrict : x < y := lt_iff_le_not_ge.mpr ⟨hxy, fun hyx =>
      hne ((Scheme.le_iff_specializes.mp hyx).antisymm (Scheme.le_iff_specializes.mp hxy)).eq⟩
    have hlt := Order.coheight_strictAnti hstrict (by simp [hy])
    rw [hx, hy] at hlt
    exact (lt_irrefl _ hlt)
  · rintro rfl
    exact subset_closure rfl

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- The actual zero Cartier divisor has coefficient zero away from the zero locus. -/
theorem cartierSectionZeroDivisor_coefficient_zero_of_notMem
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (x : CodimensionOnePoint X) (hx : (x : X) ∉ cartierSectionZeroLocus D s) :
    cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) = 0 := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (x : X)
  have hu : IsUnit (cartierLocalCoefficient D (x : X) f hf s) := by
    apply (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (x : X) f hf).mp
    exact not_not.mp hx
  obtain ⟨r, hr, hrimage, heq, hrorder⟩ :=
    cartierSectionZeroDivisor_regular_localEquation D (x : X) f hf s hs
  have hre : r = cartierLocalCoefficient D (x : X) f hf s := by
    apply IsFractionRing.injective (X.presheaf.stalk (x : X)) X.functionField
    rw [hrimage, cartierLocalCoefficient_image]
    simp only [Units.val_mul, cartierSectionUnit_val]
  rw [cartierCoefficient_eq_ord heq, ← hrimage]
  have hne : algebraMap (X.presheaf.stalk (x : X)) X.functionField r ≠ 0 :=
    fun h => hr (IsFractionRing.injective _ _ (h.trans (map_zero _).symm))
  rw [X.ord_eq_iff x.property hne]
  have : Ring.KrullDimLE 1 (X.presheaf.stalk (x : X)) :=
    krullDimLE_of_coheight_le x.property.le
  change Ring.ordFrac (X.presheaf.stalk (x : X))
    (algebraMap (X.presheaf.stalk (x : X)) X.functionField r) = _
  exact Ring.ordFrac_of_isUnit (hre.symm ▸ hu)

variable {K : Type u} [Field K] [X.Over (Spec (CommRingCat.of K))]

include K in
/-- A reduced cut with an enumerated prime cover has the exact coefficient indicator formula. -/
theorem cartierSectionZeroDivisor_coefficient_eq_indicator
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    [IsReduced (cartierSectionZeroScheme D s hs)] {q : ℕ} (η : Fin q → X)
    (hη : ∀ j, Order.coheight (η j) = 1)
    (hcover : cartierSectionZeroLocus D s = ⋃ j, closure ({η j} : Set X))
    (x : CodimensionOnePoint X) [IsDiscreteValuationRing (X.presheaf.stalk (x : X))] :
    cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
      if (x : X) ∈ Set.range η then 1 else 0 := by
  classical
  have hmem : (x : X) ∈ cartierSectionZeroLocus D s ↔ (x : X) ∈ Set.range η := by
    rw [hcover]
    simp only [Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, ((scheme_codimensionOne_mem_closure_iff_eq _ _ x.property (hη j)).mp hj).symm⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, hj ▸ subset_closure rfl⟩
  by_cases hx : (x : X) ∈ Set.range η
  · rw [ite_eq_left hx]
    exact cartierSectionZeroDivisor_coefficient_one_of_reduced (K := K) D s hs x
      (hmem.mpr hx)
  · rw [ite_eq_right hx]
    exact cartierSectionZeroDivisor_coefficient_zero_of_notMem D s hs x (hmem.not.mpr hx)

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- A general nonzero cut supplies a reduced prime SNC divisor with coefficients known at every
codimension-one point. No component multiplicity or ambient DVR assumption is supplied. -/
theorem cartierSections_general_reduced_prime_snc [CharZero K] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {n r : ℕ} (ξ : Fin r → X)
    (hξ : IsSNCFamily K n ξ) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∃ (hst : (∑ i, t i • s i) ≠ 0) (q : ℕ) (η : Fin q → X),
          Smooth (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
            (X ↘ Spec (CommRingCat.of K))) ∧ Function.Injective η ∧
          (∀ j, Order.coheight (η j) = 1) ∧
          Set.range η = (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst) ''
            genericPoints (cartierSectionZeroScheme D (∑ i, t i • s i) hst) ∧
          cartierSectionZeroLocus D (∑ i, t i • s i) = ⋃ j, closure ({η j} : Set X) ∧
          (Pairwise fun i j => Disjoint (closure ({η i} : Set X))
            (closure ({η j} : Set X))) ∧ IsSNCFamily K n (Fin.append ξ η) ∧
          (∀ x : CodimensionOnePoint X,
            cartierCoefficient (cartierSectionZeroDivisor D (∑ i, t i • s i) hst) (x : X) =
              if (x : X) ∈ Set.range η then 1 else 0) := by
  classical
  obtain ⟨p, hp, hpex, hgood⟩ := cartierSections_general_nonzero_smooth_prime_snc D s hs ξ hξ
  refine ⟨p, hp, hpex, fun t ht => ?_⟩
  obtain ⟨hst, q, η, hsm, hinj, hη, hrange, hcover, hdis, hsnc⟩ := hgood t ht
  refine ⟨hst, q, η, hsm, hinj, hη, hrange, hcover, hdis, hsnc, ?_⟩
  intro x
  have := hsm
  have : IsReduced (cartierSectionZeroScheme D (∑ i, t i • s i) hst) :=
    smoothScheme_isReduced (cartierSectionZeroSchemeι D (∑ i, t i • s i) hst ≫
      (X ↘ Spec (CommRingCat.of K)))
  have := isSNCFamily_stalk_regular hξ (x : X)
  have := CodimensionOnePoint.isDiscreteValuationRing_stalk x
  exact cartierSectionZeroDivisor_coefficient_eq_indicator (K := K) D _ hst η hη hcover x

/-- Denominator-cleared perturbations add exactly k at the new prime components and leave
every other prime coefficient unchanged apart from the chosen denominator multiplier. -/
theorem cartierSection_perturbation_coefficient_formula
    (B D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    {q : ℕ} (η : Fin q → X)
    (hcoeff : ∀ x : CodimensionOnePoint X,
      cartierCoefficient (cartierSectionZeroDivisor D s hs) (x : X) =
        if (x : X) ∈ Set.range η then 1 else 0)
    (a k : ℕ) (x : CodimensionOnePoint X) :
    cartierCoefficient (a • B + k • cartierSectionZeroDivisor D s hs) (x : X) =
      (a : ℤ) * cartierCoefficient B (x : X) +
        if (x : X) ∈ Set.range η then (k : ℤ) else 0 := by
  classical
  rw [cartierCoefficient_add, cartierCoefficient_nsmul, cartierCoefficient_nsmul, hcoeff]
  split_ifs <;> ring

end MixedFujita
