/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionSNC
public import MixedFujita.EffectiveCartierIdealSheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
Supply a nonzero general section along with the SNC charts. Avoiding one additional linear
polynomial excludes the kernel of the section map. Its actual effective Cartier divisor and
closed zero subscheme are then available without assuming that a general section is nonzero.
The identification of the ideal sheaf of this subscheme with the chart coefficient ideals is a
separate geometric bridge; the SNC conclusion below refers to the intrinsic zero locus of the
section, not yet to that subscheme's ideal sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The global ideal sheaf of the zero scheme of a nonzero Cartier section. -/
noncomputable def cartierSectionZeroIdeal (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : X.IdealSheafData :=
  effectiveCartierIdealSheaf (cartierSectionZeroDivisor D s hs)
    (cartierSectionZeroDivisor_isEffective D s hs)

/-- The actual global closed zero subscheme, constructed from the effective Cartier divisor. -/
noncomputable def cartierSectionZeroScheme (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : Scheme.{u} :=
  (cartierSectionZeroIdeal D s hs).subscheme

/-- Its closed immersion into X. -/
noncomputable def cartierSectionZeroSchemeι (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : cartierSectionZeroScheme D s hs ⟶ X :=
  (cartierSectionZeroIdeal D s hs).subschemeι

theorem cartierSectionZeroSchemeι_isClosedImmersion (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) : IsClosedImmersion (cartierSectionZeroSchemeι D s hs) := by
  unfold cartierSectionZeroSchemeι
  infer_instance

/-- The zero ideal has the invertible presentation of an effective Cartier divisor. -/
noncomputable def cartierSectionZeroIdealPresentation (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0) :
    InvertibleIdealPresentation (cartierSectionZeroIdeal D s hs) :=
  effectiveCartierIdealPresentation (cartierSectionZeroDivisor D s hs)
    (cartierSectionZeroDivisor_isEffective D s hs)

/-- A base-point-free family has a nonzero section map. -/
theorem cartierSections_linearCombination_ne_zero (D : CartierDivisor X) {ι : Type*}
    [Fintype ι] (s : ι → Γ(D.sheaf, ⊤)) (hs : CartierSectionsBasePointFree D s) :
    Fintype.linearCombination K s ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := hs (genericPoint X)
  intro h0
  have hz := LinearMap.congr_fun h0 (Pi.single i 1)
  rw [Fintype.linearCombination_apply_single, one_smul, LinearMap.zero_apply] at hz
  rw [hz, map_zero] at hi
  exact not_isUnit_zero hi

/-- A nonzero general member is in SNC position with the given family and defines an actual
effective Cartier divisor and a global closed subscheme. -/
theorem cartierSections_general_nonzero_sncFamilyWith_zeroLocus [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] [CompactSpace X]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) {r : ℕ} (ξ : Fin r → X) (hξ : IsSNCFamily K n ξ) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        (∑ i, t i • s i) ≠ 0 ∧
        IsSNCFamilyWith K n ξ (cartierSectionZeroLocus D (∑ i, t i • s i)) := by
  classical
  obtain ⟨p, hp, _, hsnc⟩ := cartierSections_general_sncFamilyWith_zeroLocus D s hs ξ hξ
  obtain ⟨ℓ, hℓ, hnonzero⟩ := exists_mvPolynomial_ne_zero_of_linearMap_ne_zero
    (Fintype.linearCombination K s) (cartierSections_linearCombination_ne_zero D s hs)
  refine ⟨p * ℓ, mul_ne_zero hp hℓ, ?_, fun t ht => ?_⟩
  · by_contra h
    push Not at h
    apply mul_ne_zero hp hℓ
    apply MvPolynomial.funext
    intro t
    rw [map_zero]
    exact h t
  · rw [map_mul] at ht
    exact ⟨hnonzero t (right_ne_zero_of_mul ht), hsnc t (left_ne_zero_of_mul ht)⟩

end MixedFujita
