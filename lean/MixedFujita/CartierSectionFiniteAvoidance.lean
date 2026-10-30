/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionSNC
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
A finite base-point-free system has a nonempty general parameter open whose cuts avoid any
specified finite set of scheme points. These points need not be closed or K-rational.
At a point, a K-linear functional on the stalk annihilating its maximal ideal detects one
unit coefficient. The resulting nonzero linear polynomial detects a nonvanishing section.
Multiplying the finitely many detectors handles all points simultaneously.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseSectionScalarTower

/-- A nonzero linear parameter polynomial forces nonvanishing at an arbitrary scheme point. -/
theorem cartierSections_point_nonvanishing_polynomial
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) (x : X) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        x ∉ cartierSectionZeroLocus D (∑ i, t i • s i) := by
  classical
  let f := Classical.choose (D.exists_isLocalEquationAt x)
  have hf := Classical.choose_spec (D.exists_isLocalEquationAt x)
  let c := (cartierLocalCoefficient D x f hf).restrictScalars K
  let W : Submodule K (X.presheaf.stalk x) :=
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).restrictScalars K
  obtain ⟨i, hi⟩ := hs x
  have hiW : c (s i) ∉ W := by
    change ¬ cartierLocalCoefficient D x f hf (s i) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)
    exact not_not.mpr hi
  obtain ⟨ℓ, hℓi, hℓW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hiW inferInstance
  have hkill : ∀ r ∈ W, ℓ r = 0 := by
    intro r hr
    apply (Submodule.mem_bot K).mp
    rw [← hℓW]
    exact Submodule.mem_map_of_mem hr
  let p : MvPolynomial ι K := ∑ j, MvPolynomial.C (ℓ (c (s j))) * MvPolynomial.X j
  have heval (t : ι → K) : MvPolynomial.aeval t p = ℓ (c (∑ j, t j • s j)) := by
    simp only [p, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, RingHom.id_apply, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hp : p ≠ 0 := by
    have hsingle : MvPolynomial.aeval (Pi.single i (1 : K)) p = ℓ (c (s i)) := by
      simp [p, Pi.single_apply]
    intro hp0
    apply hℓi
    rw [← hsingle, hp0, map_zero]
  refine ⟨p, hp, fun t ht => ?_⟩
  have hu : IsUnit (c (∑ j, t j • s j)) := by
    by_contra h
    apply ht
    rw [heval]
    exact hkill _ h
  have hx : x ∈ cartierSectionNonvanishingOpen D (∑ j, t j • s j) :=
    (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D _ x f hf).mpr hu
  exact not_not.mpr hx

/-- A product of linear detectors avoids finitely many arbitrary scheme points at once. -/
theorem cartierSections_finite_nonvanishing_polynomial
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) (Z : Set X) (hZ : Z.Finite) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∀ x ∈ Z, x ∉ cartierSectionZeroLocus D (∑ i, t i • s i) := by
  classical
  let : Fintype Z := hZ.fintype
  choose p hp hgood using fun x : Z =>
    cartierSections_point_nonvanishing_polynomial (K := K) D s hs x
  refine ⟨∏ x, p x, Finset.prod_ne_zero_iff.mpr (fun x hx => hp x), ?_⟩
  intro t ht x hx
  have hpx : MvPolynomial.aeval t (p ⟨x, hx⟩) ≠ 0 := by
    rw [map_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht ⟨x, hx⟩ (Finset.mem_univ _)
  exact hgood ⟨x, hx⟩ t hpx

/-- Over an infinite field the simultaneous point-avoidance parameter open is nonempty. -/
theorem cartierSections_general_finite_nonvanishing [Infinite K]
    (D : CartierDivisor X) {ι : Type*} [Fintype ι] (s : ι → Γ(D.sheaf, ⊤))
    (hs : CartierSectionsBasePointFree D s) (Z : Set X) (hZ : Z.Finite) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ (∃ t : ι → K, MvPolynomial.aeval t p ≠ 0) ∧
      ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
        ∀ x ∈ Z, x ∉ cartierSectionZeroLocus D (∑ i, t i • s i) := by
  obtain ⟨p, hp, hgood⟩ := cartierSections_finite_nonvanishing_polynomial (K := K) D s hs Z hZ
  refine ⟨p, hp, ?_, hgood⟩
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro t
  rw [map_zero]
  exact h t

end MixedFujita
