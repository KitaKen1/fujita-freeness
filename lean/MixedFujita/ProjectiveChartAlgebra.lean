/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialProjectiveCharts
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
Dehomogenization into the polynomial ring on the coordinates other than k.
It commutes with scalar evaluation. A ring map from the actual degree-zero
homogeneous localization sends f/X_k^d to that dehomogenization. Its inverse
and ring equivalence are proved in ProjectiveChartEquiv.
-/

@[expose] public section

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ}

noncomputable def projectiveChartVariable (R : Type*) [CommRing R] (k i : Fin n) :
    MvPolynomial {j : Fin n // j ≠ k} R :=
  if h : i = k then 1 else MvPolynomial.X ⟨i, h⟩

noncomputable def projectiveDehomogenize (R : Type*) [CommRing R] (k : Fin n) :
    MvPolynomial (Fin n) R →+* MvPolynomial {j : Fin n // j ≠ k} R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (projectiveChartVariable R k)

theorem projectiveDehomogenize_C (R : Type*) [CommRing R] (k : Fin n) (r : R) :
    projectiveDehomogenize R k (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [projectiveDehomogenize]

theorem projectiveDehomogenize_X_self (R : Type*) [CommRing R] (k : Fin n) :
    projectiveDehomogenize R k (MvPolynomial.X k) = 1 := by
  simp [projectiveDehomogenize, projectiveChartVariable]

theorem projectiveDehomogenize_X_other (R : Type*) [CommRing R] (k : Fin n)
    (i : {j : Fin n // j ≠ k}) :
    projectiveDehomogenize R k (MvPolynomial.X i.val) = MvPolynomial.X i := by
  simp [projectiveDehomogenize, projectiveChartVariable, i.property]

theorem projectiveDehomogenize_monomial (R : Type*) [CommRing R] (k : Fin n)
    (p : Fin n →₀ ℕ) (r : R) :
    projectiveDehomogenize R k (MvPolynomial.monomial p r) =
      MvPolynomial.C r * p.prod (fun i e => projectiveChartVariable R k i ^ e) := by
  exact MvPolynomial.eval₂Hom_monomial _ _ _ _

theorem projectiveDehomogenize_coordinate_power (R : Type*) [CommRing R] (k : Fin n)
    (d : ℕ) :
    projectiveDehomogenize R k (MvPolynomial.monomial (Finsupp.single k d) (1 : R)) = 1 := by
  rw [← MvPolynomial.X_pow_eq_monomial, map_pow, projectiveDehomogenize_X_self, one_pow]

theorem projectiveDehomogenize_scalar_commutes {R S : Type*} [CommRing R] [CommRing S]
    (c : R →+* S) (k : Fin n) (f : MvPolynomial (Fin n) R) :
    MvPolynomial.map c (projectiveDehomogenize R k f) =
      projectiveDehomogenize S k (MvPolynomial.map c f) := by
  have heq : (MvPolynomial.map c).comp (projectiveDehomogenize R k) =
      (projectiveDehomogenize S k).comp (MvPolynomial.map c) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [projectiveDehomogenize]
    · intro i
      by_cases h : i = k
      · subst i
        simp [projectiveDehomogenize, projectiveChartVariable]
      · simp [projectiveDehomogenize, projectiveChartVariable, h]
  exact RingHom.congr_fun heq f

noncomputable def projectiveChartLocalizationToAffine (R : Type*) [CommRing R] (k : Fin n) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin n) R)
      (MvPolynomial.X k) →+* MvPolynomial {j : Fin n // j ≠ k} R :=
  (Localization.awayLift (projectiveDehomogenize R k) (MvPolynomial.X k)
    (by rw [projectiveDehomogenize_X_self]; exact isUnit_one)).comp
      (algebraMap _ (Localization.Away (MvPolynomial.X k : MvPolynomial (Fin n) R)))

set_option backward.isDefEq.respectTransparency false in
theorem projectiveChartLocalizationToAffine_mk (R : Type*) [CommRing R] (k : Fin n)
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    projectiveChartLocalizationToAffine R k
      (HomogeneousLocalization.Away.mk _ (MvPolynomial.isHomogeneous_X R k) d f
        (by simpa using hf)) = projectiveDehomogenize R k f := by
  unfold projectiveChartLocalizationToAffine
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  have hunit : projectiveDehomogenize R k (MvPolynomial.X k) * 1 = 1 := by
    rw [projectiveDehomogenize_X_self, one_mul]
  simpa using Localization.awayLift_mk (projectiveDehomogenize R k)
    (MvPolynomial.X k) f 1 hunit d

end MixedFujita
