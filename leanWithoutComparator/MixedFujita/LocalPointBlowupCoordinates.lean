/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialPointBlowupTransform
public import Hironaka.Scheme.BlowUp.AffineAlgebra

/-!
Standard polynomial blow-up coordinates in the actual algebra R[I/a].
The coordinate X_k maps to a and the others to the fractions x_i/a.
The polynomial substitution is proved to be the actual pullback from R,
and the exceptional ideal and its nonzerodivisor equation come from Hironaka.
-/

@[expose] public section
open AlgebraicGeometry IsLocalization.Away
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] {n : ℕ}

theorem affineBlowup_frac_mul_exceptional (I : Ideal R) (a : R) {b : R} (hb : b ∈ I) :
    affineBlowUpAlgebra.frac (a := a) hb * algebraMap R (affineBlowUpAlgebra I a) a =
      algebraMap R (affineBlowUpAlgebra I a) b := by
  apply Subtype.ext
  change (algebraMap R (Localization.Away a) b * invSelf a) *
    algebraMap R (Localization.Away a) a = algebraMap R (Localization.Away a) b
  rw [mul_assoc, mul_comm (invSelf a), mul_invSelf, mul_one]

noncomputable def localPointBlowupPolynomialMap (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I) (k : Fin n) :
    MvPolynomial (Fin n) K →+* affineBlowUpAlgebra I (ψ (MvPolynomial.X k)) := by
  classical
  exact MvPolynomial.eval₂Hom
    ((algebraMap R (affineBlowUpAlgebra I (ψ (MvPolynomial.X k)))).comp (algebraMap K R))
    (fun i => if i = k then algebraMap R _ (ψ (MvPolynomial.X k)) else
      affineBlowUpAlgebra.frac (a := ψ (MvPolynomial.X k)) (hψ i))

theorem localPointBlowupPolynomialMap_C (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I)
    (k : Fin n) (c : K) :
    localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.C c) =
      algebraMap R (affineBlowUpAlgebra I (ψ (MvPolynomial.X k))) (algebraMap K R c) :=
  MvPolynomial.eval₂Hom_C _ _ c

theorem localPointBlowupPolynomialMap_X_self (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I) (k : Fin n) :
    localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.X k) =
      algebraMap R (affineBlowUpAlgebra I (ψ (MvPolynomial.X k))) (ψ (MvPolynomial.X k)) := by
  classical
  simp [localPointBlowupPolynomialMap]

theorem localPointBlowupPolynomialMap_X_other (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I)
    (k i : Fin n) (hi : i ≠ k) :
    localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.X i) =
      affineBlowUpAlgebra.frac (a := ψ (MvPolynomial.X k)) (hψ i) := by
  classical
  simp only [localPointBlowupPolynomialMap, MvPolynomial.eval₂Hom_X', ite_eq_right hi]

theorem localPointBlowupPolynomialMap_substitution (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I)
    (k : Fin n) (g : MvPolynomial (Fin n) K) :
    localPointBlowupPolynomialMap I ψ hψ k (polynomialPointBlowupMap k g) =
      algebraMap R (affineBlowUpAlgebra I (ψ (MvPolynomial.X k))) (ψ g) := by
  have hX (i : Fin n) :
      localPointBlowupPolynomialMap I ψ hψ k (polynomialPointBlowupMap k (MvPolynomial.X i)) =
        algebraMap R (affineBlowUpAlgebra I (ψ (MvPolynomial.X k))) (ψ (MvPolynomial.X i)) := by
    by_cases hi : i = k
    · subst i
      rw [polynomialPointBlowupMap_X_self, localPointBlowupPolynomialMap_X_self]
    · rw [polynomialPointBlowupMap_X_other k i hi, map_mul,
        localPointBlowupPolynomialMap_X_other I ψ hψ k i hi,
        localPointBlowupPolynomialMap_X_self, affineBlowup_frac_mul_exceptional]
  induction g using MvPolynomial.induction_on with
  | C c =>
    have hc : polynomialPointBlowupMap (K := K) k (MvPolynomial.C c) = MvPolynomial.C c :=
      (polynomialPointBlowupMap (K := K) k).commutes c
    rw [hc, localPointBlowupPolynomialMap_C]
    congr 1
    exact (ψ.commutes c).symm
  | add g h hg hh => simp only [map_add, hg, hh]
  | mul_X g i hg => simp only [map_mul, hg, hX]

theorem localPointBlowupPolynomialMap_exceptionalIdeal (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I) (k : Fin n) :
    I.map (algebraMap R (affineBlowUpAlgebra I (ψ (MvPolynomial.X k)))) =
      Ideal.span {localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.X k)} := by
  rw [localPointBlowupPolynomialMap_X_self]
  exact affineBlowUpAlgebra.map_algebraMap_eq_span_singleton (hψ k)

theorem localPointBlowupPolynomialMap_exceptional_nonZeroDivisor (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I) (k : Fin n) :
    localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.X k) ∈
      nonZeroDivisors (affineBlowUpAlgebra I (ψ (MvPolynomial.X k))) := by
  rw [localPointBlowupPolynomialMap_X_self]
  exact affineBlowUpAlgebra.algebraMap_mem_nonZeroDivisors

theorem localPointBlowupStrictTransform_unique (I : Ideal R)
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ I)
    (k : Fin n) (m : ℕ) (s : R)
    (q r : affineBlowUpAlgebra I (ψ (MvPolynomial.X k)))
    (hq : algebraMap R _ s = localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.X k) ^ m * q)
    (hr : algebraMap R _ s = localPointBlowupPolynomialMap I ψ hψ k (MvPolynomial.X k) ^ m * r) :
    q = r := by
  have hreg := (isRegular_iff_mem_nonZeroDivisors.mpr
    (localPointBlowupPolynomialMap_exceptional_nonZeroDivisor I ψ hψ k)).left
  exact IsLeftRegular.pow m hreg (hq.symm.trans hr)

end MixedFujita
