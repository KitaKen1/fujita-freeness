/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RationalLocalPoints
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
The actual residue field of a maximal ideal in a finite type algebra over
an algebraically closed field is the base field. This constructs evaluation
on the algebra and its actual localization, without a supplied rational point.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A]
  [Algebra K A] [Algebra.FiniteType K A] (p : Ideal A) [p.IsMaximal]

noncomputable def closedPointResidueEquiv : (A ⧸ p) ≃ₐ[K] K := by
  let := Ideal.Quotient.field p
  let := finite_of_finite_type_of_isJacobsonRing K (A ⧸ p)
  exact (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ p))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := A ⧸ p))).symm

noncomputable def closedPointEvaluation : A →ₐ[K] K :=
  (closedPointResidueEquiv (K := K) p).toAlgHom.comp (Ideal.Quotient.mkₐ K p)

theorem closedPointEvaluation_eq_zero_iff (a : A) :
    closedPointEvaluation (K := K) p a = 0 ↔ a ∈ p := by
  change closedPointResidueEquiv (K := K) p (Ideal.Quotient.mk p a) = 0 ↔ a ∈ p
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (closedPointResidueEquiv (K := K) p).injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

theorem closedPointEvaluation_ker :
    RingHom.ker (closedPointEvaluation (K := K) p).toRingHom = p := by
  ext a
  exact closedPointEvaluation_eq_zero_iff (K := K) p a

variable (S : Type*) [CommRing S] [Algebra K S] [Algebra A S]
  [IsScalarTower K A S] [IsLocalization.AtPrime S p]

noncomputable def closedPointLocalEvaluation : S →ₐ[K] K :=
  IsLocalization.liftAlgHom (M := p.primeCompl) (f := closedPointEvaluation (K := K) p)
    (fun y => isUnit_iff_ne_zero.mpr (fun h =>
      y.property ((closedPointEvaluation_eq_zero_iff (K := K) p y.val).mp h)))

@[simp]
theorem closedPointLocalEvaluation_algebraMap (a : A) :
    closedPointLocalEvaluation (K := K) p S (algebraMap A S a) =
      closedPointEvaluation (K := K) p a := by
  exact IsLocalization.lift_eq _ a

include p in
theorem closedPointLocalEvaluation_residueField [IsLocalRing S] :
    Nonempty ((S ⧸ IsLocalRing.maximalIdeal S) ≃ₐ[K] K) :=
  ⟨rationalLocalPointResidueEquiv (closedPointLocalEvaluation (K := K) p S)⟩

end MixedFujita
