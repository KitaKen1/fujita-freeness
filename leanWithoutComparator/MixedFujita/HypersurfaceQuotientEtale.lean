/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KernelCoordinates
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
Coordinate hyperplanes of étale coordinates (step 9, restriction theorem).

If K[X_0, …, X_N] → C is formally étale, then so is K[X_1, …, X_N] → C/(φ X_0)
(`formallyEtale_quotient_of_formallyEtale_succ`): write K[X_0, …, X_N] = P'[X] with
P' = K[X_1, …, X_N]; then C/(φ X_0) is the base change of C along P'[X] → P'[X]/(X) ≅ P'.
So the hypersurface cut out by the first étale coordinate is étale over affine space of one
dimension less, the smoothness half of the hypersurface step in the induction on the codimension
in the restriction theorem.
-/

@[expose] public section

namespace MixedFujita

set_option linter.style.haveILetI false

section QuotientMap

/-- A formally étale map stays formally étale modulo an ideal and its extension (base change along
Q → Q/I). -/
theorem formallyEtale_quotientMap_map {Q C : Type*} [CommRing Q] [CommRing C] (f : Q →+* C)
    (hf : f.FormallyEtale) (I : Ideal Q) :
    (Ideal.quotientMap (I.map f) f Ideal.le_comap_map).FormallyEtale := by
  letI : Algebra Q C := f.toAlgebra
  haveI : Algebra.FormallyEtale Q C := hf
  haveI : Algebra.FormallyEtale (Q ⧸ I) (C ⧸ I.map (algebraMap Q C)) :=
    Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C I).symm
  exact (RingHom.formallyEtale_algebraMap (R := Q ⧸ I)
    (S := C ⧸ I.map (algebraMap Q C))).mpr inferInstance

end QuotientMap

section Quotient

variable {K C : Type*} [CommRing K] [CommRing C] [Algebra K C] {N : ℕ}

/-- If K[X_0, …, X_N] → C is formally étale, then so is K[X_1, …, X_N] → C/(φ X_0). -/
theorem formallyEtale_quotient_of_formallyEtale_succ
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] C) (hφ : φ.toRingHom.FormallyEtale) :
    ((Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})).comp
      (φ.comp (MvPolynomial.rename Fin.succ))).toRingHom.FormallyEtale := by
  classical
  -- K[X_0, …, X_N] = P'[X]
  let φ' : Polynomial (MvPolynomial (Fin N) K) →+* C :=
    φ.toRingHom.comp (MvPolynomial.finSuccEquiv K N).symm.toRingEquiv.toRingHom
  have hφ' : φ'.FormallyEtale :=
    RingHom.FormallyEtale.comp (ringHom_formallyEtale_of_etale _
      (RingHom.Etale.of_bijective (MvPolynomial.finSuccEquiv K N).symm.bijective)) hφ
  let I : Ideal (Polynomial (MvPolynomial (Fin N) K)) := Ideal.span {Polynomial.X}
  -- the base change along P'[X] → P'[X]/(X)
  have h2 := formallyEtale_quotientMap_map φ' hφ' I
  -- P' ≅ P'[X]/(X)
  let α₁ : MvPolynomial (Fin N) K →+* Polynomial (MvPolynomial (Fin N) K) ⧸ I :=
    (Ideal.Quotient.mk I).comp Polynomial.C
  have hspan : Ideal.span {Polynomial.X - Polynomial.C (0 : MvPolynomial (Fin N) K)} = I := by
    simp [I]
  let E : (Polynomial (MvPolynomial (Fin N) K) ⧸ I) ≃ₐ[MvPolynomial (Fin N) K]
      MvPolynomial (Fin N) K :=
    (Ideal.quotientEquivAlgOfEq (MvPolynomial (Fin N) K) hspan.symm).trans
      (Polynomial.quotientSpanXSubCAlgEquiv 0)
  have hα₁ : Function.Bijective α₁ := by
    have h1 : ∀ a, α₁ a = E.symm a := by
      intro a
      have h := E.symm.commutes a
      rw [Algebra.algebraMap_self, RingHom.id_apply] at h
      rw [h]
      rfl
    rw [show (α₁ : MvPolynomial (Fin N) K → _) = E.symm from funext h1]
    exact E.symm.bijective
  -- the ideal of C
  have hI : I.map φ' = Ideal.span {φ (MvPolynomial.X 0)} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change φ ((MvPolynomial.finSuccEquiv K N).symm Polynomial.X) = φ (MvPolynomial.X 0)
    rw [← MvPolynomial.finSuccEquiv_X_zero, AlgEquiv.symm_apply_apply]
  let α₃ := Ideal.quotEquivOfEq hI
  have hcomp : ((Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)})).comp
      (φ.comp (MvPolynomial.rename Fin.succ))).toRingHom =
      (α₃.toRingHom.comp (Ideal.quotientMap (I.map φ') φ' Ideal.le_comap_map)).comp α₁ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Ideal.Quotient.mk _ (φ (MvPolynomial.rename Fin.succ (MvPolynomial.C a))) =
        α₃ (Ideal.Quotient.mk _ (φ' (Polynomial.C (MvPolynomial.C a))))
      rw [Ideal.quotEquivOfEq_mk, MvPolynomial.rename_C]
      congr 1
      change φ (MvPolynomial.C a) =
        φ ((MvPolynomial.finSuccEquiv K N).symm (Polynomial.C (MvPolynomial.C a)))
      congr 1
      have h3 : Polynomial.C (MvPolynomial.C a) =
          algebraMap K (Polynomial (MvPolynomial (Fin N) K)) a := by
        rw [Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rw [h3, AlgEquiv.commutes, MvPolynomial.algebraMap_eq]
    · intro i
      change Ideal.Quotient.mk _ (φ (MvPolynomial.rename Fin.succ (MvPolynomial.X i))) =
        α₃ (Ideal.Quotient.mk _ (φ' (Polynomial.C (MvPolynomial.X i))))
      rw [Ideal.quotEquivOfEq_mk, MvPolynomial.rename_X]
      congr 1
      change φ (MvPolynomial.X i.succ) =
        φ ((MvPolynomial.finSuccEquiv K N).symm (Polynomial.C (MvPolynomial.X i)))
      rw [← MvPolynomial.finSuccEquiv_X_succ, AlgEquiv.symm_apply_apply]
  rw [hcomp]
  exact RingHom.FormallyEtale.comp
    (ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective hα₁))
    (RingHom.FormallyEtale.comp h2
      (ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective α₃.bijective)))

end Quotient

end MixedFujita
