/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CoordinateHypersurfaceRestriction
public import MixedFujita.EtaleRelativeJacobian

/-!
The relative Jacobian on coordinate hyperplanes (step 9, adjunction for the restriction theorem).

For étale coordinates y_0, …, y_N on S the coordinates y_1, …, y_N of S/(y_0) are étale
(check-320), and the coordinate derivations descend: ∂_k(s mod y_0) = ∂_{k+1}(s) mod y_0
(`etaleCoordinateDerivation_quotient`), as both sides are derivations S → S/(y_0) agreeing on the
coordinates. If a K-algebra map ψ : R → S sends the first coordinate x_0 of R to y_0 w, the first
row of the relative Jacobian is (w, 0, …, 0) modulo y_0 and the rest is the relative Jacobian of
the induced map R/(x_0) → S/(y_0), so det J(ψ) ≡ w · det J(ψ̄) mod y_0
(`etaleRelativeJacobian_det_quotient`). This is adjunction for the strict transform H' = {y_0 = 0}
of the hyperplane H = {x_0 = 0}: along a component of E ∩ H' the order of K_{H'/H} is the order
of K_{T/X} along E minus the order of x_0 along E.
-/

@[expose] public section

namespace MixedFujita

open KaehlerDifferential

set_option linter.style.haveILetI false

section Hyperplane

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] {N : ℕ}

/-- The coordinates x_1, …, x_N on R/(x_0). -/
noncomputable def hyperplaneCoords (x : MvPolynomial (Fin (N + 1)) K →ₐ[K] R) :
    MvPolynomial (Fin N) K →ₐ[K] R ⧸ Ideal.span {x (MvPolynomial.X 0)} :=
  (Ideal.Quotient.mkₐ K (Ideal.span {x (MvPolynomial.X 0)})).comp
    (x.comp (MvPolynomial.rename Fin.succ))

theorem hyperplaneCoords_X (x : MvPolynomial (Fin (N + 1)) K →ₐ[K] R) (i : Fin N) :
    hyperplaneCoords x (MvPolynomial.X i) =
      Ideal.Quotient.mk (Ideal.span {x (MvPolynomial.X 0)}) (x (MvPolynomial.X i.succ)) := by
  change Ideal.Quotient.mk _ (x (MvPolynomial.rename Fin.succ (MvPolynomial.X i))) = _
  rw [MvPolynomial.rename_X]

/-- The coordinates y_1, …, y_N of S/(y_0) are étale. -/
theorem hyperplaneCoords_formallyEtale (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) : (hyperplaneCoords y).toRingHom.FormallyEtale :=
  formallyEtale_quotient_of_formallyEtale_succ y hy

/-- The coordinate derivations descend to S/(y_0): ∂_k(s mod y_0) = ∂_{k+1}(s) mod y_0. -/
theorem etaleCoordinateDerivation_quotient (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (k : Fin N) (s : S) :
    etaleCoordinateDerivation (hyperplaneCoords y) (hyperplaneCoords_formallyEtale y hy) k
        (Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}) s) =
      Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)})
        (etaleCoordinateDerivation y hy k.succ s) := by
  let I : Ideal S := Ideal.span {y (MvPolynomial.X 0)}
  let d₁ : Derivation K S (S ⧸ I) :=
    (etaleCoordinateDerivation (hyperplaneCoords y)
      (hyperplaneCoords_formallyEtale y hy) k).compAlgebraMap S
  let d₂ : Derivation K S (S ⧸ I) :=
    (Algebra.linearMap S (S ⧸ I)).compDer (etaleCoordinateDerivation y hy k.succ)
  have h : d₁ = d₂ := derivation_ext_etaleCoordinates y hy fun i => by
    change etaleCoordinateDerivation (hyperplaneCoords y) (hyperplaneCoords_formallyEtale y hy) k
        (Ideal.Quotient.mk I (y (MvPolynomial.X i))) =
      Ideal.Quotient.mk I (etaleCoordinateDerivation y hy k.succ (y (MvPolynomial.X i)))
    rw [etaleCoordinateDerivation_coordinate]
    cases i using Fin.cases with
    | zero =>
      have h0 : Ideal.Quotient.mk I (y (MvPolynomial.X 0)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      rw [h0, map_zero, ite_eq_right (Fin.succ_ne_zero k).symm, map_zero]
    | succ l =>
      rw [← hyperplaneCoords_X, etaleCoordinateDerivation_coordinate]
      by_cases hlk : l = k
      · rw [ite_eq_left hlk, ite_eq_left (congrArg Fin.succ hlk), map_one]
      · rw [ite_eq_right hlk, ite_eq_right (fun h => hlk (Fin.succ_injective _ h)), map_zero]
  exact congr($h s)

/-- If ψ sends x_0 to y_0 w, then det J(ψ) ≡ w · det J(ψ̄) modulo y_0, for the induced map
ψ̄ : R/(x_0) → S/(y_0) in the coordinates x_1, …, x_N and y_1, …, y_N. -/
theorem etaleRelativeJacobian_det_quotient (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin (N + 1)) K →ₐ[K] R) (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (w : S)
    (hw : ψ (x (MvPolynomial.X 0)) = y (MvPolynomial.X 0) * w)
    (h : Ideal.span {x (MvPolynomial.X 0)} ≤ (Ideal.span {y (MvPolynomial.X 0)}).comap ψ) :
    Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}) (etaleRelativeJacobian ψ x y hy).det =
      Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}) w *
        (etaleRelativeJacobian (Ideal.quotientMapₐ (Ideal.span {y (MvPolynomial.X 0)}) ψ h)
          (hyperplaneCoords x) (hyperplaneCoords y) (hyperplaneCoords_formallyEtale y hy)).det := by
  let I : Ideal S := Ideal.span {y (MvPolynomial.X 0)}
  have hy0 : Ideal.Quotient.mk I (y (MvPolynomial.X 0)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  -- the first row modulo y_0
  have hrow : ∀ j, Ideal.Quotient.mk I (etaleRelativeJacobian ψ x y hy 0 j) =
      if j = 0 then Ideal.Quotient.mk I w else 0 := by
    intro j
    change Ideal.Quotient.mk I (etaleCoordinateDerivation y hy j (ψ (x (MvPolynomial.X 0)))) = _
    rw [hw, Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, hy0, zero_mul,
      zero_add, etaleCoordinateDerivation_coordinate]
    by_cases hj : j = 0
    · rw [ite_eq_left hj.symm, ite_eq_left hj, map_one, mul_one]
    · rw [ite_eq_right (Ne.symm hj), ite_eq_right hj, map_zero, mul_zero]
  -- the remaining block is the Jacobian of the induced map
  have hblock : ((etaleRelativeJacobian ψ x y hy).map (Ideal.Quotient.mk I)).submatrix
      Fin.succ Fin.succ =
      etaleRelativeJacobian (Ideal.quotientMapₐ I ψ h) (hyperplaneCoords x) (hyperplaneCoords y)
        (hyperplaneCoords_formallyEtale y hy) := by
    ext i k
    change Ideal.Quotient.mk I
        (etaleCoordinateDerivation y hy k.succ (ψ (x (MvPolynomial.X i.succ)))) =
      etaleCoordinateDerivation (hyperplaneCoords y) (hyperplaneCoords_formallyEtale y hy) k
        (Ideal.quotientMapₐ I ψ h (hyperplaneCoords x (MvPolynomial.X i)))
    rw [hyperplaneCoords_X, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      etaleCoordinateDerivation_quotient]
  rw [RingHom.map_det, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have htail : ∑ j : Fin N, (-1 : S ⧸ I) ^ (j.succ : ℕ) *
      (Ideal.Quotient.mk I).mapMatrix (etaleRelativeJacobian ψ x y hy) 0 j.succ *
      (((Ideal.Quotient.mk I).mapMatrix (etaleRelativeJacobian ψ x y hy)).submatrix Fin.succ
        j.succ.succAbove).det = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hrow, ite_eq_right (Fin.succ_ne_zero j), mul_zero,
      zero_mul]
  rw [htail, add_zero, RingHom.mapMatrix_apply, Matrix.map_apply, hrow, ite_eq_left rfl,
    Fin.succAbove_zero, hblock, Fin.val_zero, pow_zero, one_mul]

end Hyperplane

end MixedFujita
