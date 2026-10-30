/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupRelativeCanonical
public import MixedFujita.DVRVanishingOrder

/-! A vanishing coordinate with a derivative equal to one is irreducible in a
local ring: two nonunit factors would force its derivative into the maximal
ideal. In a DVR it is therefore a uniformizer. This avoids a separate
coordinate-stratum reducedness argument and works in every characteristic. -/

@[expose] public section
namespace MixedFujita
open KaehlerDifferential

theorem localRing_irreducible_of_derivation_eq_one {K R : Type*} [CommRing K]
    [CommRing R] [Algebra K R] [IsLocalRing R]
    (δ : Derivation K R R) (a : R) (ha : ¬ IsUnit a) (hδ : δ a = 1) :
    Irreducible a := by
  refine ⟨ha, ?_⟩
  intro b c hbc
  by_contra h
  have hb : b ∈ IsLocalRing.maximalIdeal R := by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using (fun hu => h (Or.inl hu))
  have hc : c ∈ IsLocalRing.maximalIdeal R := by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using (fun hu => h (Or.inr hu))
  have hd : δ a ∈ IsLocalRing.maximalIdeal R := by
    rw [hbc, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hb) (Ideal.mul_mem_right _ _ hc)
  rw [hδ] at hd
  exact Ideal.one_notMem (IsLocalRing.maximalIdeal R) hd

theorem etaleDVR_coordinate_irreducible {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
    (y : MvPolynomial (Fin n) K →ₐ[K] R) (hy : y.toRingHom.FormallyEtale)
    (k : Fin n) (hk : ¬ IsUnit (y (MvPolynomial.X k))) :
    Irreducible (y (MvPolynomial.X k)) := by
  apply localRing_irreducible_of_derivation_eq_one (etaleCoordinateDerivation y hy k) _ hk
  simpa using etaleCoordinateDerivation_coordinate y hy k k

theorem etaleDVR_coordinate_localAdicOrder {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
    (y : MvPolynomial (Fin n) K →ₐ[K] R) (hy : y.toRingHom.FormallyEtale)
    (k : Fin n) (hk : ¬ IsUnit (y (MvPolynomial.X k))) :
    localAdicOrder R (y (MvPolynomial.X k)) = 1 := by
  rw [dvr_localAdicOrder_eq_addVal]
  exact IsDiscreteValuationRing.addVal_uniformizer (etaleDVR_coordinate_irreducible y hy k hk)

theorem pointBlowup_etaleDVR_jacobian_order {K R S : Type*} [Field K]
    [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]
    [IsDomain S] [IsDiscreteValuationRing S] {n : ℕ}
    (β : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y z : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hz : z.toRingHom.FormallyEtale)
    (k : Fin n) (hk : ¬ IsUnit (y (MvPolynomial.X k)))
    (hcoord : ∀ i, β (x (MvPolynomial.X i)) =
      if i = k then y (MvPolynomial.X k) else y (MvPolynomial.X i) * y (MvPolynomial.X k)) :
    localAdicOrder S (etaleRelativeJacobian β x z hz).det = (n - 1 : ℕ) := by
  rw [etaleRelativeJacobian_det_change_target β x y z hy hz,
    pointBlowup_etaleRelativeJacobian_det β x y hy k hcoord,
    dvr_localAdicOrder_eq_addVal, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer (etaleDVR_coordinate_irreducible y hy k hk),
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (Module.Basis.isUnit_det _ _)]
  simp

end MixedFujita
