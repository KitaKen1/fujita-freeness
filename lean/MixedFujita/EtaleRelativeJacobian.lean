/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleCoordinateDifferentials
public import MixedFujita.JacobianCoordinateChange

/-!
The relative canonical divisor through étale coordinates and its value on test valuations (step 6).
For étale coordinates y on S the coordinate derivations ∂_j, the dual basis of (d y_j), satisfy
∂_j(y_k) = δ_jk, and a K-derivation of S is determined by its values on the coordinates, since
Ω[S/K] has the basis (d y_j). If φ : S → K[[Y]] sends y_j to Y_j, such as the Taylor expansion in
the completion coordinates of a centred étale chart, then φ(∂_j s) = ∂φ(s)/∂Y_j, as both sides are
derivations agreeing on the coordinates. For a K-algebra map ψ : R → S and coordinates x on R the
relative Jacobian J_ij = ∂_j ψ(x_i) has as determinant the coefficient of ψ*(dx_1 ∧ ⋯ ∧ dx_n) in
dy_1 ∧ ⋯ ∧ dy_n, the local equation of the relative canonical divisor K_{T'/X}. The chain rule
J(ψ₂ ∘ ψ₁) = ψ₂(J(ψ₁)) J(ψ₂) holds, so other coordinates multiply the determinant by a unit. Its image
under φ is the determinant of the formal Jacobian of the map of completions, so the log discrepancy
Σ w + v(det J) of a monomial test valuation is Σ w + v(K_{T'/X}), the usual log discrepancy.
-/

@[expose] public section

namespace MixedFujita

open KaehlerDifferential

variable {n : ℕ}

section Derivations

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S]

/-- The coordinate derivation ∂/∂y_j of étale coordinates y. -/
noncomputable def etaleCoordinateDerivation (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (j : Fin n) : Derivation K S S :=
  ((etaleCoordinateBasis y hy).coord j).compDer (D K S)

theorem etaleCoordinateDerivation_apply (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (j : Fin n) (s : S) :
    etaleCoordinateDerivation y hy j s = (etaleCoordinateBasis y hy).repr (D K S s) j :=
  rfl

/-- ∂_j(y_i) = δ_ij. -/
theorem etaleCoordinateDerivation_coordinate (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (i j : Fin n) :
    etaleCoordinateDerivation y hy j (y (MvPolynomial.X i)) = if i = j then 1 else 0 := by
  rw [etaleCoordinateDerivation_apply, ← etaleCoordinateBasis_apply y hy,
    Module.Basis.repr_self_apply]

/-- A derivation of S is determined by its values on étale coordinates. -/
theorem derivation_ext_etaleCoordinates {M : Type*} [AddCommGroup M] [Module S M] [Module K M]
    [IsScalarTower K S M] (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
    {d d' : Derivation K S M} (h : ∀ i, d (y (MvPolynomial.X i)) = d' (y (MvPolynomial.X i))) :
    d = d' := by
  have hlift : d.liftKaehlerDifferential = d'.liftKaehlerDifferential :=
    (etaleCoordinateBasis y hy).ext fun i => by
      rw [etaleCoordinateBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D, h i]
  rw [← d.liftKaehlerDifferential_comp, ← d'.liftKaehlerDifferential_comp, hlift]

/-- Taylor expansion commutes with the coordinate derivations: if φ sends y_i to Y_i then
φ(∂_j s) = ∂φ(s)/∂Y_j. -/
theorem etaleCoordinateDerivation_taylor (φ : S →ₐ[K] MvPowerSeries (Fin n) K)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
    (hφ : ∀ i, φ (y (MvPolynomial.X i)) = MvPowerSeries.X i) (j : Fin n) (s : S) :
    φ (etaleCoordinateDerivation y hy j s) = MvPowerSeries.pderiv j (φ s) := by
  let _ : Algebra S (MvPowerSeries (Fin n) K) := φ.toRingHom.toAlgebra
  have : IsScalarTower K S (MvPowerSeries (Fin n) K) :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  let d₁ : Derivation K S (MvPowerSeries (Fin n) K) :=
    (Algebra.linearMap S (MvPowerSeries (Fin n) K)).compDer (etaleCoordinateDerivation y hy j)
  let d₂ : Derivation K S (MvPowerSeries (Fin n) K) :=
    (MvPowerSeries.pderiv j).compAlgebraMap S
  have h : d₁ = d₂ := derivation_ext_etaleCoordinates y hy fun i => by
    change φ (etaleCoordinateDerivation y hy j (y (MvPolynomial.X i))) =
      MvPowerSeries.pderiv j (φ (y (MvPolynomial.X i)))
    rw [etaleCoordinateDerivation_coordinate, hφ, MvPowerSeries.pderiv_X, Pi.single_apply]
    by_cases hij : i = j
    · rw [ite_eq_left hij, ite_eq_left hij, map_one]
    · rw [ite_eq_right hij, ite_eq_right hij, map_zero]
  exact congr($h s)

end Derivations

section Relative

variable {K R S T : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing T]
  [Algebra K T]

/-- The relative Jacobian J_ij = ∂ψ(x_i)/∂y_j of ψ : R → S in coordinates x on R and étale
coordinates y on S. -/
noncomputable def etaleRelativeJacobian (ψ : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) :
    Matrix (Fin n) (Fin n) S :=
  Matrix.of fun i j => etaleCoordinateDerivation y hy j (ψ (x (MvPolynomial.X i)))

/-- det J is the coefficient of ψ*(dx_1 ∧ ⋯ ∧ dx_n) in dy_1 ∧ ⋯ ∧ dy_n. -/
theorem etaleRelativeJacobian_det (ψ : R →ₐ[K] S) (x : MvPolynomial (Fin n) K →ₐ[K] R)
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) :
    (etaleRelativeJacobian ψ x y hy).det =
      (etaleCoordinateBasis y hy).det fun i => D K S (ψ (x (MvPolynomial.X i))) := by
  rw [Module.Basis.det_apply, ← Matrix.det_transpose]
  congr 1

/-- For the identity in two étale coordinate systems, det J is the change of basis determinant,
the transition function of K_X. -/
theorem etaleRelativeJacobian_id_det (x y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hx : x.toRingHom.FormallyEtale) (hy : y.toRingHom.FormallyEtale) :
    (etaleRelativeJacobian (AlgHom.id K S) x y hy).det =
      (etaleCoordinateBasis y hy).det (etaleCoordinateBasis x hx) := by
  rw [etaleRelativeJacobian_det]
  congr 1
  funext i
  rw [etaleCoordinateBasis_apply]
  rfl

/-- The chain rule ∂^z_k(ψ s) = Σ_j ψ(∂^y_j s) ∂^z_k(ψ y_j). -/
theorem etaleCoordinateDerivation_chainRule (ψ : S →ₐ[K] T) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (z : MvPolynomial (Fin n) K →ₐ[K] T)
    (hz : z.toRingHom.FormallyEtale) (k : Fin n) (s : S) :
    etaleCoordinateDerivation z hz k (ψ s) =
      ∑ j, ψ (etaleCoordinateDerivation y hy j s) *
        etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))) := by
  let _ : Algebra S T := ψ.toRingHom.toAlgebra
  have : IsScalarTower K S T := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  let d₁ : Derivation K S T := (etaleCoordinateDerivation z hz k).compAlgebraMap S
  let d₂ : Derivation K S T := ∑ j, (LinearMap.id.smulRight
    (etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))))).compDer
      (etaleCoordinateDerivation y hy j)
  have hd₂ : ∀ s, d₂ s = ∑ j, ψ (etaleCoordinateDerivation y hy j s) *
      etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))) := by
    intro s
    have h := congr_fun (map_sum (Derivation.coeFnAddMonoidHom (R := K) (A := S) (M := T))
      (fun j => (LinearMap.id.smulRight
        (etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X j))))).compDer
          (etaleCoordinateDerivation y hy j)) Finset.univ) s
    rw [Finset.sum_apply] at h
    exact h
  have h : d₁ = d₂ := derivation_ext_etaleCoordinates y hy fun i => by
    rw [hd₂]
    change etaleCoordinateDerivation z hz k (ψ (y (MvPolynomial.X i))) = _
    simp_rw [etaleCoordinateDerivation_coordinate]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [ite_eq_right (Ne.symm hji), map_zero, zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi), ite_eq_left rfl, map_one, one_mul]
  rw [← hd₂, ← h]
  rfl

/-- J(ψ₂ ∘ ψ₁) = ψ₂(J(ψ₁)) J(ψ₂). -/
theorem etaleRelativeJacobian_comp (ψ₁ : R →ₐ[K] S) (ψ₂ : S →ₐ[K] T)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (z : MvPolynomial (Fin n) K →ₐ[K] T)
    (hz : z.toRingHom.FormallyEtale) :
    etaleRelativeJacobian (ψ₂.comp ψ₁) x z hz =
      (ψ₂ : S →+* T).mapMatrix (etaleRelativeJacobian ψ₁ x y hy) *
        etaleRelativeJacobian ψ₂ y z hz := by
  refine Matrix.ext fun i k => ?_
  rw [Matrix.mul_apply]
  exact etaleCoordinateDerivation_chainRule ψ₂ y hy z hz k (ψ₁ (x (MvPolynomial.X i)))

/-- det J(ψ₂ ∘ ψ₁) = ψ₂(det J(ψ₁)) det J(ψ₂). -/
theorem etaleRelativeJacobian_det_comp (ψ₁ : R →ₐ[K] S) (ψ₂ : S →ₐ[K] T)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (z : MvPolynomial (Fin n) K →ₐ[K] T)
    (hz : z.toRingHom.FormallyEtale) :
    (etaleRelativeJacobian (ψ₂.comp ψ₁) x z hz).det =
      ψ₂ (etaleRelativeJacobian ψ₁ x y hy).det * (etaleRelativeJacobian ψ₂ y z hz).det := by
  rw [etaleRelativeJacobian_comp ψ₁ ψ₂ x y hy z hz, Matrix.det_mul]
  congr 1
  exact (RingHom.map_det (ψ₂ : S →+* T) _).symm

/-- Other étale coordinates on the source multiply det J by a unit. -/
theorem etaleRelativeJacobian_det_change_source (ψ : R →ₐ[K] S)
    (x x' : MvPolynomial (Fin n) K →ₐ[K] R) (hx : x.toRingHom.FormallyEtale)
    (hx' : x'.toRingHom.FormallyEtale) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) :
    (etaleRelativeJacobian ψ x' y hy).det =
      ψ ((etaleCoordinateBasis x hx).det (etaleCoordinateBasis x' hx')) *
        (etaleRelativeJacobian ψ x y hy).det := by
  have h := etaleRelativeJacobian_det_comp (AlgHom.id K R) ψ x' x hx y hy
  rw [AlgHom.comp_id, etaleRelativeJacobian_id_det x' x hx' hx] at h
  exact h

/-- Other étale coordinates on the target multiply det J by a unit. -/
theorem etaleRelativeJacobian_det_change_target (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y y' : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale) :
    (etaleRelativeJacobian ψ x y' hy').det =
      (etaleRelativeJacobian ψ x y hy).det *
        (etaleCoordinateBasis y' hy').det (etaleCoordinateBasis y hy) := by
  have h := etaleRelativeJacobian_det_comp ψ (AlgHom.id K S) x y hy y' hy'
  rw [AlgHom.id_comp, etaleRelativeJacobian_id_det y y' hy hy'] at h
  exact h

end Relative

section Completion

variable {K R S : Type*} [Field K] [CommRing R] [Algebra K R] [CommRing S] [Algebra K S]

/-- The formal Jacobian of the map of completions is the Taylor expansion of the relative
Jacobian: if φ_R and φ_S send the coordinates to the variables and Ψ ∘ φ_R = φ_S ∘ ψ, then
J(Ψ) = φ_S(J(ψ)). -/
theorem powerSeriesJacobian_eq_map_etaleRelativeJacobian (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (φR : R →ₐ[K] MvPowerSeries (Fin n) K)
    (φS : S →ₐ[K] MvPowerSeries (Fin n) K)
    (hφR : ∀ i, φR (x (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hφS : ∀ i, φS (y (MvPolynomial.X i)) = MvPowerSeries.X i)
    (Ψ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hΨ : ∀ r, Ψ (φR r) = φS (ψ r)) :
    powerSeriesJacobian Ψ = (φS : S →+* MvPowerSeries (Fin n) K).mapMatrix
      (etaleRelativeJacobian ψ x y hy) := by
  refine Matrix.ext fun i j => ?_
  change MvPowerSeries.pderiv j (Ψ (MvPowerSeries.X i)) =
    φS (etaleCoordinateDerivation y hy j (ψ (x (MvPolynomial.X i))))
  rw [← hφR i, hΨ, etaleCoordinateDerivation_taylor φS y hy hφS]

/-- det J(Ψ) = φ_S(det J(ψ)): the formal Jacobian determinant is the Taylor expansion of the local
equation of K_{T'/X}. -/
theorem powerSeriesJacobian_det_eq_etaleRelativeJacobian (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (φR : R →ₐ[K] MvPowerSeries (Fin n) K)
    (φS : S →ₐ[K] MvPowerSeries (Fin n) K)
    (hφR : ∀ i, φR (x (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hφS : ∀ i, φS (y (MvPolynomial.X i)) = MvPowerSeries.X i)
    (Ψ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hΨ : ∀ r, Ψ (φR r) = φS (ψ r)) :
    (powerSeriesJacobian Ψ).det = φS (etaleRelativeJacobian ψ x y hy).det := by
  rw [powerSeriesJacobian_eq_map_etaleRelativeJacobian ψ x y hy φR φS hφR hφS Ψ hΨ]
  exact (RingHom.map_det (φS : S →+* MvPowerSeries (Fin n) K) _).symm

/-- The log discrepancy of a monomial test valuation is Σ w + v(K_{T'/X}). -/
theorem testValuation_logDiscrepancy_eq_relativeCanonical (w : Fin n → ℕ) (ψ : R →ₐ[K] S)
    (x : MvPolynomial (Fin n) K →ₐ[K] R) (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (φR : R →ₐ[K] MvPowerSeries (Fin n) K)
    (φS : S →ₐ[K] MvPowerSeries (Fin n) K)
    (hφR : ∀ i, φR (x (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hφS : ∀ i, φS (y (MvPolynomial.X i)) = MvPowerSeries.X i)
    (Ψ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hΨ : ∀ r, Ψ (φR r) = φS (ψ r)) :
    ((∑ j, w j : ℕ) : ℕ∞) + (powerSeriesJacobian Ψ).det.weightedOrder w =
      ((∑ j, w j : ℕ) : ℕ∞) + (φS (etaleRelativeJacobian ψ x y hy).det).weightedOrder w := by
  rw [powerSeriesJacobian_det_eq_etaleRelativeJacobian ψ x y hy φR φS hφR hφS Ψ hΨ]

end Completion

section Scheme

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] {T T' : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [T'.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower

/-- The Taylor expansion of germs at q in completion coordinates e. -/
noncomputable def stalkTaylorExpansion (q : T)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk q)) (T.presheaf.stalk q) ≃ₐ[K]
      MvPowerSeries (Fin n) K) : T.presheaf.stalk q →ₐ[K] MvPowerSeries (Fin n) K :=
  { (e : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk q)) (T.presheaf.stalk q) →+*
      MvPowerSeries (Fin n) K).comp (algebraMap (T.presheaf.stalk q)
        (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk q)) (T.presheaf.stalk q))) with
    commutes' := fun c => by
      change e (algebraMap _ _ (algebraMap K (T.presheaf.stalk q) c)) = _
      rw [← e.commutes c]
      rfl }

theorem stalkTaylorExpansion_apply (q : T)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk q)) (T.presheaf.stalk q) ≃ₐ[K]
      MvPowerSeries (Fin n) K) (a : T.presheaf.stalk q) :
    stalkTaylorExpansion q e a = e (algebraMap _
      (AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk q)) (T.presheaf.stalk q)) a) :=
  rfl

/-- In completion coordinates given by centred étale coordinates x at ρ(p) and y at p, the formal
Jacobian determinant of the map of completed local rings is the Taylor expansion at p of
det(∂ρ^♯x_i/∂y_j), the local equation of K_{T'/T}. -/
theorem schemeCompletedStalkMap_jacobian_det_eq_relative (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T')
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (x : MvPolynomial (Fin n) K →ₐ[K] T.presheaf.stalk (ρ p))
    (y : MvPolynomial (Fin n) K →ₐ[K] T'.presheaf.stalk p) (hy : y.toRingHom.FormallyEtale)
    (hx : ∀ i, stalkTaylorExpansion (ρ p) ez (x (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hy' : ∀ i, stalkTaylorExpansion p ep (y (MvPolynomial.X i)) = MvPowerSeries.X i) :
    (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det =
      stalkTaylorExpansion p ep
        (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ p) x y hy).det :=
  powerSeriesJacobian_det_eq_etaleRelativeJacobian _ x y hy _ _ hx hy' _
    fun a => schemeCompletedStalkMap_algebraMap ρ p ez ep a

/-- The log discrepancy Σ w + v(det J) of the monomial test valuation with weights w in the
coordinates ep at p is Σ w + v(K_{T'/T}), for any completion coordinates at ρ(p). -/
theorem schemeTestValuation_jacobian_weightedOrder_eq_relative [CharZero K] (ρ : T' ⟶ T)
    [ρ.IsOver (Spec (CommRingCat.of K))] (p : T')
    (ez ez₀ : AdicCompletion (IsLocalRing.maximalIdeal (T.presheaf.stalk (ρ p)))
      (T.presheaf.stalk (ρ p)) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (ep : AdicCompletion (IsLocalRing.maximalIdeal (T'.presheaf.stalk p))
      (T'.presheaf.stalk p) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (x : MvPolynomial (Fin n) K →ₐ[K] T.presheaf.stalk (ρ p))
    (y : MvPolynomial (Fin n) K →ₐ[K] T'.presheaf.stalk p) (hy : y.toRingHom.FormallyEtale)
    (hx : ∀ i, stalkTaylorExpansion (ρ p) ez₀ (x (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hy' : ∀ i, stalkTaylorExpansion p ep (y (MvPolynomial.X i)) = MvPowerSeries.X i)
    (w : Fin n → ℕ) :
    (powerSeriesJacobian (schemeCompletedStalkMap ρ p ez ep)).det.weightedOrder w =
      (stalkTaylorExpansion p ep
        (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) ρ p) x y hy).det).weightedOrder w := by
  rw [schemeCompletedStalkMap_jacobian_weightedOrder_eq ρ p ez₀ ez ep w,
    schemeCompletedStalkMap_jacobian_det_eq_relative ρ p ez₀ ep x y hy hx hy']

end Scheme

end MixedFujita
