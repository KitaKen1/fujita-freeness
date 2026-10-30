/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PolynomialCartierDecomposition
public import MixedFujita.EtaleRelativeJacobian

/-!
The Cartier decomposition on étale coordinate charts (step 10, the algebraic core of the
Deligne–Illusie route).

The argument of check-396 uses only four properties of the polynomial ring: the derivations
commute, `∂_i x_j = δ_{ij}`, the Euler operators satisfy `(x_j ∂_j)^p = x_j ∂_j`, and
`∂_j (1 - (x_j ∂_j)^{p-1}) = 0`. Under these hypotheses every cocycle of the coordinate de Rham
complex of an algebra `A` of characteristic `p` is uniquely the sum of a coboundary and a form on
which all weight operators vanish, and `d` vanishes on such forms
(`koszulDeRham_cartier_decomposition`).

All four properties hold for an algebra `S` over a field `K` of characteristic `p` with étale
coordinates `y_1, …, y_n` and the coordinate derivations `∂_j = ∂/∂y_j`, when `S` is a domain
(`etale_cartier_decomposition`): the commutator of two coordinate derivations is a derivation
vanishing on the coordinates, hence zero; in characteristic `p` the `p`-th power of a derivation
is a derivation (`derivation_pow_char_leibniz`, from `(E ⊗ 1 + 1 ⊗ E)^p = E^p ⊗ 1 + 1 ⊗ E^p` on
`S ⊗ S`), so `(y_j ∂_j)^p - y_j ∂_j` is a derivation vanishing on the coordinates, hence zero; and
`y_j ∂_j b = 0` forces `∂_j b = 0` in a domain. Every étale chart of a smooth variety over a field
of characteristic `p` therefore carries the Cartier decomposition of its coordinate de Rham complex.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section General

variable {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] {n : ℕ}
  (D : Fin n → A →ₗ[K] A) (x : Fin n → A)

/-- The Euler operators commute when the derivations commute and `∂_i x_j = δ_{ij}`. -/
theorem eulerOperator_comm (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (i j : Fin n) :
    eulerOperator D x i ∘ₗ eulerOperator D x j = eulerOperator D x j ∘ₗ eulerOperator D x i := by
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, eulerOperator_apply, hleib]
  have h1 : D i (D j a) = D j (D i a) := LinearMap.congr_fun (hD i j) a
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬j = i := fun h => hij h.symm
    simp only [hij, hji, ite_false, add_zero, h1]
    ring

theorem koszulDeRhamWeight_comm (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (i j : Fin n) :
    koszulDeRhamWeight D x i ∘ₗ koszulDeRhamWeight D x j =
      koszulDeRhamWeight D x j ∘ₗ koszulDeRhamWeight D x i := by
  simp only [koszulDeRhamWeight_eq_add, LinearMap.comp_add, LinearMap.add_comp,
    ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id,
    eulerOperator_comm D x hD hleib i j, coordWedgeContract_comm i j]
  abel

theorem koszulDeRhamDiff_comp_weight_pow (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (j : Fin n)
    (m : ℕ) :
    koszulDeRhamDiff D ∘ₗ (koszulDeRhamWeight D x j ^ m) =
      (koszulDeRhamWeight D x j ^ m) ∘ₗ koszulDeRhamDiff D := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
      koszulDeRhamDiff_comp_weight D x hD hleib, ← LinearMap.comp_assoc]

theorem koszulDeRhamWeight_comp_weight_pow (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0)) (i j : Fin n)
    (m : ℕ) :
    koszulDeRhamWeight D x i ∘ₗ (koszulDeRhamWeight D x j ^ m) =
      (koszulDeRhamWeight D x j ^ m) ∘ₗ koszulDeRhamWeight D x i := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
      koszulDeRhamWeight_comm D x hD hleib, ← LinearMap.comp_assoc]

/-- The composite of the idempotents `1 - θ_j^{p-1}` over the first `k` coordinates. -/
noncomputable def koszulCartierProjection (p : ℕ) (k : ℕ) :
    A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n :=
  match k with
  | 0 => LinearMap.id
  | k + 1 =>
    if h : k < n then
      (LinearMap.id - koszulDeRhamWeight D x ⟨k, h⟩ ^ (p - 1)) ∘ₗ koszulCartierProjection p k
    else koszulCartierProjection p k

theorem koszulCartierProjection_succ_of_lt (p : ℕ) {k : ℕ} (h : k < n) :
    koszulCartierProjection D x p (k + 1) =
      (LinearMap.id - koszulDeRhamWeight D x ⟨k, h⟩ ^ (p - 1)) ∘ₗ
        koszulCartierProjection D x p k := by
  simp only [koszulCartierProjection, h, dite_true]

theorem koszulCartierProjection_succ_of_not_lt (p : ℕ) {k : ℕ} (h : ¬k < n) :
    koszulCartierProjection D x p (k + 1) = koszulCartierProjection D x p k := by
  simp only [koszulCartierProjection, h, dite_false]

variable (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
  (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then a else 0))

include hD hleib in
theorem koszulDeRhamDiff_comp_cartierProjection (p : ℕ) (k : ℕ) :
    koszulDeRhamDiff D ∘ₗ koszulCartierProjection D x p k =
      koszulCartierProjection D x p k ∘ₗ koszulDeRhamDiff D := by
  induction k with
  | zero => rw [koszulCartierProjection, LinearMap.comp_id, LinearMap.id_comp]
  | succ k ih =>
    by_cases h : k < n
    · refine LinearMap.ext fun z => ?_
      have h1 := LinearMap.congr_fun ih z
      have h2 := LinearMap.congr_fun (koszulDeRhamDiff_comp_weight_pow D x hD hleib ⟨k, h⟩ (p - 1))
        (koszulCartierProjection D x p k z)
      simp only [LinearMap.comp_apply] at h1 h2
      simp only [LinearMap.comp_apply, koszulCartierProjection_succ_of_lt D x p h,
        LinearMap.sub_apply, LinearMap.id_apply, map_sub, h2, h1]
    · rw [koszulCartierProjection_succ_of_not_lt D x p h, ih]

variable (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) = 0)
  (hE : ∀ j, eulerOperator D x j ^ p = eulerOperator D x j)
  (hker : ∀ j, D j ∘ₗ (eulerOperator D x j ^ (p - 1)) = D j)

include hp hpK hE in
theorem koszulDeRhamWeight_pow_char_of_euler (j : Fin n) :
    koszulDeRhamWeight D x j ^ p = koszulDeRhamWeight D x j :=
  koszulDeRhamWeight_pow_of_euler p hpK D x j (hE j)

include hp in
theorem koszulDeRhamWeight_pow_pred_eq_zero (j : Fin n) (z : A ⊗[K] CoordExterior K n)
    (hz : koszulDeRhamWeight D x j z = 0) : (koszulDeRhamWeight D x j ^ (p - 1)) z = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by omega⟩
  rw [hq, pow_succ, Module.End.mul_apply, hz, map_zero]

include hp hker in
/-- `d` vanishes where all weights vanish. -/
theorem koszulDeRhamDiff_eq_zero_of_weights (z : A ⊗[K] CoordExterior K n)
    (hz : ∀ j, koszulDeRhamWeight D x j z = 0) : koszulDeRhamDiff D z = 0 := by
  rw [koszulDeRhamDiff, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h := LinearMap.congr_fun (partialWedge_comp_weight_pow D x i (p - 1)) z
  rw [LinearMap.comp_apply, koszulDeRhamWeight_pow_pred_eq_zero D x p i z (hz i), map_zero,
    hker i] at h
  exact h.symm

include hp in
theorem koszulCartierProjection_apply_of_weights (k : ℕ) (z : A ⊗[K] CoordExterior K n)
    (hz : ∀ j, koszulDeRhamWeight D x j z = 0) : koszulCartierProjection D x p k z = z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < n
    · rw [koszulCartierProjection_succ_of_lt D x p h, LinearMap.comp_apply, ih, LinearMap.sub_apply,
        LinearMap.id_apply, koszulDeRhamWeight_pow_pred_eq_zero D x p _ z (hz _), sub_zero]
    · rw [koszulCartierProjection_succ_of_not_lt D x p h, ih]

include hD hleib hp hpK hE in
theorem koszulDeRhamWeight_cartierProjection (k : ℕ) (y : A ⊗[K] CoordExterior K n) (j : Fin n)
    (hj : (j : ℕ) < k) : koszulDeRhamWeight D x j (koszulCartierProjection D x p k y) = 0 := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases h : k < n
    · rw [koszulCartierProjection_succ_of_lt D x p h, LinearMap.comp_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · have hc := LinearMap.congr_fun (koszulDeRhamWeight_comp_weight_pow D x hD hleib j ⟨k, h⟩
          (p - 1)) (koszulCartierProjection D x p k y)
        simp only [LinearMap.comp_apply] at hc
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hc, ih hjk, map_zero, sub_zero]
      · have hjk' : j = ⟨k, h⟩ := Fin.ext hjk
        subst hjk'
        have hw : koszulDeRhamWeight D x ⟨k, h⟩ ((koszulDeRhamWeight D x ⟨k, h⟩ ^ (p - 1))
            (koszulCartierProjection D x p k y)) =
              koszulDeRhamWeight D x ⟨k, h⟩ (koszulCartierProjection D x p k y) := by
          rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le,
            koszulDeRhamWeight_pow_char_of_euler D x p hpK hE]
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hw, sub_self]
    · rw [koszulCartierProjection_succ_of_not_lt D x p h]
      exact ih (by omega)

include hD hleib hp in
theorem sub_koszulCartierProjection_mem_range (k : ℕ) (z : A ⊗[K] CoordExterior K n)
    (hz : koszulDeRhamDiff D z = 0) :
    z - koszulCartierProjection D x p k z ∈ LinearMap.range (koszulDeRhamDiff D) := by
  induction k with
  | zero =>
    rw [koszulCartierProjection, LinearMap.id_apply, sub_self]
    exact Submodule.zero_mem _
  | succ k ih =>
    by_cases h : k < n
    · have hw : koszulDeRhamDiff D (koszulCartierProjection D x p k z) = 0 := by
        have hc := LinearMap.congr_fun (koszulDeRhamDiff_comp_cartierProjection D x hD hleib p k) z
        simp only [LinearMap.comp_apply] at hc
        rw [hc, hz, map_zero]
      have hθ : (koszulDeRhamWeight D x ⟨k, h⟩ ^ (p - 1)) (koszulCartierProjection D x p k z) ∈
          LinearMap.range (koszulDeRhamDiff D) := by
        obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by have := hp.out.two_le; omega⟩
        rw [hq, pow_succ', Module.End.mul_apply]
        apply koszulDeRhamWeight_mem_range D x hleib
        have hc := LinearMap.congr_fun (koszulDeRhamDiff_comp_weight_pow D x hD hleib ⟨k, h⟩ q)
          (koszulCartierProjection D x p k z)
        simp only [LinearMap.comp_apply] at hc
        rw [hc, hw, map_zero]
      have heq : z - koszulCartierProjection D x p (k + 1) z = (z - koszulCartierProjection D x p k z) +
          (koszulDeRhamWeight D x ⟨k, h⟩ ^ (p - 1)) (koszulCartierProjection D x p k z) := by
        rw [koszulCartierProjection_succ_of_lt D x p h, LinearMap.comp_apply, LinearMap.sub_apply,
          LinearMap.id_apply]
        abel
      rw [heq]
      exact Submodule.add_mem _ ih hθ
    · rw [koszulCartierProjection_succ_of_not_lt D x p h]; exact ih

include hD hleib hp hpK hE hker in
/-- An element on which all weights vanish and which is a coboundary is zero. -/
theorem koszulDeRham_weights_eq_zero_of_mem_range (c : A ⊗[K] CoordExterior K n)
    (hc : ∀ j, koszulDeRhamWeight D x j c = 0)
    (hcd : c ∈ LinearMap.range (koszulDeRhamDiff D)) : c = 0 := by
  obtain ⟨y, rfl⟩ := hcd
  rw [← koszulCartierProjection_apply_of_weights D x p n _ hc]
  have hc' := LinearMap.congr_fun (koszulDeRhamDiff_comp_cartierProjection D x hD hleib p n) y
  simp only [LinearMap.comp_apply] at hc'
  rw [← hc']
  exact koszulDeRhamDiff_eq_zero_of_weights D x p hker _
    (fun j => koszulDeRhamWeight_cartierProjection D x hD hleib p hpK hE n y j j.2)

include hD hleib hp hpK hE hker in
/-- **The Cartier decomposition** of the coordinate de Rham complex of an algebra of characteristic
`p` with commuting derivations, coordinates with `∂_i x_j = δ_{ij}`, `(x_j ∂_j)^p = x_j ∂_j` and
`∂_j (1 - (x_j ∂_j)^{p-1}) = 0`. -/
theorem koszulDeRham_cartier_decomposition (z : A ⊗[K] CoordExterior K n)
    (hz : koszulDeRhamDiff D z = 0) :
    ∃! c : A ⊗[K] CoordExterior K n,
      (∀ j, koszulDeRhamWeight D x j c = 0) ∧ z - c ∈ LinearMap.range (koszulDeRhamDiff D) := by
  refine ⟨koszulCartierProjection D x p n z,
    ⟨fun j => koszulDeRhamWeight_cartierProjection D x hD hleib p hpK hE n z j j.2,
      sub_koszulCartierProjection_mem_range D x hD hleib p n z hz⟩, ?_⟩
  rintro c ⟨hc, hzc⟩
  have hdiff : c - koszulCartierProjection D x p n z ∈ LinearMap.range (koszulDeRhamDiff D) := by
    have h := Submodule.sub_mem _ (sub_koszulCartierProjection_mem_range D x hD hleib p n z hz) hzc
    rwa [sub_sub_sub_cancel_left] at h
  have hw : ∀ j, koszulDeRhamWeight D x j (c - koszulCartierProjection D x p n z) = 0 := fun j => by
    rw [map_sub, hc j, koszulDeRhamWeight_cartierProjection D x hD hleib p hpK hE n z j j.2, sub_zero]
  exact sub_eq_zero.mp (koszulDeRham_weights_eq_zero_of_mem_range D x hD hleib p hpK hE hker _ hw hdiff)

end General

section DerivationPower

variable {K : Type u} [CommRing K] {S : Type v} [CommRing S] [Algebra K S]

/-- The Leibniz rule for a `K`-linear map as an identity on `S ⊗ S`. -/
theorem leibniz_comp_mulTensor (E : S →ₗ[K] S) (hE : ∀ a b, E (a * b) = E a * b + a * E b) :
    E ∘ₗ LinearMap.mul' K S =
      LinearMap.mul' K S ∘ₗ (TensorProduct.map E LinearMap.id + TensorProduct.map LinearMap.id E) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.add_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, map_add, hE]

/-- **In characteristic `p` the `p`-th power of a derivation satisfies the Leibniz rule.** -/
theorem derivation_pow_char_leibniz (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) = 0)
    (E : S →ₗ[K] S) (hE : ∀ a b, E (a * b) = E a * b + a * E b) (a b : S) :
    (E ^ p) (a * b) = (E ^ p) a * b + a * (E ^ p) b := by
  have hcomp : ∀ m : ℕ, (E ^ m) ∘ₗ LinearMap.mul' K S =
      LinearMap.mul' K S ∘ₗ (TensorProduct.map E LinearMap.id + TensorProduct.map LinearMap.id E) ^ m := by
    intro m
    induction m with
    | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
    | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc,
        leibniz_comp_mulTensor E hE, LinearMap.comp_assoc, pow_succ', Module.End.mul_eq_comp]
  have hcomm : Commute (TensorProduct.map E (LinearMap.id : S →ₗ[K] S))
      (TensorProduct.map (LinearMap.id : S →ₗ[K] S) E) := by
    change TensorProduct.map _ _ * TensorProduct.map _ _ = TensorProduct.map _ _ * TensorProduct.map _ _
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul]
    rfl
  have hpE : ((p : ℕ) : Module.End K (S ⊗[K] S)) = 0 := by
    rw [← map_natCast (algebraMap K (Module.End K (S ⊗[K] S))), hpK, map_zero]
  have hpow : (TensorProduct.map E LinearMap.id + TensorProduct.map LinearMap.id E) ^ p =
      TensorProduct.map (E ^ p) LinearMap.id + TensorProduct.map LinearMap.id (E ^ p) := by
    rw [hcomm.add_pow_prime_eq hp.out, TensorProduct.map_pow, TensorProduct.map_pow]
    simp only [linearMap_id_pow, hpE, zero_mul, add_zero]
  have h := LinearMap.congr_fun (hcomp p) (a ⊗ₜ b)
  rw [hpow] at h
  simpa only [LinearMap.comp_apply, LinearMap.mul'_apply, LinearMap.add_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, map_add] using h

end DerivationPower

section Etale

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}
  (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)

/-- The coordinate derivations of étale coordinates, as linear maps. -/
noncomputable abbrev etaleCoordPartial (j : Fin n) : S →ₗ[K] S :=
  (etaleCoordinateDerivation y hy j : Derivation K S S)

/-- The étale coordinates. -/
noncomputable abbrev etaleCoordFun (j : Fin n) : S := y (MvPolynomial.X j)

theorem etaleCoordPartial_comm (i j : Fin n) :
    etaleCoordPartial y hy i ∘ₗ etaleCoordPartial y hy j =
      etaleCoordPartial y hy j ∘ₗ etaleCoordPartial y hy i := by
  have h : ⁅etaleCoordinateDerivation y hy i, etaleCoordinateDerivation y hy j⁆ = 0 := by
    apply derivation_ext_etaleCoordinates y hy
    intro k
    rw [Derivation.commutator_apply, etaleCoordinateDerivation_coordinate,
      etaleCoordinateDerivation_coordinate, Derivation.zero_apply]
    split_ifs <;> simp
  refine LinearMap.ext fun a => ?_
  have h2 := congrArg (fun D : Derivation K S S => D a) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  simpa [sub_eq_zero] using h2

theorem etaleCoordPartial_mul (i j : Fin n) (a : S) :
    etaleCoordPartial y hy i (etaleCoordFun y j * a) =
      etaleCoordFun y j * etaleCoordPartial y hy i a + (if i = j then a else 0) := by
  change etaleCoordinateDerivation y hy i (y (MvPolynomial.X j) * a) = _
  rw [Derivation.leibniz, etaleCoordinateDerivation_coordinate, smul_eq_mul, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · have h' : ¬j = i := fun e => h e.symm
    simp [h, h']

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]

theorem etaleEuler_leibniz (j : Fin n) (a b : S) :
    eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j (a * b) =
      eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j a * b +
        a * eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j b := by
  show etaleCoordFun y j * etaleCoordinateDerivation y hy j (a * b) =
    etaleCoordFun y j * etaleCoordinateDerivation y hy j a * b +
      a * (etaleCoordFun y j * etaleCoordinateDerivation y hy j b)
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

include hp in
/-- On étale coordinates `(y_j ∂_j)^p = y_j ∂_j` in characteristic `p`. -/
theorem etaleEuler_pow_char (j : Fin n) :
    eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j ^ p =
      eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j := by
  set E := eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j with hEdef
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have hleibE : ∀ a b : S, E (a * b) = E a * b + a * E b := etaleEuler_leibniz y hy j
  have hleibP := derivation_pow_char_leibniz p hpK E hleibE
  let L : Derivation K S S := Derivation.mk' (E ^ p - E) (fun a b => by
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.sub_apply, hleibP, hleibE,
      smul_eq_mul, smul_eq_mul]
    ring)
  have hval : ∀ k : Fin n, E (etaleCoordFun y k) = if k = j then etaleCoordFun y j else 0 := by
    intro k
    rw [hEdef, eulerOperator_apply]
    change etaleCoordFun y j * etaleCoordinateDerivation y hy j (y (MvPolynomial.X k)) = _
    rw [etaleCoordinateDerivation_coordinate]
    split_ifs with h
    · rw [mul_one]
    · rw [mul_zero]
  have hpowval : ∀ (m : ℕ) (k : Fin n), (E ^ (m + 1)) (etaleCoordFun y k) =
      if k = j then etaleCoordFun y j else 0 := by
    intro m k
    induction m with
    | zero => rw [zero_add, pow_one, hval]
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      split_ifs with h
      · rw [hval j]; simp
      · rw [map_zero]
  have hL : L = 0 := by
    apply derivation_ext_etaleCoordinates y hy
    intro k
    rw [Derivation.zero_apply]
    change (E ^ p - E) (y (MvPolynomial.X k)) = 0
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    rw [LinearMap.sub_apply, hq]
    exact sub_eq_zero.mpr ((hpowval q k).trans (hval k).symm)
  have h2 : (E ^ p - E : S →ₗ[K] S) = 0 := by
    have := congrArg (fun D : Derivation K S S => (D : S →ₗ[K] S)) hL
    simpa [L] using this
  exact sub_eq_zero.mp h2

include hp in
/-- On a domain with étale coordinates, `∂_j (1 - (y_j ∂_j)^{p-1}) = 0`. -/
theorem etalePartial_comp_euler_pow_pred [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (j : Fin n) :
    etaleCoordPartial y hy j ∘ₗ
        (eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j ^ (p - 1)) =
      etaleCoordPartial y hy j := by
  set E := eulerOperator (etaleCoordPartial y hy) (etaleCoordFun y) j with hEdef
  refine LinearMap.ext fun a => ?_
  have hEp : E ^ p = E := etaleEuler_pow_char y hy p j
  have hb : E (a - (E ^ (p - 1)) a) = 0 := by
    rw [map_sub, ← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le,
      hEp, sub_self]
  rw [hEdef, eulerOperator_apply] at hb
  have hb' : etaleCoordPartial y hy j (a - (E ^ (p - 1)) a) = 0 :=
    (mul_eq_zero.mp hb).resolve_left (hy0 j)
  rw [map_sub, sub_eq_zero] at hb'
  rw [LinearMap.comp_apply]
  exact hb'.symm

include hp in
/-- **The Cartier decomposition on an étale coordinate chart.** For a domain `S` over a field of
characteristic `p` with étale coordinates, every cocycle of the coordinate de Rham complex is
uniquely the sum of a coboundary and a form on which all weight operators vanish. -/
theorem etale_cartier_decomposition [IsDomain S] (hy0 : ∀ j : Fin n, etaleCoordFun y j ≠ 0)
    (z : S ⊗[K] CoordExterior K n) (hz : koszulDeRhamDiff (etaleCoordPartial y hy) z = 0) :
    ∃! c : S ⊗[K] CoordExterior K n,
      (∀ j, koszulDeRhamWeight (etaleCoordPartial y hy) (etaleCoordFun y) j c = 0) ∧
        z - c ∈ LinearMap.range (koszulDeRhamDiff (etaleCoordPartial y hy)) :=
  koszulDeRham_cartier_decomposition (etaleCoordPartial y hy) (etaleCoordFun y)
    (etaleCoordPartial_comm y hy) (etaleCoordPartial_mul y hy) p (CharP.cast_eq_zero K p)
    (etaleEuler_pow_char y hy p) (etalePartial_comp_euler_pow_pred y hy p hy0) z hz

end Etale

end MixedFujita
