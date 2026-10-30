/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartCartierDecomposition

/-!
The Cartier decomposition of mixed coordinate de Rham models (step 10, R2).

The coordinate de Rham model `A ⊗ ⋀Kⁿ` with commuting operators `D_j` and the homotopies
`h_j = x_j ⊗ ι_j` (check 395) satisfies a mixed Cartan formula when
`D_i (x_j a) = x_j D_i a + δ_{ij} c_j a` for scalars `c_j` (`mixedKoszul_cartan`):
`d h_j + h_j d = θ_j` with the mixed weight `θ_j = x_j D_j ⊗ 1 + c_j (1 ⊗ e_j ∧ ι_j)`
(`mixedKoszulWeight`). Ordinary directions have `c_j = 1` (`D_j = ∂_j`, `x_j = y_j`, check 395).
Logarithmic directions of a twisted logarithmic de Rham complex have `c_j = 0`
(`D_j = y_j ∂_j − r_j`, `x_j = 1`).

The argument of check 397 goes through. The weights commute with `d` and with each other, and
`θ_j^p = θ_j` when `(x_j D_j)^p = x_j D_j` and `c_j^p = c_j` (`mixedKoszulWeight_pow_of_euler`). Every
cocycle is uniquely the sum of a form with all weights zero and a coboundary
(`mixedKoszul_cartier_decomposition`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section Mixed

variable {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] {n : ℕ}
  (D : Fin n → A →ₗ[K] A) (x : Fin n → A) (c : Fin n → K)

/-- **The mixed weight operator** `θ_j = x_j D_j ⊗ 1 + c_j (1 ⊗ e_j ∧ ι_j)`. -/
noncomputable def mixedKoszulWeight (j : Fin n) :
    A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n :=
  TensorProduct.map (eulerOperator D x j) LinearMap.id +
    c j • TensorProduct.map LinearMap.id (coordWedge K j ∘ₗ coordContract j)

theorem mixedKoszulWeight_eq_add (j : Fin n) :
    mixedKoszulWeight D x c j = TensorProduct.map (eulerOperator D x j) LinearMap.id +
      c j • TensorProduct.map LinearMap.id (coordWedge K j ∘ₗ coordContract j) := rfl

/-- **The mixed Cartan formula** `d h_j + h_j d = θ_j`, for commuting `K`-linear maps `D_i` with
`D_i (x_j a) = x_j D_i a + δ_{ij} c_j a`. -/
theorem mixedKoszul_cartan
    (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then c j • a else 0))
    (j : Fin n) :
    koszulDeRhamDiff D ∘ₗ koszulDeRhamHomotopy x j +
        koszulDeRhamHomotopy x j ∘ₗ koszulDeRhamDiff D = mixedKoszulWeight D x c j := by
  classical
  apply TensorProduct.ext'
  intro a e
  simp only [LinearMap.add_apply, LinearMap.comp_apply, koszulDeRhamHomotopy, mixedKoszulWeight,
    TensorProduct.map_tmul, LinearMap.mulLeft_apply, koszulDeRhamDiff_tmul, map_sum,
    LinearMap.id_apply, coordWedge_apply, LinearMap.smul_apply, eulerOperator_apply]
  simp_rw [hleib, coordContract_coordVector_mul]
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin n,
      (x j * D i a + (if i = j then c j • a else 0)) ⊗ₜ[K] (coordVector K i * coordContract j e) +
        (x j * D i a) ⊗ₜ[K] ((Pi.single i (1 : K) : Fin n → K) j • e -
          coordVector K i * coordContract j e) =
      if i = j then (c j • a) ⊗ₜ[K] (coordVector K j * coordContract j e) + (x j * D j a) ⊗ₜ[K] e
      else 0 := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, Pi.single_eq_same, one_smul, TensorProduct.add_tmul,
        TensorProduct.tmul_sub]
      abel
    · have hji : (Pi.single i (1 : K) : Fin n → K) j = 0 := Pi.single_eq_of_ne' hij 1
      simp only [hij, ite_false, add_zero, hji, zero_smul, zero_sub, TensorProduct.tmul_neg,
        add_neg_cancel]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, ite_true, ← TensorProduct.smul_tmul']
  abel

variable (hD : ∀ i j, D i ∘ₗ D j = D j ∘ₗ D i)
  (hleib : ∀ i j (a : A), D i (x j * a) = x j * D i a + (if i = j then c j • a else 0))

include hD hleib in
/-- The mixed weight operators commute with the differential. -/
theorem mixedKoszulDiff_comp_weight (j : Fin n) :
    koszulDeRhamDiff D ∘ₗ mixedKoszulWeight D x c j =
      mixedKoszulWeight D x c j ∘ₗ koszulDeRhamDiff D := by
  have hdd := koszulDeRhamDiff_comp_self D hD
  have hdd' : ∀ f : A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n,
      koszulDeRhamDiff D ∘ₗ (koszulDeRhamDiff D ∘ₗ f) = 0 := fun f => by
    rw [← LinearMap.comp_assoc, hdd, LinearMap.zero_comp]
  rw [← mixedKoszul_cartan D x c hleib j, LinearMap.comp_add, LinearMap.add_comp]
  simp only [LinearMap.comp_assoc, hdd, hdd', LinearMap.comp_zero, zero_add, add_zero]

include hleib in
/-- The mixed weight operators send cocycles to coboundaries. -/
theorem mixedKoszulWeight_mem_range (j : Fin n) (z : A ⊗[K] CoordExterior K n)
    (hz : koszulDeRhamDiff D z = 0) :
    mixedKoszulWeight D x c j z ∈ LinearMap.range (koszulDeRhamDiff D) := by
  refine ⟨koszulDeRhamHomotopy x j z, ?_⟩
  have h := LinearMap.congr_fun (mixedKoszul_cartan D x c hleib j) z
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero] using h

include hD hleib in
/-- The Euler operators commute. -/
theorem eulerOperator_comm_of_mixed (i j : Fin n) :
    eulerOperator D x i ∘ₗ eulerOperator D x j = eulerOperator D x j ∘ₗ eulerOperator D x i := by
  refine LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, eulerOperator_apply, hleib]
  have h1 : D i (D j a) = D j (D i a) := LinearMap.congr_fun (hD i j) a
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬j = i := fun h => hij h.symm
    simp only [hij, hji, ite_false, add_zero, h1]
    ring

include hD hleib in
theorem mixedKoszulWeight_comm (i j : Fin n) :
    mixedKoszulWeight D x c i ∘ₗ mixedKoszulWeight D x c j =
      mixedKoszulWeight D x c j ∘ₗ mixedKoszulWeight D x c i := by
  simp only [mixedKoszulWeight_eq_add, LinearMap.comp_add, LinearMap.add_comp,
    LinearMap.comp_smul, LinearMap.smul_comp, ← TensorProduct.map_comp, LinearMap.id_comp,
    LinearMap.comp_id, eulerOperator_comm_of_mixed D x c hD hleib i j, coordWedgeContract_comm i j]
  simp only [smul_add, smul_smul, mul_comm (c i) (c j)]
  abel

include hD hleib in
theorem mixedKoszulDiff_comp_weight_pow (j : Fin n) (m : ℕ) :
    koszulDeRhamDiff D ∘ₗ (mixedKoszulWeight D x c j ^ m) =
      (mixedKoszulWeight D x c j ^ m) ∘ₗ koszulDeRhamDiff D := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
      mixedKoszulDiff_comp_weight D x c hD hleib, ← LinearMap.comp_assoc]

include hD hleib in
theorem mixedKoszulWeight_comp_weight_pow (i j : Fin n) (m : ℕ) :
    mixedKoszulWeight D x c i ∘ₗ (mixedKoszulWeight D x c j ^ m) =
      (mixedKoszulWeight D x c j ^ m) ∘ₗ mixedKoszulWeight D x c i := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
  | succ m ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc,
      mixedKoszulWeight_comm D x c hD hleib, ← LinearMap.comp_assoc]

omit hD hleib in
/-- In characteristic `p`, `θ_j^p = θ_j` when `(x_j D_j)^p = x_j D_j` and `c_j^p = c_j`. -/
theorem mixedKoszulWeight_pow_of_euler (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) = 0)
    (j : Fin n) (hE : eulerOperator D x j ^ p = eulerOperator D x j) (hc : c j ^ p = c j) :
    mixedKoszulWeight D x c j ^ p = mixedKoszulWeight D x c j := by
  rw [mixedKoszulWeight_eq_add,
    ((commute_eulerPart_wedgePart D x j).smul_right (c j)).add_pow_prime_eq hp.out,
    TensorProduct.map_pow, smul_pow, TensorProduct.map_pow, hE, linearMap_id_pow,
    linearMap_id_pow, hc]
  have hY : (coordWedge K j ∘ₗ coordContract (K := K) j) ^ p =
      coordWedge K j ∘ₗ coordContract j := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.out.pos).symm⟩
    rw [hq, coordWedgeContract_pow_succ]
  have hpE : ((p : ℕ) : Module.End K (A ⊗[K] CoordExterior K n)) = 0 := by
    rw [← map_natCast (algebraMap K (Module.End K (A ⊗[K] CoordExterior K n))), hpK, map_zero]
  simp only [hY, hpE, zero_mul, add_zero]

omit hD hleib in
/-- The term `D_i ⊗ (e_i ∧ -)` of the differential absorbs powers of the `i`-th mixed weight into
its Euler part. -/
theorem partialWedge_comp_mixedWeight_pow (i : Fin n) (k : ℕ) :
    TensorProduct.map (D i) (coordWedge K i) ∘ₗ mixedKoszulWeight D x c i ^ k =
      TensorProduct.map (D i ∘ₗ eulerOperator D x i ^ k) (coordWedge K i) := by
  induction k with
  | zero => simp only [pow_zero, Module.End.one_eq_id, LinearMap.comp_id]
  | succ k ih =>
    rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, mixedKoszulWeight_eq_add,
      LinearMap.comp_add, LinearMap.comp_smul, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
      coordWedge_comp_wedgeContract, TensorProduct.map_zero_right, smul_zero, add_zero,
      LinearMap.comp_id, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]

omit hD hleib in
/-- The composite of the idempotents `1 - θ_j^{p-1}` over the first `k` coordinates. -/
noncomputable def mixedKoszulCartierProjection (p : ℕ) (k : ℕ) :
    A ⊗[K] CoordExterior K n →ₗ[K] A ⊗[K] CoordExterior K n :=
  match k with
  | 0 => LinearMap.id
  | k + 1 =>
    if h : k < n then
      (LinearMap.id - mixedKoszulWeight D x c ⟨k, h⟩ ^ (p - 1)) ∘ₗ mixedKoszulCartierProjection p k
    else mixedKoszulCartierProjection p k

omit hD hleib in
theorem mixedKoszulCartierProjection_succ_of_lt (p : ℕ) {k : ℕ} (h : k < n) :
    mixedKoszulCartierProjection D x c p (k + 1) =
      (LinearMap.id - mixedKoszulWeight D x c ⟨k, h⟩ ^ (p - 1)) ∘ₗ
        mixedKoszulCartierProjection D x c p k := by
  simp only [mixedKoszulCartierProjection, h, dite_true]

omit hD hleib in
theorem mixedKoszulCartierProjection_succ_of_not_lt (p : ℕ) {k : ℕ} (h : ¬k < n) :
    mixedKoszulCartierProjection D x c p (k + 1) = mixedKoszulCartierProjection D x c p k := by
  simp only [mixedKoszulCartierProjection, h, dite_false]

include hD hleib in
theorem mixedKoszulDiff_comp_cartierProjection (p : ℕ) (k : ℕ) :
    koszulDeRhamDiff D ∘ₗ mixedKoszulCartierProjection D x c p k =
      mixedKoszulCartierProjection D x c p k ∘ₗ koszulDeRhamDiff D := by
  induction k with
  | zero => rw [mixedKoszulCartierProjection, LinearMap.comp_id, LinearMap.id_comp]
  | succ k ih =>
    by_cases h : k < n
    · refine LinearMap.ext fun z => ?_
      have h1 := LinearMap.congr_fun ih z
      have h2 := LinearMap.congr_fun
        (mixedKoszulDiff_comp_weight_pow D x c hD hleib ⟨k, h⟩ (p - 1))
        (mixedKoszulCartierProjection D x c p k z)
      simp only [LinearMap.comp_apply] at h1 h2
      simp only [LinearMap.comp_apply, mixedKoszulCartierProjection_succ_of_lt D x c p h,
        LinearMap.sub_apply, LinearMap.id_apply, map_sub, h2, h1]
    · rw [mixedKoszulCartierProjection_succ_of_not_lt D x c p h, ih]

variable (p : ℕ) [hp : Fact p.Prime] (hpK : (p : K) = 0)
  (hE : ∀ j, eulerOperator D x j ^ p = eulerOperator D x j) (hc : ∀ j, c j ^ p = c j)
  (hker : ∀ j, D j ∘ₗ (eulerOperator D x j ^ (p - 1)) = D j)

include hp hpK hE hc in
theorem mixedKoszulWeight_pow_char (j : Fin n) :
    mixedKoszulWeight D x c j ^ p = mixedKoszulWeight D x c j :=
  mixedKoszulWeight_pow_of_euler D x c p hpK j (hE j) (hc j)

include hp in
theorem mixedKoszulWeight_pow_pred_eq_zero (j : Fin n) (z : A ⊗[K] CoordExterior K n)
    (hz : mixedKoszulWeight D x c j z = 0) : (mixedKoszulWeight D x c j ^ (p - 1)) z = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by omega⟩
  rw [hq, pow_succ, Module.End.mul_apply, hz, map_zero]

include hp hker in
/-- `d` vanishes where all mixed weights vanish. -/
theorem mixedKoszulDiff_eq_zero_of_weights (z : A ⊗[K] CoordExterior K n)
    (hz : ∀ j, mixedKoszulWeight D x c j z = 0) : koszulDeRhamDiff D z = 0 := by
  rw [koszulDeRhamDiff, LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h := LinearMap.congr_fun (partialWedge_comp_mixedWeight_pow D x c i (p - 1)) z
  rw [LinearMap.comp_apply, mixedKoszulWeight_pow_pred_eq_zero D x c p i z (hz i), map_zero,
    hker i] at h
  exact h.symm

include hp in
theorem mixedKoszulCartierProjection_apply_of_weights (k : ℕ) (z : A ⊗[K] CoordExterior K n)
    (hz : ∀ j, mixedKoszulWeight D x c j z = 0) : mixedKoszulCartierProjection D x c p k z = z := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases h : k < n
    · rw [mixedKoszulCartierProjection_succ_of_lt D x c p h, LinearMap.comp_apply, ih,
        LinearMap.sub_apply, LinearMap.id_apply,
        mixedKoszulWeight_pow_pred_eq_zero D x c p _ z (hz _), sub_zero]
    · rw [mixedKoszulCartierProjection_succ_of_not_lt D x c p h, ih]

include hD hleib hp hpK hE hc in
theorem mixedKoszulWeight_cartierProjection (k : ℕ) (y : A ⊗[K] CoordExterior K n) (j : Fin n)
    (hj : (j : ℕ) < k) : mixedKoszulWeight D x c j (mixedKoszulCartierProjection D x c p k y) = 0 := by
  induction k with
  | zero => exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    by_cases h : k < n
    · rw [mixedKoszulCartierProjection_succ_of_lt D x c p h, LinearMap.comp_apply]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
      · have hcomm := LinearMap.congr_fun (mixedKoszulWeight_comp_weight_pow D x c hD hleib j
          ⟨k, h⟩ (p - 1)) (mixedKoszulCartierProjection D x c p k y)
        simp only [LinearMap.comp_apply] at hcomm
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hcomm, ih hjk, map_zero, sub_zero]
      · have hjk' : j = ⟨k, h⟩ := Fin.ext hjk
        subst hjk'
        have hw : mixedKoszulWeight D x c ⟨k, h⟩ ((mixedKoszulWeight D x c ⟨k, h⟩ ^ (p - 1))
            (mixedKoszulCartierProjection D x c p k y)) =
              mixedKoszulWeight D x c ⟨k, h⟩ (mixedKoszulCartierProjection D x c p k y) := by
          rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le,
            mixedKoszulWeight_pow_char D x c p hpK hE hc]
        rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hw, sub_self]
    · rw [mixedKoszulCartierProjection_succ_of_not_lt D x c p h]
      exact ih (by omega)

include hD hleib hp in
theorem sub_mixedKoszulCartierProjection_mem_range (k : ℕ) (z : A ⊗[K] CoordExterior K n)
    (hz : koszulDeRhamDiff D z = 0) :
    z - mixedKoszulCartierProjection D x c p k z ∈ LinearMap.range (koszulDeRhamDiff D) := by
  induction k with
  | zero =>
    rw [mixedKoszulCartierProjection, LinearMap.id_apply, sub_self]
    exact Submodule.zero_mem _
  | succ k ih =>
    by_cases h : k < n
    · have hw : koszulDeRhamDiff D (mixedKoszulCartierProjection D x c p k z) = 0 := by
        have hcomm := LinearMap.congr_fun
          (mixedKoszulDiff_comp_cartierProjection D x c hD hleib p k) z
        simp only [LinearMap.comp_apply] at hcomm
        rw [hcomm, hz, map_zero]
      have hθ : (mixedKoszulWeight D x c ⟨k, h⟩ ^ (p - 1))
          (mixedKoszulCartierProjection D x c p k z) ∈ LinearMap.range (koszulDeRhamDiff D) := by
        obtain ⟨q, hq⟩ : ∃ q, p - 1 = q + 1 := ⟨p - 2, by have := hp.out.two_le; omega⟩
        rw [hq, pow_succ', Module.End.mul_apply]
        apply mixedKoszulWeight_mem_range D x c hleib
        have hcomm := LinearMap.congr_fun
          (mixedKoszulDiff_comp_weight_pow D x c hD hleib ⟨k, h⟩ q)
          (mixedKoszulCartierProjection D x c p k z)
        simp only [LinearMap.comp_apply] at hcomm
        rw [hcomm, hw, map_zero]
      have heq : z - mixedKoszulCartierProjection D x c p (k + 1) z =
          (z - mixedKoszulCartierProjection D x c p k z) +
            (mixedKoszulWeight D x c ⟨k, h⟩ ^ (p - 1)) (mixedKoszulCartierProjection D x c p k z) := by
        rw [mixedKoszulCartierProjection_succ_of_lt D x c p h, LinearMap.comp_apply,
          LinearMap.sub_apply, LinearMap.id_apply]
        abel
      rw [heq]
      exact Submodule.add_mem _ ih hθ
    · rw [mixedKoszulCartierProjection_succ_of_not_lt D x c p h]; exact ih

include hD hleib hp hpK hE hc hker in
/-- An element on which all mixed weights vanish and which is a coboundary is zero. -/
theorem mixedKoszul_weights_eq_zero_of_mem_range (z : A ⊗[K] CoordExterior K n)
    (hzw : ∀ j, mixedKoszulWeight D x c j z = 0)
    (hzd : z ∈ LinearMap.range (koszulDeRhamDiff D)) : z = 0 := by
  obtain ⟨y, rfl⟩ := hzd
  rw [← mixedKoszulCartierProjection_apply_of_weights D x c p n _ hzw]
  have hcomm := LinearMap.congr_fun (mixedKoszulDiff_comp_cartierProjection D x c hD hleib p n) y
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm]
  exact mixedKoszulDiff_eq_zero_of_weights D x c p hker _
    (fun j => mixedKoszulWeight_cartierProjection D x c hD hleib p hpK hE hc n y j j.2)

include hD hleib hp hpK hE hc hker in
/-- **The Cartier decomposition of a mixed model**: every cocycle is uniquely the sum of a form
on which all mixed weights vanish and a coboundary. -/
theorem mixedKoszul_cartier_decomposition (z : A ⊗[K] CoordExterior K n)
    (hz : koszulDeRhamDiff D z = 0) :
    ∃! w : A ⊗[K] CoordExterior K n,
      (∀ j, mixedKoszulWeight D x c j w = 0) ∧ z - w ∈ LinearMap.range (koszulDeRhamDiff D) := by
  refine ⟨mixedKoszulCartierProjection D x c p n z,
    ⟨fun j => mixedKoszulWeight_cartierProjection D x c hD hleib p hpK hE hc n z j j.2,
      sub_mixedKoszulCartierProjection_mem_range D x c hD hleib p n z hz⟩, ?_⟩
  rintro w ⟨hw, hzw⟩
  have hdiff : w - mixedKoszulCartierProjection D x c p n z ∈
      LinearMap.range (koszulDeRhamDiff D) := by
    have h := Submodule.sub_mem _ (sub_mixedKoszulCartierProjection_mem_range D x c hD hleib p n z
      hz) hzw
    rwa [sub_sub_sub_cancel_left] at h
  have hw' : ∀ j, mixedKoszulWeight D x c j (w - mixedKoszulCartierProjection D x c p n z) = 0 :=
    fun j => by
      rw [map_sub, hw j, mixedKoszulWeight_cartierProjection D x c hD hleib p hpK hE hc n z j j.2,
        sub_zero]
  exact sub_eq_zero.mp
    (mixedKoszul_weights_eq_zero_of_mem_range D x c hD hleib p hpK hE hc hker _ hw' hdiff)

end Mixed

end MixedFujita
