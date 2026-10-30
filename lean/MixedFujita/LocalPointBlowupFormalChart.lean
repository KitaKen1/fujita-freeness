/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalPointBlowupLeadingRestriction

/-! A map from the actual chart R[m/x_k] to the formal point-blow-up chart.
The map is constructed by Hironaka's lifting lemma, using the actual generating
parameters of m. It sends every polynomial chart coordinate to the corresponding
power-series coordinate. -/

@[expose] public section
open AlgebraicGeometry
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R] [IsLocalRing R] {n : ℕ}

set_option maxHeartbeats 400000 in
theorem localPointBlowup_exists_formalChart
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span (Set.range (fun i => ψ (MvPolynomial.X i))))
    (hψ : ∀ i, ψ (MvPolynomial.X i) ∈ IsLocalRing.maximalIdeal R) (k : Fin n) :
    ∃ ν : affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k)) →+*
        MvPowerSeries (Fin n) K,
      (∀ r, ν (algebraMap R _ r) =
        MvPowerSeries.subst (monomialSubstVars (pointBlowupChart k)) (T r)) ∧
      ∀ g, ν (localPointBlowupPolynomialMap _ ψ hψ k g) = (g : MvPowerSeries (Fin n) K) := by
  classical
  let S := MvPowerSeries (Fin n) K
  let σ := MvPowerSeries.substAlgHom (R := K)
    (hasSubst_monomialSubstVars (K := K) (pointBlowupChart_row_ne_zero k))
  let β : R →+* S := (σ.comp T).toRingHom
  have hβX (i : Fin n) : β (ψ (MvPolynomial.X i)) =
      if i = k then MvPowerSeries.X k else MvPowerSeries.X i * MvPowerSeries.X k := by
    change σ (T (ψ (MvPolynomial.X i))) = _
    rw [hX, MvPowerSeries.substAlgHom_X, monomialSubstVars_pointBlowupChart]
  have hβk : β (ψ (MvPolynomial.X k)) = MvPowerSeries.X k := by simpa using hβX k
  have hI : (IsLocalRing.maximalIdeal R).map β = Ideal.span {β (ψ (MvPolynomial.X k))} := by
    apply le_antisymm
    · rw [hmax, Ideal.map_span, hβk, Ideal.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      rw [hβX]
      split_ifs
      · exact Ideal.subset_span (Set.mem_singleton _)
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem β (hψ k)
  have hreg : β (ψ (MvPolynomial.X k)) ∈ nonZeroDivisors S := by
    rw [hβk]
    exact MvPowerSeries.X_mem_nonZeroDivisors
  let ν := affineBlowUpAlgebra.lift β (hψ k) hreg hI
  have hν (r : R) : ν (algebraMap R _ r) = β r :=
    RingHom.congr_fun (affineBlowUpAlgebra.lift_comp_algebraMap β (hψ k) hreg hI) r
  let τ := localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k
  have hνX (i : Fin n) : ν (τ (MvPolynomial.X i)) = MvPowerSeries.X i := by
    by_cases hi : i = k
    · subst i
      change ν (localPointBlowupPolynomialMap _ ψ hψ k (MvPolynomial.X k)) = _
      rw [localPointBlowupPolynomialMap_X_self, hν, hβk]
    · have he := congrArg ν (affineBlowup_frac_mul_exceptional
          (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k)) (hψ i))
      rw [map_mul, hν, hν, hβk, hβX, ite_eq_right hi] at he
      change ν (localPointBlowupPolynomialMap _ ψ hψ k (MvPolynomial.X i)) = _
      rw [localPointBlowupPolynomialMap_X_other _ ψ hψ k i hi]
      have hc : IsRightRegular (MvPowerSeries.X k : S) :=
        (isRegular_iff_mem_nonZeroDivisors.mpr
          (show (MvPowerSeries.X k : S) ∈ nonZeroDivisors S from
            MvPowerSeries.X_mem_nonZeroDivisors)).right
      exact hc he
  refine ⟨ν, ?_, ?_⟩
  · intro r
    rw [hν]
    exact MvPowerSeries.substAlgHom_apply
      (hasSubst_monomialSubstVars (K := K) (pointBlowupChart_row_ne_zero k)) (T r)
  intro g
  change ν (τ g) = (g : MvPowerSeries (Fin n) K)
  induction g using MvPolynomial.induction_on with
  | C c =>
    change ν (localPointBlowupPolynomialMap _ ψ hψ k (MvPolynomial.C c)) = _
    rw [localPointBlowupPolynomialMap_C, hν]
    rw [MvPolynomial.coe_C]
    exact (σ.comp T).commutes c
  | add g h hg hh => simp only [map_add, MvPolynomial.coe_add, hg, hh]
  | mul_X g i hg => simp only [map_mul, MvPolynomial.coe_mul, MvPolynomial.coe_X, hg, hνX]

end MixedFujita
