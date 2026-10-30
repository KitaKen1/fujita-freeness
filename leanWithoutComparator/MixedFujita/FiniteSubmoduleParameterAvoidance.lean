/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SmoothQuotientJacobian

@[expose] public section
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
theorem finiteSubmoduleAvoidance_parameter_polynomial
    {K M ι κ : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Fintype ι] [Fintype κ] (b : Module.Basis ι K M)
    (q : κ → Submodule K M) (m₀ : M) (hm₀ : ∀ k, m₀ ∉ q k) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K,
      MvPolynomial.aeval t p ≠ 0 → ∀ k, (∑ i, t i • b i) ∉ q k := by
  classical
  let Φ (k : κ) : (ι → K) →ₗ[K] M ⧸ q k :=
    (q k).mkQ.comp b.equivFun.symm.toLinearMap
  have hΦ (k : κ) : Φ k ≠ 0 := by
    intro hzero
    have h := LinearMap.congr_fun hzero (b.equivFun m₀)
    change (q k).mkQ (b.equivFun.symm (b.equivFun m₀)) = 0 at h
    rw [b.equivFun.symm_apply_apply] at h
    exact hm₀ k ((Submodule.Quotient.mk_eq_zero (q k)).mp h)
  choose p hp hguard using fun k => exists_mvPolynomial_ne_zero_of_linearMap_ne_zero (Φ k) (hΦ k)
  refine ⟨∏ k, p k, Finset.prod_ne_zero_iff.mpr (fun k _ => hp k), fun t ht k hm => ?_⟩
  rw [map_prod] at ht
  apply hguard k t (Finset.prod_ne_zero_iff.mp ht k (Finset.mem_univ k))
  change (q k).mkQ (b.equivFun.symm t) = 0
  rw [b.equivFun_symm_apply]
  exact (Submodule.Quotient.mk_eq_zero (q k)).mpr hm


end MixedFujita
