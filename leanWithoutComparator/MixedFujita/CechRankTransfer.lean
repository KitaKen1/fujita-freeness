/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FlatComplexHomologyBaseChange
public import MixedFujita.GenericModuleFreeAway
public import Mathlib.RingTheory.Localization.BaseChange

/-!
The rank of the kernel of a flat complex is the same over all fields away from one nonzero
element (step 10, R4-3).

* `exists_ne_zero_forall_free_baseChange`: for finitely many finite modules `M_j` over a
  noetherian domain `R` there is `f ≠ 0` such that `S ⊗[R] M_j` is free over every `R`-algebra `S`
  in which `f` is a unit (generic freeness for each `M_j`, then the product of the elements).
* `exists_ne_zero_finrank_ker_baseChange_eq`: let `C` be a complex of flat `R`-modules, exact after
  any `N ⊗ -` in degrees `≥ m`, with finitely generated cohomology and finitely generated `ker d⁰`.
  There are `f ≠ 0` and `r` such that `dim_k ker(k ⊗ d⁰) = r` for every field `k` over `R` in
  which `f` is a unit. Over `S = R_f` the cohomology in low degrees and `ker d⁰` become free
  (check 513), the boundaries become flat (checks 492, 494), and check 494 compares
  `k ⊗_S ker(S ⊗ d⁰)` with `ker(k ⊗ d⁰)`.

For the Čech complex of the structure sheaf of the closure `T_A` this gives
`dim Γ(T_κ, O) = dim Γ(T_K, O)` for every closed point `κ` of `Spec A` avoiding `f`.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

section GenericFree

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- **Generic freeness for a finite family, in base change form.** -/
theorem exists_ne_zero_forall_free_baseChange {ι : Type*} [Finite ι] (M : ι → Type u)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] [∀ j, Module.Finite R (M j)] :
    ∃ f : R, f ≠ 0 ∧ ∀ (S : Type u) [CommRing S] [Algebra R S], IsUnit (algebraMap R S f) →
      ∀ j, Module.Free S (S ⊗[R] M j) := by
  classical
  have := Fintype.ofFinite ι
  have key : ∀ j, ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r) (Localization.Away r ⊗[R] M j) := by
    intro j
    have : Module.FinitePresentation R (M j) := Module.finitePresentation_of_finite R (M j)
    obtain ⟨r, hr, hfree, -⟩ := finitePresentation_exists_nonzero_free_away R (M j)
    have hbc := IsLocalizedModule.isBaseChange (Submonoid.powers r) (Localization.Away r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) (M j))
    exact ⟨r, hr, Module.Free.of_equiv hbc.equiv.symm⟩
  choose r hr hfree using key
  refine ⟨∏ j, r j, Finset.prod_ne_zero_iff.2 fun j _ => hr j, fun S _ _ hS j => ?_⟩
  have hj : IsUnit (algebraMap R S (r j)) :=
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem r (Finset.mem_univ j))) hS
  let _ : Algebra (Localization.Away (r j)) S := (IsLocalization.Away.lift (r j) hj).toAlgebra
  have : IsScalarTower R (Localization.Away (r j)) S :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq (r j) hj x).symm
  have := hfree j
  exact Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange R (Localization.Away (r j)) S S (M j))

end GenericFree

section Rank

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {C : ℕ → Type u} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hd : ∀ i, (d (i + 1)).comp (d i) = 0)

/-- The kernel of the base change of `d⁰` along `R → S → k` is that along `R → k`. -/
noncomputable def kerBaseChangeCancelEquiv (S : Type u) [CommRing S] [Algebra R S]
    (k : Type u) [CommRing k] [Algebra R k] [Algebra S k] [IsScalarTower R S k] (i : ℕ) :
    LinearMap.ker (((d i).baseChange S).baseChange k) ≃ₗ[k]
      LinearMap.ker ((d i).baseChange k) :=
  LinearEquiv.ofSubmodules (AlgebraTensorModule.cancelBaseChange R S k k (C i)) _ _ (by
    have hcomm : ((d i).baseChange k).comp
        (AlgebraTensorModule.cancelBaseChange R S k k (C i)).toLinearMap =
        (AlgebraTensorModule.cancelBaseChange R S k k (C (i + 1))).toLinearMap.comp
          (((d i).baseChange S).baseChange k) := by
      ext c
      simp
    ext x
    simp only [Submodule.mem_map_equiv, LinearMap.mem_ker]
    have h2 := LinearMap.congr_fun hcomm
      ((AlgebraTensorModule.cancelBaseChange R S k k (C i)).symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h2
    rw [h2, LinearEquiv.map_eq_zero_iff])

/-- **The rank of the kernel of a flat complex over the fields away from one element.** -/
theorem exists_ne_zero_finrank_ker_baseChange_eq (m : ℕ)
    (htop : ∀ (N : Type u) [AddCommGroup N] [Module R N], ∀ i, m ≤ i →
      Function.Exact ((d i).lTensor N) ((d (i + 1)).lTensor N))
    (hfg : ∀ i, Module.Finite R (homologyAt d hd i)) [Module.Finite R (LinearMap.ker (d 0))] :
    ∃ f : R, f ≠ 0 ∧ ∃ r : ℕ, ∀ (k : Type u) [Field k] [Algebra R k],
      IsUnit (algebraMap R k f) → Module.finrank k (LinearMap.ker ((d 0).baseChange k)) = r := by
  classical
  obtain ⟨f₁, hf₁, h₁⟩ := exists_ne_zero_forall_free_baseChange (R := R)
    (fun _ : Unit => LinearMap.ker (d 0))
  obtain ⟨f₂, hf₂, h₂⟩ := exists_ne_zero_forall_free_baseChange (R := R)
    (fun j : Fin (m + 2) => homologyAt d hd j)
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, ?_⟩
  let S := Localization.Away (f₁ * f₂)
  have hS : IsUnit (algebraMap R S (f₁ * f₂)) := IsLocalization.Away.algebraMap_isUnit _
  have hS₁ : IsUnit (algebraMap R S f₁) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right f₁ f₂)) hS
  have hS₂ : IsUnit (algebraMap R S f₂) :=
    isUnit_of_dvd_unit (map_dvd _ (dvd_mul_left f₂ f₁)) hS
  let dS := fun i => (d i).baseChange S
  have hdS := baseChange_comp_eq_zero d hd S
  -- the cohomology in low degrees and the kernel become free over `S`
  have hH : ∀ j, j < m + 2 → Module.Flat S (homologyAt dS hdS j) := by
    intro j hj
    have := h₂ S hS₂ ⟨j, hj⟩
    exact Module.Flat.of_linearEquiv (homologyAtBaseChangeEquiv d hd S j).symm
  have : Module.Free S (LinearMap.ker (dS 0)) := by
    have := h₁ S hS₁ ()
    exact Module.Free.of_equiv (kerBaseChangeLinearEquiv S (d 0))
  have : Module.Finite S (LinearMap.ker (dS 0)) :=
    Module.Finite.equiv (kerBaseChangeLinearEquiv S (d 0))
  -- the boundaries are flat
  have hM : Module.Flat S (LinearMap.range (dS (m + 2))) := by
    refine flat_range_of_exact_lTensor_quotient dS hdS m (fun I => ?_) ?_
    · exact (exact_lTensor_baseChange_iff d S (S ⧸ I) m).2 (htop (S ⧸ I) m le_rfl)
    · exact htop S (m + 1) (by omega)
  have hB := flat_range_of_flat_homologyAt dS hdS (m + 2) hM hH
  have : Module.Flat S (homologyAt dS hdS 0) := hH 0 (by omega)
  have : Module.Flat S (LinearMap.range (dS 0)) := hB 0 (by omega)
  have : Module.Flat S (LinearMap.range (dS 1)) := hB 1 (by omega)
  refine ⟨Module.finrank S (LinearMap.ker (dS 0)), fun k _ _ hk => ?_⟩
  have hkS : IsUnit (algebraMap R k (f₁ * f₂)) := hk
  let _ : Algebra S k := (IsLocalization.Away.lift (f₁ * f₂) hkS).toAlgebra
  have : IsScalarTower R S k :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq (f₁ * f₂) hkS x).symm
  have : Nontrivial S := RingHom.domain_nontrivial (algebraMap S k)
  rw [← (kerBaseChangeCancelEquiv d S k 0).finrank_eq]
  exact finrank_ker_baseChange dS hdS k

end Rank

end MixedFujita
