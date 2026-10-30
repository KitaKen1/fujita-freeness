/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FlatComplexBaseChange

/-!
Base change of the kernel of a complex of flat modules (step 10, R4).

Let `C` be a complex of flat modules whose boundary at the top is flat and whose cohomology
below the top is flat. Then every boundary is flat (`flat_range_of_flat_homologyAt`). For every
module `N`, the kernel of `N ⊗ d⁰` is `N ⊗ ker d⁰` (`lTensor_ker_subtype_injective`,
`range_lTensor_ker_subtype`). Over an algebra `k` this is an isomorphism of `k`-modules
(`kerBaseChangeEquiv`), so a free kernel of rank `r` stays of rank `r` after the base change
(`finrank_ker_baseChange`).

This is the degree-zero cohomology and base change used to show that the special fibre is
connected: there the kernel is the space of global functions.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

variable {R : Type u} [CommRing R] {C : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hd : ∀ i, (d (i + 1)).comp (d i) = 0)

/-- **A boundary is flat if the cycles and the cohomology there are flat.** -/
theorem flat_range_of_flat_ker_of_flat_homologyAt (i : ℕ)
    [Module.Flat R (LinearMap.ker (d (i + 1)))] [Module.Flat R (homologyAt d hd i)] :
    Module.Flat R (LinearMap.range (d i)) := by
  have h1 : Module.Flat R (LinearMap.ker (LinearMap.range (cycleRestrict d hd i)).mkQ) :=
    flat_ker_of_surjective _ (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ] at h1
  have hmap : (LinearMap.range (cycleRestrict d hd i)).map (LinearMap.ker (d (i + 1))).subtype =
      LinearMap.range (d i) := by
    rw [← LinearMap.range_comp, subtype_comp_cycleRestrict]
  exact Module.Flat.of_linearEquiv
    (((LinearMap.range (cycleRestrict d hd i)).equivMapOfInjective _
      Subtype.val_injective).trans (LinearEquiv.ofEq _ _ hmap)).symm

/-- **Every boundary is flat** below a flat boundary, if the cohomology there is flat. -/
theorem flat_range_of_flat_homologyAt [∀ i, Module.Flat R (C i)] (M : ℕ)
    (hM : Module.Flat R (LinearMap.range (d M)))
    (hH : ∀ i, i < M → Module.Flat R (homologyAt d hd i)) :
    ∀ i, i ≤ M → Module.Flat R (LinearMap.range (d i)) := by
  intro i hiM
  induction h : M - i using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    rcases Nat.eq_or_lt_of_le hiM with rfl | hlt
    · exact hM
    · have h1 : Module.Flat R (LinearMap.range (d (i + 1))) :=
        ih (M - (i + 1)) (by omega) (i + 1) hlt rfl
      have h2 : Module.Flat R (LinearMap.ker (d (i + 1)).rangeRestrict) :=
        flat_ker_of_surjective _ (d (i + 1)).surjective_rangeRestrict
      rw [LinearMap.ker_rangeRestrict] at h2
      have := hH i hlt
      exact flat_range_of_flat_ker_of_flat_homologyAt d hd i

/-- **The kernel stays a submodule after `N ⊗ -`** if the first boundary is flat. -/
theorem lTensor_ker_subtype_injective (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R (LinearMap.range (d 0))] :
    Function.Injective ((LinearMap.ker (d 0)).subtype.lTensor N) :=
  LinearMap.lTensor_injective_of_exact_of_flat (d 0).rangeRestrict (d 0).surjective_rangeRestrict
    (LinearMap.ker (d 0)).subtype Subtype.val_injective (by
      rw [← LinearMap.ker_rangeRestrict]
      exact LinearMap.exact_subtype_ker_map _) N

/-- **The kernel of `N ⊗ d⁰` is `N ⊗ ker d⁰`** if the first cohomology and the second boundary are
flat. -/
theorem range_lTensor_ker_subtype (N : Type*) [AddCommGroup N] [Module R N]
    [Module.Flat R (homologyAt d hd 0)] [Module.Flat R (LinearMap.range (d 1))] :
    LinearMap.range ((LinearMap.ker (d 0)).subtype.lTensor N) =
      LinearMap.ker ((d 0).lTensor N) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have h0 : (d 0).comp (LinearMap.ker (d 0)).subtype = 0 := by
      ext z
      exact z.2
    rw [h0, LinearMap.lTensor_zero, LinearMap.zero_apply]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    -- the factorization `C⁰ → B¹ → Z¹ → C¹` of `d⁰`
    let B := LinearMap.range (cycleRestrict d hd 0)
    let ρ := (cycleRestrict d hd 0).rangeRestrict
    have hfac : ((LinearMap.ker (d 1)).subtype.comp B.subtype).comp ρ = d 0 := by
      ext c
      rfl
    have hB : Function.Injective (B.subtype.lTensor N) :=
      LinearMap.lTensor_injective_of_exact_of_flat B.mkQ B.mkQ_surjective B.subtype
        Subtype.val_injective (LinearMap.exact_subtype_mkQ B) N
    have hZ : Function.Injective ((LinearMap.ker (d 1)).subtype.lTensor N) :=
      LinearMap.lTensor_injective_of_exact_of_flat (d 1).rangeRestrict
        (d 1).surjective_rangeRestrict (LinearMap.ker (d 1)).subtype Subtype.val_injective (by
          rw [← LinearMap.ker_rangeRestrict]
          exact LinearMap.exact_subtype_ker_map _) N
    have hρ : ρ.lTensor N x = 0 := by
      apply hB
      apply hZ
      rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp, hfac, hx]
    obtain ⟨t, ht⟩ := (lTensor_exact N (LinearMap.exact_subtype_ker_map ρ)
      (cycleRestrict d hd 0).surjective_rangeRestrict x).mp hρ
    have hker : LinearMap.ker ρ = LinearMap.ker (d 0) := by
      rw [LinearMap.ker_rangeRestrict]
      exact LinearMap.ker_codRestrict _ _ _
    have hsub : (LinearMap.ker (d 0)).subtype ∘ₗ (LinearEquiv.ofEq _ _ hker).toLinearMap =
        (LinearMap.ker ρ).subtype := by
      ext
      rfl
    refine ⟨((LinearEquiv.ofEq _ _ hker).toLinearMap.lTensor N) t, ?_⟩
    rw [← ht, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hsub]

section BaseChange

variable (k : Type w) [CommRing k] [Algebra R k]

/-- **The base change of the kernel is the kernel of the base change**, if the first cohomology
and the first two boundaries are flat. -/
noncomputable def kerBaseChangeEquiv [Module.Flat R (homologyAt d hd 0)]
    [Module.Flat R (LinearMap.range (d 0))] [Module.Flat R (LinearMap.range (d 1))] :
    k ⊗[R] LinearMap.ker (d 0) ≃ₗ[k] LinearMap.ker ((d 0).baseChange k) :=
  (LinearEquiv.ofInjective ((LinearMap.ker (d 0)).subtype.baseChange k)
    (lTensor_ker_subtype_injective d k)).trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      exact SetLike.ext_iff.mp (range_lTensor_ker_subtype d hd k) x))

/-- **A free kernel keeps its rank after the base change.** -/
theorem finrank_ker_baseChange [Nontrivial R] [Nontrivial k] [Module.Flat R (homologyAt d hd 0)]
    [Module.Flat R (LinearMap.range (d 0))] [Module.Flat R (LinearMap.range (d 1))]
    [Module.Free R (LinearMap.ker (d 0))] [Module.Finite R (LinearMap.ker (d 0))] :
    Module.finrank k (LinearMap.ker ((d 0).baseChange k)) =
      Module.finrank R (LinearMap.ker (d 0)) := by
  rw [← (kerBaseChangeEquiv d hd k).finrank_eq, Module.finrank_baseChange]

/-- **Over a flat algebra the base change of the kernel is always the kernel of the base
change.** -/
noncomputable def kerFlatBaseChangeEquiv [Module.Flat R k] :
    k ⊗[R] LinearMap.ker (d 0) ≃ₗ[k] LinearMap.ker ((d 0).baseChange k) :=
  (LinearEquiv.ofInjective ((LinearMap.ker (d 0)).subtype.baseChange k)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      exact ((Module.Flat.lTensor_exact k (LinearMap.exact_subtype_ker_map (d 0))) x).symm))

/-- **Over a flat algebra a free kernel keeps its rank.** -/
theorem finrank_ker_flatBaseChange [Nontrivial R] [Nontrivial k] [Module.Flat R k]
    [Module.Free R (LinearMap.ker (d 0))] [Module.Finite R (LinearMap.ker (d 0))] :
    Module.finrank k (LinearMap.ker ((d 0).baseChange k)) =
      Module.finrank R (LinearMap.ker (d 0)) := by
  rw [← (kerFlatBaseChangeEquiv d k).finrank_eq, Module.finrank_baseChange]

end BaseChange

end MixedFujita
