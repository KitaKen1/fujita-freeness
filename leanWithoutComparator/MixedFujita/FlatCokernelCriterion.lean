/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
A cokernel of a map into a flat module is flat when tensoring the first
map with every quotient R/I is injective. Checking quotient rings, rather
than all modules, is enough: use the ideal criterion for flatness and a
diagram chase in the two right-exact tensor sequences.
-/

@[expose] public section

namespace MixedFujita

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module R N] [Module R P]

theorem flat_cokernel_of_quotient_tensor_injective [Module.Flat R N]
    (g : M →ₗ[R] N) (f : N →ₗ[R] P) (hex : Function.Exact g f)
    (hf : Function.Surjective f)
    (hg : ∀ I : Ideal R, Function.Injective (g.lTensor (R ⧸ I))) :
    Module.Flat R P := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective I hf z
  have h₁ : (f.lTensor R).comp (I.subtype.rTensor N) =
      (I.subtype.rTensor P).comp (f.lTensor I) := by simp
  have hx : (f.lTensor R) ((I.subtype.rTensor N) x) = 0 := by
    rw [← LinearMap.comp_apply, h₁, LinearMap.comp_apply]
    exact hz
  obtain ⟨y, hy⟩ := (lTensor_exact R hex hf ((I.subtype.rTensor N) x)).mp hx
  have h₂ : (g.lTensor (R ⧸ I)).comp (I.mkQ.rTensor M) =
      (I.mkQ.rTensor N).comp (g.lTensor R) := by simp
  have hy0 : (I.mkQ.rTensor M) y = 0 := by
    apply (map_eq_zero_iff _ (hg I)).mp
    rw [← LinearMap.comp_apply, h₂, LinearMap.comp_apply, hy,
      ← LinearMap.rTensor_comp_apply,
      (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero]
    simp
  obtain ⟨w, hw⟩ := (rTensor_exact M (LinearMap.exact_subtype_mkQ I)
    (Submodule.mkQ_surjective I) y).mp hy0
  have h₃ : (g.lTensor R).comp (I.subtype.rTensor M) =
      (I.subtype.rTensor N).comp (g.lTensor I) := by simp
  have hxg : (g.lTensor I) w = x := by
    apply Module.Flat.rTensor_preserves_injective_linearMap I.subtype
      Subtype.val_injective
    rw [← LinearMap.comp_apply, ← h₃, LinearMap.comp_apply, hw, hy]
  rw [← hxg, ← LinearMap.lTensor_comp_apply, hex.linearMap_comp_eq_zero]
  simp

end MixedFujita
