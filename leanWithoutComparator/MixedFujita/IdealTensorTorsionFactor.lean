/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section
open TensorProduct
namespace MixedFujita
universe u v w
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

noncomputable def idealTensorMultiply (I : Ideal A) : B ⊗[A] I →ₗ[B] B :=
  (AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ AlgebraTensorModule.lTensor B B I.subtype

theorem idealTensorMultiply_tmul (I : Ideal A) (b : B) (a : I) :
    idealTensorMultiply I (b ⊗ₜ[A] a) = (a : A) • b := rfl

/-- The tensor multiplication image is the actual extended ideal. -/
theorem idealTensorMultiply_range (I : Ideal A) :
    LinearMap.range (idealTensorMultiply I (B := B)) = I.map (algebraMap A B) := by
  apply le_antisymm
  · rintro b ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b a =>
        rw [idealTensorMultiply_tmul, Algebra.smul_def]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ a.property)
    | add x y hx hy => simpa only [map_add] using Ideal.add_mem _ hx hy
  · apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    refine ⟨(1 : B) ⊗ₜ[A] (⟨a, ha⟩ : I), ?_⟩
    simp only [idealTensorMultiply_tmul, Algebra.smul_def, mul_one]

/-- One fixed ideal element clears the entire kernel, by tensor balancing. -/
theorem idealTensorMultiply_clear_kernel_identity (I : Ideal A) (a : I) (x : B ⊗[A] I) :
    algebraMap A B (a : A) • x = idealTensorMultiply I x ⊗ₜ[A] a := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b i =>
      rw [TensorProduct.smul_tmul', idealTensorMultiply_tmul]
      have h : ((a : A) • b) ⊗ₜ[A] i = ((i : A) • b) ⊗ₜ[A] a := by
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul]
        congr 1
        apply Subtype.ext
        exact mul_comm _ _
      simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self,
        RingHom.id_apply] using h
  | add x y hx hy => simp only [smul_add, hx, hy, map_add, add_tmul]

theorem idealTensorMultiply_kernel_has_nonzero_annihilator
    (I : Ideal A) (hI : I ≠ ⊥) (hf : Function.Injective (algebraMap A B))
    (x : B ⊗[A] I) (hx : idealTensorMultiply I x = 0) :
    ∃ b : B, b ≠ 0 ∧ b • x = 0 := by
  obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff I).mp hI
  refine ⟨algebraMap A B a, ?_, ?_⟩
  · intro h
    apply hane
    apply hf
    simpa using h
  · simpa only [hx, zero_tmul] using idealTensorMultiply_clear_kernel_identity I ⟨a, ha⟩ x

theorem idealTensorMultiply_ker_le_ker_to_torsionFree
    (I : Ideal A) (hI : I ≠ ⊥) (hf : Function.Injective (algebraMap A B))
    {N : Type w} [AddCommGroup N] [Module B N] [NoZeroSMulDivisors B N]
    (φ : B ⊗[A] I →ₗ[B] N) : LinearMap.ker (idealTensorMultiply I) ≤ LinearMap.ker φ := by
  intro x hx
  obtain ⟨b, hb, hbx⟩ := idealTensorMultiply_kernel_has_nonzero_annihilator I hI hf x hx
  have hφ : b • φ x = 0 := by rw [← φ.map_smul, hbx, φ.map_zero]
  exact (eq_zero_or_eq_zero_of_smul_eq_zero hφ).resolve_left hb

/-- Any map to a torsion-free target factors through the extended ideal image;
no flatness assumption is needed. -/
theorem idealTensorMultiply_exists_range_factor_to_torsionFree
    (I : Ideal A) (hI : I ≠ ⊥) (hf : Function.Injective (algebraMap A B))
    {N : Type w} [AddCommGroup N] [Module B N] [NoZeroSMulDivisors B N]
    (φ : B ⊗[A] I →ₗ[B] N) :
    ∃ g : LinearMap.range (idealTensorMultiply I) →ₗ[B] N,
      ∀ x, g ((idealTensorMultiply I).rangeRestrict x) = φ x := by
  let m := idealTensorMultiply I (B := B)
  have hker : LinearMap.ker m.rangeRestrict ≤ LinearMap.ker φ := by
    intro x hx
    apply idealTensorMultiply_ker_le_ker_to_torsionFree I hI hf φ
    exact congrArg Subtype.val (show m.rangeRestrict x = 0 from hx)
  refine ⟨(m.rangeRestrict.liftOfSurjective m.surjective_rangeRestrict) ⟨φ, hker⟩, ?_⟩
  intro x
  exact LinearMap.equivOfSurjective_apply m.surjective_rangeRestrict hker

end MixedFujita

