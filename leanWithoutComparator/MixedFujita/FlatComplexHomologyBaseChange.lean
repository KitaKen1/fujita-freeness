/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FlatComplexKernelBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
Flat base change commutes with the cohomology of a complex (step 10, R4-3).

For a flat `R`-algebra `S`, `S ⊗[R] ker f ≅ ker (S ⊗ f)` (`kerBaseChangeLinearEquiv`), and the
cohomology of the base change of a complex `C` is the base change of its cohomology:
`S ⊗[R] H^{i+1}(C) ≅ H^{i+1}(S ⊗[R] C)` (`homologyAtBaseChangeEquiv`), `S`-linearly. The cycles
are kernels, and the boundaries of `S ⊗ C` are the image of `S ⊗` the boundaries
(`map_range_cycleRestrict_baseChange`); the quotient commutes with `S ⊗ -` by right exactness.

This is used for the fibre of the closure over a localization `A_f` of the base, where the
cohomology of the Čech complex has become free.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

section Kernel

variable {R : Type u} [CommRing R] (S : Type w) [CommRing S] [Algebra R S] [Module.Flat R S]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Flat base change commutes with kernels.** -/
noncomputable def kerBaseChangeLinearEquiv (f : M →ₗ[R] N) :
    S ⊗[R] LinearMap.ker f ≃ₗ[S] LinearMap.ker (f.baseChange S) :=
  (LinearEquiv.ofInjective ((LinearMap.ker f).subtype.baseChange S)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)).trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      exact ((Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map f)) x).symm))

theorem kerBaseChangeLinearEquiv_apply (f : M →ₗ[R] N) (x : S ⊗[R] LinearMap.ker f) :
    (kerBaseChangeLinearEquiv S f x : S ⊗[R] M) = (LinearMap.ker f).subtype.baseChange S x :=
  rfl

end Kernel

section Homology

variable {R : Type u} [CommRing R] {C : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hd : ∀ i, (d (i + 1)).comp (d i) = 0)
  (S : Type w) [CommRing S] [Algebra R S] [Module.Flat R S]

/-- The boundaries of the base change are the image of the base change of the boundaries. -/
theorem map_range_cycleRestrict_baseChange (i : ℕ) :
    (LinearMap.range (AlgebraTensorModule.lTensor S S
        ((LinearMap.range (cycleRestrict d hd i)).subtype.restrictScalars R))).map
      (kerBaseChangeLinearEquiv S (d (i + 1))).toLinearMap =
    LinearMap.range (cycleRestrict (fun j => (d j).baseChange S)
      (baseChange_comp_eq_zero d hd S) i) := by
  -- the boundaries are the image of `S ⊗ C_i`
  have hsurj : Function.Surjective (AlgebraTensorModule.lTensor S S
      ((cycleRestrict d hd i).rangeRestrict.restrictScalars R)) :=
    LinearMap.lTensor_surjective _ (cycleRestrict d hd i).surjective_rangeRestrict
  have hcomp : AlgebraTensorModule.lTensor S S (cycleRestrict d hd i) =
      (AlgebraTensorModule.lTensor S S
        ((LinearMap.range (cycleRestrict d hd i)).subtype.restrictScalars R)).comp
      (AlgebraTensorModule.lTensor S S
        ((cycleRestrict d hd i).rangeRestrict.restrictScalars R)) := by
    ext c
    rfl
  have hrange : LinearMap.range (AlgebraTensorModule.lTensor S S
        ((LinearMap.range (cycleRestrict d hd i)).subtype.restrictScalars R)) =
      LinearMap.range (AlgebraTensorModule.lTensor S S (cycleRestrict d hd i)) := by
    rw [hcomp, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hsurj)]
  have hfin : (kerBaseChangeLinearEquiv S (d (i + 1))).toLinearMap.comp
      (AlgebraTensorModule.lTensor S S (cycleRestrict d hd i)) =
      cycleRestrict (fun j => (d j).baseChange S) (baseChange_comp_eq_zero d hd S) i := by
    ext c
    rfl
  rw [hrange, ← LinearMap.range_comp, hfin]

/-- **Flat base change commutes with cohomology.** -/
noncomputable def homologyAtBaseChangeEquiv (i : ℕ) :
    S ⊗[R] homologyAt d hd i ≃ₗ[S]
      homologyAt (fun j => (d j).baseChange S) (baseChange_comp_eq_zero d hd S) i :=
  (AlgebraTensorModule.tensorQuotientEquiv S R S (LinearMap.range (cycleRestrict d hd i))).trans
    (Submodule.Quotient.equiv _ _ (kerBaseChangeLinearEquiv S (d (i + 1)))
      (map_range_cycleRestrict_baseChange d hd S i))

end Homology

end MixedFujita
