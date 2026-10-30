/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
Transversality from smoothness of a stratum over the base (step 9, generic restriction).

For a formally smooth algebra R → O' the base change map O' ⊗ Ω_R → Ω_{O'} of differentials is
injective (Jacobi–Zariski: H₁(L_{O'/R}) → O' ⊗ Ω_R → Ω_{O'} is exact and H₁ vanishes), and it is
split because Ω_{O'/R} is projective; hence it stays injective after any base change
(`residueKaehlerMap_injective`).

Let O be the local ring of a point t of a smooth model, R the local ring of the base at the image
of t, z_s ∈ O finitely many elements and O → O' a map killing the z_s to an R-algebra O' (the local
ring of the stratum z = 0 at t). If O' is formally smooth over R, then on a field F over O' the
differentials of the z_s and of base functions u_l with independent differentials are
independent together (`linearIndependent_kaehler_of_formallySmooth_quotient`): the strata of a
simple normal crossing family that are smooth over the base meet the fibres transversally.
-/

@[expose] public section

open TensorProduct KaehlerDifferential

namespace MixedFujita

section Kaehler

variable (K : Type*) {R O' : Type*} [CommRing K] [CommRing R] [CommRing O'] [Algebra K R]
  [Algebra K O'] [Algebra R O'] [IsScalarTower K R O']

/-- For a formally smooth algebra the base change map of differentials is injective. -/
theorem mapBaseChange_injective_of_formallySmooth [Algebra.FormallySmooth R O'] :
    Function.Injective (mapBaseChange K R O') := by
  have hδ : Algebra.H1Cotangent.δ K R O' = 0 :=
    LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  rw [← LinearMap.ker_eq_bot,
    (Algebra.H1Cotangent.exact_δ_mapBaseChange K R O').linearMap_ker_eq, hδ,
    LinearMap.range_zero]

/-- For a formally smooth algebra the base change map of differentials has a retraction. -/
theorem exists_retraction_mapBaseChange [Algebra.FormallySmooth R O'] :
    ∃ l : Ω[O'⁄K] →ₗ[O'] O' ⊗[R] Ω[R⁄K], l ∘ₗ mapBaseChange K R O' = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (map K R O' O') LinearMap.id
    (map_surjective K R O')
  exact ((((exact_mapBaseChange_map K R O').split_tfae').out 1 2 rfl rfl).mp
    ⟨mapBaseChange_injective_of_formallySmooth K, s, hs⟩).2

variable (F : Type*) [CommRing F] [Algebra O' F] [Algebra R F] [IsScalarTower R O' F]

/-- The map F ⊗_R Ω_R → F ⊗_{O'} Ω_{O'}, a ⊗ d r ↦ a ⊗ d r, for an O'-algebra F. -/
noncomputable def residueKaehlerMap : F ⊗[R] Ω[R⁄K] →ₗ[F] F ⊗[O'] Ω[O'⁄K] :=
  AlgebraTensorModule.lTensor F F (mapBaseChange K R O') ∘ₗ
    (AlgebraTensorModule.cancelBaseChange R O' F F Ω[R⁄K]).symm.toLinearMap

theorem residueKaehlerMap_tmul (a : F) (r : R) :
    residueKaehlerMap K F (a ⊗ₜ[R] D K R r) = a ⊗ₜ[O'] D K O' (algebraMap R O' r) := by
  simp only [residueKaehlerMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, AlgebraTensorModule.lTensor_tmul,
    mapBaseChange_tmul, one_smul, map_D]

/-- For a formally smooth algebra the map of differentials stays injective after base change. -/
theorem residueKaehlerMap_injective [Algebra.FormallySmooth R O'] :
    Function.Injective (residueKaehlerMap K (R := R) (O' := O') F) := by
  obtain ⟨l, hl⟩ := exists_retraction_mapBaseChange K (R := R) (O' := O')
  have hinj : Function.Injective (AlgebraTensorModule.lTensor F F (mapBaseChange K R O')) := by
    refine Function.LeftInverse.injective (g := AlgebraTensorModule.lTensor F F l) fun x => ?_
    rw [← LinearMap.comp_apply, ← AlgebraTensorModule.lTensor_comp, hl,
      AlgebraTensorModule.lTensor_id, LinearMap.id_apply]
  exact hinj.comp (AlgebraTensorModule.cancelBaseChange R O' F F Ω[R⁄K]).symm.injective

end Kaehler

section Stalk

variable (K : Type*) {R O O' F : Type*} [CommRing K] [CommRing R] [CommRing O] [CommRing O']
  [Field F] [Algebra K R] [Algebra K O] [Algebra K O'] [Algebra R O] [Algebra R O']
  [Algebra O O'] [IsScalarTower K R O'] [IsScalarTower K O O'] [IsScalarTower R O O']
  [Algebra O' F] [Algebra O F] [Algebra R F] [IsScalarTower O O' F] [IsScalarTower R O' F]

/-- Transversality: if the quotient O' of O by the z_s is formally smooth over R, the
differentials of the z_s and of base functions with independent differentials are independent on
every field over O'. -/
theorem linearIndependent_kaehler_of_formallySmooth_quotient [Algebra.FormallySmooth R O']
    {S ι : Type*} [Fintype S] [Fintype ι] (z : S → O) (hz : ∀ s, algebraMap O O' (z s) = 0)
    (u : ι → R) (hu : LinearIndependent F (fun l => (1 : F) ⊗ₜ[R] D K R (u l)))
    (hzind : LinearIndependent F (fun s => (1 : F) ⊗ₜ[O] D K O (z s))) :
    LinearIndependent F (Sum.elim (fun s => (1 : F) ⊗ₜ[O] D K O (z s))
      (fun l => (1 : F) ⊗ₜ[O] D K O (algebraMap R O (u l)))) := by
  set Φ := residueKaehlerMap K (R := O) (O' := O') F with hΦ
  set Ψ := residueKaehlerMap K (R := R) (O' := O') F with hΨ
  have hΦz : ∀ s, Φ ((1 : F) ⊗ₜ[O] D K O (z s)) = 0 := by
    intro s
    rw [hΦ, residueKaehlerMap_tmul, hz s, map_zero, tmul_zero]
  have hΦu : ∀ l, Φ ((1 : F) ⊗ₜ[O] D K O (algebraMap R O (u l))) =
      Ψ ((1 : F) ⊗ₜ[R] D K R (u l)) := by
    intro l
    rw [hΦ, hΨ, residueKaehlerMap_tmul, residueKaehlerMap_tmul,
      ← IsScalarTower.algebraMap_apply R O O']
  have hind : LinearIndependent F (fun l => Ψ ((1 : F) ⊗ₜ[R] D K R (u l))) :=
    hu.map' Ψ (LinearMap.ker_eq_bot.mpr (residueKaehlerMap_injective K F))
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  have hr : ∀ l, g (Sum.inr l) = 0 := by
    have h := congrArg Φ hg
    rw [map_add, map_sum, map_sum, map_zero] at h
    simp only [map_smul, hΦz, smul_zero, Finset.sum_const_zero, zero_add, hΦu] at h
    exact Fintype.linearIndependent_iff.mp hind (fun l => g (Sum.inr l)) h
  have hl : ∀ s, g (Sum.inl s) = 0 := by
    simp only [hr, zero_smul, Finset.sum_const_zero, add_zero] at hg
    exact Fintype.linearIndependent_iff.mp hzind (fun s => g (Sum.inl s)) hg
  intro i
  cases i with
  | inl s => exact hl s
  | inr l => exact hr l

end Stalk

end MixedFujita
