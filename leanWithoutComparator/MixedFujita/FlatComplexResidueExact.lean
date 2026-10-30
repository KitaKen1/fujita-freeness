/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.Module

/-!
Exactness of complexes of flat modules from their special fibre (step 10, R4).

This is the algebra of the transfer of vanishing from a special fibre. Let `C^0 → C^1 → ⋯` be a
complex of flat modules over a local ring. Assume:

* `C` and every `(R ⧸ I) ⊗ C` are exact in degrees `≥ m` (for a Čech complex of `m` opens this
  holds for every presheaf of modules);
* the cohomology is finitely generated in degrees `≥ j₀`;
* `k ⊗ C` is exact in degrees `≥ j₀` (`k` the residue field).

Then `C` is exact in degrees `≥ j₀` (`exact_of_exact_lTensor_residueField`). The proof:

* exactness of `N ⊗ C` at `C^{i+1}` makes `N ⊗ B^{i+2} → N ⊗ C^{i+2}` injective
  (`lTensor_range_subtype_injective`); for all `N = R ⧸ I` this makes `C^{i+2} ⧸ B^{i+2}` flat
  (`flat_quotient_of_lTensor_injective`), so a boundary at the top is flat
  (`flat_range_of_exact_lTensor_quotient`);
* the kernel of a surjection between flat modules is flat (`flat_ker_of_surjective`), so the
  boundaries below it are flat where `C` is exact (`flat_range_of_flat_range_of_exact`);
* if `B^{j+2}` is flat and `N ⊗ C` is exact at `C^{j+1}`, then `N ⊗ H^{j+1}(C) = 0`
  (`lTensor_homologyAt_eq_zero`);
* with `N = k`, Nakayama gives `H^{j+1}(C) = 0`, and a descending induction concludes.

No semicontinuity or generic freeness is needed.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v

section FlatKernel

variable {R : Type u} [CommRing R] {M P : Type v} [AddCommGroup M] [Module R M] [AddCommGroup P]
  [Module R P]

/-- **The kernel of a surjection between flat modules is flat.** -/
theorem flat_ker_of_surjective [Module.Flat R M] [Module.Flat R P] (g : M →ₗ[R] P)
    (hg : Function.Surjective g) : Module.Flat R (LinearMap.ker g) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  have hleft : Function.Injective ((LinearMap.ker g).subtype.lTensor I) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg (LinearMap.ker g).subtype
      Subtype.val_injective (LinearMap.exact_subtype_ker_map g) I
  have hbottom : Function.Injective (I.subtype.rTensor M) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance I
  have hcomm : (I.subtype.rTensor M).comp ((LinearMap.ker g).subtype.lTensor I) =
      ((LinearMap.ker g).subtype.lTensor R).comp (I.subtype.rTensor (LinearMap.ker g)) := by
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  have hinj : Function.Injective (((LinearMap.ker g).subtype.lTensor R).comp
      (I.subtype.rTensor (LinearMap.ker g))) := by
    rw [← hcomm]
    exact hbottom.comp hleft
  exact Function.Injective.of_comp hinj

/-- **A quotient of a flat module is flat if the submodule stays a submodule modulo every
ideal.** -/
theorem flat_quotient_of_lTensor_injective [Module.Flat R M] (B : Submodule R M)
    (hB : ∀ I : Ideal R, Function.Injective (B.subtype.lTensor (R ⧸ I))) :
    Module.Flat R (M ⧸ B) := by
  rw [Module.Flat.iff_rTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective I B.mkQ_surjective x
  have hβ : Function.Injective (I.subtype.rTensor M) :=
    Module.Flat.iff_rTensor_injective'.mp inferInstance I
  have hrow : Function.Exact (B.subtype.lTensor R) (B.mkQ.lTensor R) :=
    lTensor_exact R (LinearMap.exact_subtype_mkQ B) B.mkQ_surjective
  have h1 : B.mkQ.lTensor R (I.subtype.rTensor M y) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor,
      LinearMap.comp_apply, hx]
  obtain ⟨z, hz⟩ := (hrow _).mp h1
  have hI0 : (Submodule.mkQ I).comp I.subtype = 0 := by
    ext a
    exact Ideal.Quotient.eq_zero_iff_mem.mpr a.2
  have h2 : (Submodule.mkQ I).rTensor B z = 0 := by
    apply hB I
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hz, ← LinearMap.comp_apply,
      ← LinearMap.rTensor_comp, hI0, LinearMap.rTensor_zero, LinearMap.zero_apply]
  obtain ⟨w, hw⟩ := (rTensor_exact B (LinearMap.exact_subtype_mkQ I)
    (Submodule.mkQ_surjective I) _).mp h2
  have h3 : B.subtype.lTensor I w = y := by
    apply hβ
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, hw, hz]
  have hB0 : B.mkQ.comp B.subtype = 0 := by
    ext a
    simp
  rw [← h3, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hB0, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

end FlatKernel

section Complex

variable {R : Type u} [CommRing R] {C : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hd : ∀ i, (d (i + 1)).comp (d i) = 0)

/-- The differential into the cycles. -/
noncomputable def cycleRestrict (i : ℕ) : C i →ₗ[R] LinearMap.ker (d (i + 1)) :=
  (d i).codRestrict _ fun c => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hd i, LinearMap.zero_apply]

/-- **The cohomology at `C^{i+1}`**: cycles modulo boundaries. -/
abbrev homologyAt (i : ℕ) : Type v :=
  LinearMap.ker (d (i + 1)) ⧸ LinearMap.range (cycleRestrict d hd i)

theorem subtype_comp_cycleRestrict (i : ℕ) :
    (LinearMap.ker (d (i + 1))).subtype.comp (cycleRestrict d hd i) = d i := by
  ext c
  rfl

include hd in
/-- **Exactness of `N ⊗ C` at `C^{i+1}` makes the boundaries of `C^{i+2}` stay a submodule
after `N ⊗ -`.** -/
theorem lTensor_range_subtype_injective (N : Type*) [AddCommGroup N] [Module R N] (i : ℕ)
    (hN : Function.Exact ((d i).lTensor N) ((d (i + 1)).lTensor N)) :
    Function.Injective ((LinearMap.range (d (i + 1))).subtype.lTensor N) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := LinearMap.lTensor_surjective N (d (i + 1)).surjective_rangeRestrict u
  have hv : (d (i + 1)).lTensor N v = 0 := by
    rw [← hu, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, LinearMap.subtype_comp_rangeRestrict]
  obtain ⟨w, rfl⟩ := (hN v).mp hv
  have h0 : (d (i + 1)).rangeRestrict.comp (d i) = 0 := by
    refine LinearMap.ext fun c => Subtype.ext ?_
    change d (i + 1) (d i c) = 0
    rw [← LinearMap.comp_apply, hd i, LinearMap.zero_apply]
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero,
    LinearMap.zero_apply]

include hd in
/-- **A boundary is flat if the complex is exact there and every `(R ⧸ I) ⊗ C` is exact one step
below.** -/
theorem flat_range_of_exact_lTensor_quotient [∀ i, Module.Flat R (C i)] (i : ℕ)
    (hI : ∀ I : Ideal R, Function.Exact ((d i).lTensor (R ⧸ I)) ((d (i + 1)).lTensor (R ⧸ I)))
    (hex : Function.Exact (d (i + 1)) (d (i + 1 + 1))) :
    Module.Flat R (LinearMap.range (d (i + 1 + 1))) := by
  have hQ : Module.Flat R (C (i + 1 + 1) ⧸ LinearMap.range (d (i + 1))) :=
    flat_quotient_of_lTensor_injective _ fun I =>
      lTensor_range_subtype_injective d hd (R ⧸ I) i (hI I)
  have e : (C (i + 1 + 1) ⧸ LinearMap.range (d (i + 1))) ≃ₗ[R] LinearMap.range (d (i + 1 + 1)) :=
    (Submodule.quotEquivOfEq _ _ hex.linearMap_ker_eq.symm).trans
      (d (i + 1 + 1)).quotKerEquivRange
  exact Module.Flat.of_linearEquiv e.symm

/-- **The boundaries are flat below a flat boundary, where the complex is exact.** -/
theorem flat_range_of_flat_range_of_exact [∀ i, Module.Flat R (C i)] (j M : ℕ)
    (hM : Module.Flat R (LinearMap.range (d M)))
    (hex : ∀ i, j ≤ i → i < M → Function.Exact (d i) (d (i + 1))) :
    ∀ i, j ≤ i → i ≤ M → Module.Flat R (LinearMap.range (d i)) := by
  intro i hi hiM
  induction h : M - i using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    rcases Nat.eq_or_lt_of_le hiM with rfl | hlt
    · exact hM
    · have h1 : Module.Flat R (LinearMap.range (d (i + 1))) :=
        ih (M - (i + 1)) (by omega) (i + 1) (by omega) hlt rfl
      have h2 : Module.Flat R (LinearMap.ker (d (i + 1)).rangeRestrict) :=
        flat_ker_of_surjective _ (d (i + 1)).surjective_rangeRestrict
      rw [LinearMap.ker_rangeRestrict] at h2
      rw [← (hex i hi hlt).linearMap_ker_eq]
      exact h2

/-- **The key step**: if `B^{j+2}` is flat and `N ⊗ C` is exact at `C^{j+1}`, then
`N ⊗ H^{j+1}(C) = 0`. -/
theorem lTensor_homologyAt_eq_zero (N : Type*) [AddCommGroup N] [Module R N] (j : ℕ)
    (hflat : Module.Flat R (LinearMap.range (d (j + 1))))
    (hN : Function.Exact ((d j).lTensor N) ((d (j + 1)).lTensor N)) :
    ∀ x : N ⊗[R] homologyAt d hd j, x = 0 := by
  have hinj : Function.Injective ((LinearMap.ker (d (j + 1))).subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat (d (j + 1)).rangeRestrict
      (d (j + 1)).surjective_rangeRestrict (LinearMap.ker (d (j + 1))).subtype
      Subtype.val_injective (by
        rw [← LinearMap.ker_rangeRestrict]
        exact LinearMap.exact_subtype_ker_map _) N
  have hpure : ∀ (n : N) (z : LinearMap.ker (d (j + 1))),
      n ⊗ₜ[R] (Submodule.mkQ _ z : homologyAt d hd j) = 0 := by
    intro n z
    have hz : (d (j + 1)).lTensor N (n ⊗ₜ[R] (z : C (j + 1))) = 0 := by
      rw [LinearMap.lTensor_tmul, LinearMap.mem_ker.mp z.2, TensorProduct.tmul_zero]
    obtain ⟨u, hu⟩ := (hN _).mp hz
    have hu' : ((LinearMap.ker (d (j + 1))).subtype.lTensor N)
        ((cycleRestrict d hd j).lTensor N u) =
        ((LinearMap.ker (d (j + 1))).subtype.lTensor N) (n ⊗ₜ[R] z) := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_cycleRestrict, hu,
        LinearMap.lTensor_tmul]
      rfl
    have h2 := hinj hu'
    have h3 : ((Submodule.mkQ (LinearMap.range (cycleRestrict d hd j))).lTensor N)
        ((cycleRestrict d hd j).lTensor N u) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have h0 : (Submodule.mkQ (LinearMap.range (cycleRestrict d hd j))).comp
          (cycleRestrict d hd j) = 0 := by
        ext c
        simp
      rw [h0, LinearMap.lTensor_zero, LinearMap.zero_apply]
    rw [h2, LinearMap.lTensor_tmul] at h3
    exact h3
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul n h =>
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ h
    exact hpure n z
  | add x y hx hy => rw [hx, hy, add_zero]

/-- **Exactness from the special fibre**: over a local ring, let `C` be a complex of flat modules
such that `C` and every `(R ⧸ I) ⊗ C` are exact in degrees `≥ m`. If the cohomology is finitely
generated in degrees `≥ j₀` and `k ⊗ C` is exact in degrees `≥ j₀`, then `C` is exact in
degrees `≥ j₀`. -/
theorem exact_of_exact_lTensor_residueField [IsLocalRing R] [∀ i, Module.Flat R (C i)]
    (m j₀ : ℕ) (htop : ∀ i, m ≤ i → Function.Exact (d i) (d (i + 1)))
    (htopI : ∀ I : Ideal R, ∀ i, m ≤ i →
      Function.Exact ((d i).lTensor (R ⧸ I)) ((d (i + 1)).lTensor (R ⧸ I)))
    (hfg : ∀ i, j₀ ≤ i → Module.Finite R (homologyAt d hd i))
    (hk : ∀ i, j₀ ≤ i → Function.Exact ((d i).lTensor (IsLocalRing.ResidueField R))
      ((d (i + 1)).lTensor (IsLocalRing.ResidueField R))) :
    ∀ i, j₀ ≤ i → Function.Exact (d i) (d (i + 1)) := by
  have hM : Module.Flat R (LinearMap.range (d (m + 1 + 1))) :=
    flat_range_of_exact_lTensor_quotient d hd m (fun I => htopI I m le_rfl)
      (htop (m + 1) (by omega))
  intro i hi
  induction h : m - i using Nat.strong_induction_on generalizing i with
  | _ k ih =>
    by_cases hmi : m ≤ i
    · exact htop i hmi
    · have hex : ∀ i', i + 1 ≤ i' → i' < m + 1 + 1 → Function.Exact (d i') (d (i' + 1)) :=
        fun i' hi' _ => by
          by_cases hm' : m ≤ i'
          · exact htop i' hm'
          · exact ih (m - i') (by omega) i' (by omega) rfl
      have hflat : Module.Flat R (LinearMap.range (d (i + 1))) :=
        flat_range_of_flat_range_of_exact d (i + 1) (m + 1 + 1) hM hex (i + 1) le_rfl (by omega)
      have hzero := lTensor_homologyAt_eq_zero d hd (IsLocalRing.ResidueField R) i hflat (hk i hi)
      have : Module.Finite R (homologyAt d hd i) := hfg i hi
      have hsub : Subsingleton (homologyAt d hd i) := by
        rw [← IsLocalRing.subsingleton_tensorProduct (R := R)]
        exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
      intro y
      constructor
      · intro hy
        have hmem : (Submodule.mkQ (LinearMap.range (cycleRestrict d hd i))
            (⟨y, LinearMap.mem_ker.mpr hy⟩ : LinearMap.ker (d (i + 1)))) = 0 :=
          Subsingleton.elim _ _
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
        obtain ⟨c, hc⟩ := hmem
        exact ⟨c, congrArg Subtype.val hc⟩
      · rintro ⟨c, rfl⟩
        rw [← LinearMap.comp_apply, hd i, LinearMap.zero_apply]

end Complex

end MixedFujita
