/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FlatComplexResidueExact
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
Flat base change of the transfer of vanishing (step 10, R4).

For a complex `C` of `R`-modules and an `R`-algebra `A`, the base change `A ⊗[R] C` is a complex
of `A`-modules. Tensoring it over `A` with an `A`-module `N` is tensoring `C` over `R` with `N`
(`exact_lTensor_baseChange_iff`), and for flat `A` its cohomology stays finitely generated
(`finite_homologyAt_baseChange`).

With the local transfer of check 492 this gives the transfer from a closed point: let `𝔪` be a
maximal ideal and `C` a complex of flat `R`-modules such that every `N ⊗ C` is exact in degrees
`≥ m`, with finitely generated cohomology in degrees `≥ j₀`. If `κ(𝔪) ⊗ C` is exact in degrees
`≥ j₀`, so is `R_𝔪 ⊗ C` (`exact_lTensor_localization_of_exact_residueField`), and so is `K ⊗ C`
for every flat `R_𝔪`-module `K`, such as a field containing `R` (`exact_lTensor_of_exact_residueField`).
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u v w

variable {R : Type u} [CommRing R] {C : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
  (d : ∀ i, C i →ₗ[R] C (i + 1)) (hd : ∀ i, (d (i + 1)).comp (d i) = 0)
  (A : Type w) [CommRing A] [Algebra R A]

include hd in
/-- The base change of a complex is a complex. -/
theorem baseChange_comp_eq_zero (i : ℕ) :
    ((d (i + 1)).baseChange A).comp ((d i).baseChange A) = 0 := by
  rw [← LinearMap.baseChange_comp, hd i, LinearMap.baseChange_zero]

/-- **Tensoring the base change over `A` is tensoring over `R`.** -/
theorem exact_lTensor_baseChange_iff (N : Type*) [AddCommGroup N] [Module A N] [Module R N]
    [IsScalarTower R A N] (i : ℕ) :
    Function.Exact (((d i).baseChange A).lTensor N) (((d (i + 1)).baseChange A).lTensor N) ↔
      Function.Exact ((d i).lTensor N) ((d (i + 1)).lTensor N) := by
  have hcomm : ∀ (j : ℕ) (x : N ⊗[A] (A ⊗[R] C j)),
      AlgebraTensorModule.cancelBaseChange R A A N (C (j + 1)) (((d j).baseChange A).lTensor N x) =
        (d j).lTensor N (AlgebraTensorModule.cancelBaseChange R A A N (C j) x) := by
    intro j x
    induction x using TensorProduct.inductionOn with
    | tmul n y =>
      induction y using TensorProduct.inductionOn with
      | tmul a c =>
        simp only [LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
          AlgebraTensorModule.cancelBaseChange_tmul]
      | add y y' hy hy' =>
        rw [TensorProduct.tmul_add, map_add, map_add, hy, hy', ← map_add, ← map_add,
          ← TensorProduct.tmul_add]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', ← map_add, ← map_add]
  exact (Function.Exact.iff_of_ladder_addEquiv
    (AlgebraTensorModule.cancelBaseChange R A A N (C i)).toAddEquiv
    (AlgebraTensorModule.cancelBaseChange R A A N (C (i + 1))).toAddEquiv
    (AlgebraTensorModule.cancelBaseChange R A A N (C (i + 1 + 1))).toAddEquiv
    (f₁₂ := (((d i).baseChange A).lTensor N).toAddMonoidHom)
    (f₂₃ := (((d (i + 1)).baseChange A).lTensor N).toAddMonoidHom)
    (g₁₂ := ((d i).lTensor N).toAddMonoidHom) (g₂₃ := ((d (i + 1)).lTensor N).toAddMonoidHom)
    (AddMonoidHom.ext fun x => (hcomm i x).symm)
    (AddMonoidHom.ext fun x => (hcomm (i + 1) x).symm)).symm

/-- **The cohomology of a flat base change stays finitely generated.** -/
theorem finite_homologyAt_baseChange [Module.Flat R A] (i : ℕ)
    [Module.Finite R (homologyAt d hd i)] :
    Module.Finite A (homologyAt (fun j => (d j).baseChange A) (baseChange_comp_eq_zero d hd A) i) := by
  classical
  have hZ : ∀ t : A ⊗[R] LinearMap.ker (d (i + 1)),
      (LinearMap.ker (d (i + 1))).subtype.baseChange A t ∈
        LinearMap.ker ((d (i + 1)).baseChange A) := by
    intro t
    have h0 : (d (i + 1)).comp (LinearMap.ker (d (i + 1))).subtype = 0 := by
      ext z
      exact z.2
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h0,
      LinearMap.baseChange_zero, LinearMap.zero_apply]
  let Φ : A ⊗[R] LinearMap.ker (d (i + 1)) →ₗ[A]
      homologyAt (fun j => (d j).baseChange A) (baseChange_comp_eq_zero d hd A) i :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict _ _ hZ)
  have hΦ : Function.Surjective Φ := by
    intro x
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ x
    have hexact : Function.Exact ((LinearMap.ker (d (i + 1))).subtype.lTensor A)
        ((d (i + 1)).lTensor A) :=
      Module.Flat.lTensor_exact A (LinearMap.exact_subtype_ker_map (d (i + 1)))
    obtain ⟨t, ht⟩ := (hexact w.1).mp w.2
    exact ⟨t, congrArg (Submodule.mkQ _) (Subtype.ext ht)⟩
  let ψ₀ : LinearMap.ker (d (i + 1)) →ₗ[R]
      homologyAt (fun j => (d j).baseChange A) (baseChange_comp_eq_zero d hd A) i :=
    (Φ.restrictScalars R).comp (TensorProduct.mk R A _ 1)
  have hψ₀ : LinearMap.range (cycleRestrict d hd i) ≤ LinearMap.ker ψ₀ := by
    rintro _ ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    change Submodule.mkQ _ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨1 ⊗ₜ c, Subtype.ext rfl⟩
  let ψ := (LinearMap.range (cycleRestrict d hd i)).liftQ ψ₀ hψ₀
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := homologyAt d hd i)
  refine ⟨⟨s.image ψ, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨t, rfl⟩ := hΦ x
  induction t using TensorProduct.inductionOn with
  | tmul a z =>
    have h1 : Φ (a ⊗ₜ z) = a • ψ (Submodule.mkQ _ z) := by
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
      change Φ (a ⊗ₜ z) = a • Φ (1 ⊗ₜ z)
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1]
    refine Submodule.smul_mem _ a ?_
    have hz : Submodule.mkQ _ z ∈ Submodule.span R (s : Set (homologyAt d hd i)) :=
      hs ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := ψ) hz
    rw [Submodule.map_span, ← Finset.coe_image] at h2
    exact Submodule.span_le_restrictScalars R A _ h2
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- **Exactness passes to a flat module over the base change.** -/
theorem exact_lTensor_of_flat_of_exact (K : Type*) [AddCommGroup K] [Module A K] [Module R K]
    [IsScalarTower R A K] [Module.Flat A K] (i : ℕ)
    (h : Function.Exact ((d i).lTensor A) ((d (i + 1)).lTensor A)) :
    Function.Exact ((d i).lTensor K) ((d (i + 1)).lTensor K) :=
  (exact_lTensor_baseChange_iff d A K i).mp
    (Module.Flat.lTensor_exact K (f := (d i).baseChange A) (g := (d (i + 1)).baseChange A) h)

/-- **The transfer from a closed point**: if every `N ⊗ C` is exact in degrees `≥ m`, the cohomology
is finitely generated in degrees `≥ j₀` and `κ(𝔪) ⊗ C` is exact in degrees `≥ j₀`, then so is
`R_𝔪 ⊗ C`. -/
theorem exact_lTensor_localization_of_exact_residueField (𝔪 : Ideal R) [𝔪.IsMaximal]
    [∀ i, Module.Flat R (C i)] (m j₀ : ℕ)
    (htop : ∀ (N : Type u) [AddCommGroup N] [Module R N], ∀ i, m ≤ i →
      Function.Exact ((d i).lTensor N) ((d (i + 1)).lTensor N))
    (hfg : ∀ i, j₀ ≤ i → Module.Finite R (homologyAt d hd i))
    (hk : ∀ i, j₀ ≤ i → Function.Exact ((d i).lTensor 𝔪.ResidueField)
      ((d (i + 1)).lTensor 𝔪.ResidueField)) :
    ∀ i, j₀ ≤ i → Function.Exact ((d i).lTensor (Localization.AtPrime 𝔪))
      ((d (i + 1)).lTensor (Localization.AtPrime 𝔪)) :=
  exact_of_exact_lTensor_residueField (fun j => (d j).baseChange (Localization.AtPrime 𝔪))
    (baseChange_comp_eq_zero d hd _) m j₀ (fun i hi => htop (Localization.AtPrime 𝔪) i hi)
    (fun J i hi => (exact_lTensor_baseChange_iff d _ (Localization.AtPrime 𝔪 ⧸ J) i).mpr
      (htop _ i hi))
    (fun i hi => by
      have := hfg i hi
      exact finite_homologyAt_baseChange d hd _ i)
    (fun i hi => (exact_lTensor_baseChange_iff d _ _ i).mpr (hk i hi))

/-- **The transfer to a flat module over the local ring**, such as a field containing `R`. -/
theorem exact_lTensor_of_exact_residueField (𝔪 : Ideal R) [𝔪.IsMaximal]
    [∀ i, Module.Flat R (C i)] (m j₀ : ℕ)
    (htop : ∀ (N : Type u) [AddCommGroup N] [Module R N], ∀ i, m ≤ i →
      Function.Exact ((d i).lTensor N) ((d (i + 1)).lTensor N))
    (hfg : ∀ i, j₀ ≤ i → Module.Finite R (homologyAt d hd i))
    (hk : ∀ i, j₀ ≤ i → Function.Exact ((d i).lTensor 𝔪.ResidueField)
      ((d (i + 1)).lTensor 𝔪.ResidueField))
    (K : Type*) [AddCommGroup K] [Module (Localization.AtPrime 𝔪) K] [Module R K]
    [IsScalarTower R (Localization.AtPrime 𝔪) K] [Module.Flat (Localization.AtPrime 𝔪) K] :
    ∀ i, j₀ ≤ i → Function.Exact ((d i).lTensor K) ((d (i + 1)).lTensor K) := fun i hi =>
  exact_lTensor_of_flat_of_exact d _ K i
    (exact_lTensor_localization_of_exact_residueField d hd 𝔪 m j₀ htop hfg hk i hi)

end MixedFujita
