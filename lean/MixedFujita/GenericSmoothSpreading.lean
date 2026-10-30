/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StandardSmoothSpreading
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus

/-!
Spreading out smoothness for every larger base, and a smooth base over `ℤ` (step 10, R4-3).

* `exists_fg_forall_isStandardSmooth_of_injective`: the conclusion of check 504 holds for every
  `R`-subalgebra `A'` of `S` containing a fixed finitely generated one. The model of `T_K` over `A`
  is the closure of `T_K` in projective space over `A`, taken once for the final `A`, so the
  smoothness of its charts is needed for all large `A`.
* `exists_fg_smooth_int_of_charZero`: every finitely generated `ℤ`-subalgebra of a field of
  characteristic zero lies in a finitely generated one that is smooth over `ℤ`. The fraction field
  is formally smooth over `ℚ` (finitely generated over a perfect field), hence over `ℤ`, and the
  smooth locus is open; inverting one nonzero element gives a smooth algebra, embedded in the field.
  A smooth base lets the closed point `A → κ` lift to `A → W₂(κ)` by formal smoothness.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

section Spreading

variable {R : Type*} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
  {C : Type*} [CommRing C] [Algebra S C]

/-- **Spreading out standard smoothness to subrings, for every larger base.** If `C` is standard
smooth of relative dimension `n` over `S` and generated over `S` by the finite set `γ`, there is a
finitely generated `R`-subalgebra `A₀` of `S` such that for every `R`-subalgebra `A' ≥ A₀`, every
`A'`-algebra `M` with an injective ring map `φ : M → C` over `A' → S`, whose image contains `γ` and
which is generated over `A'` by `φ⁻¹(γ)`, is standard smooth of relative dimension `n` over `A'`. -/
theorem exists_fg_forall_isStandardSmooth_of_injective (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n S C]
    (γ : Finset C) (hγ : Algebra.adjoin S (γ : Set C) = ⊤) :
    ∃ A₀ : Subalgebra R S, A₀.FG ∧ ∀ A' : Subalgebra R S, A₀ ≤ A' →
      ∀ (M : Type*) [CommRing M] [Algebra A' M] (φ : M →+* C),
        φ.comp (algebraMap A' M) = (algebraMap S C).comp (algebraMap A' S) →
        Function.Injective φ → (γ : Set C) ⊆ Set.range φ →
        Algebra.adjoin A' (φ ⁻¹' (γ : Set C)) = ⊤ →
        Algebra.IsStandardSmoothOfRelativeDimension n A' M := by
  classical
  obtain ⟨A₂, B₀, _, _, hA₂, hsm, ⟨e⟩⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg R S C n
  have : Algebra.IsStandardSmooth A₂ B₀ := hsm.isStandardSmooth
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A₂ B₀).FG)
  -- the images in `C` of elements of the model
  let b : B₀ →+* C := e.symm.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight (A := S) : B₀ →ₐ[A₂] S ⊗[A₂] B₀).toRingHom
  have hb : ∀ c : C, c ∈ Algebra.adjoin S (b '' (t : Set B₀)) := by
    intro c
    have h1 := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := S) (t : Set B₀) ht
    have h2 : e c ∈ Algebra.adjoin S (((1 : S) ⊗ₜ[A₂] ·) '' (t : Set B₀)) := by
      rw [h1]; exact Algebra.mem_top
    have h3 : e.symm (e c) ∈
        (Algebra.adjoin S (((1 : S) ⊗ₜ[A₂] ·) '' (t : Set B₀))).map e.symm.toAlgHom :=
      Subalgebra.mem_map.2 ⟨e c, h2, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_image, e.symm_apply_apply] at h3
    exact h3
  obtain ⟨F₁, hF₁⟩ := exists_finset_forall_mem_adjoinSubring (R := R) γ (fun c _ => hb c)
  obtain ⟨F₂, hF₂⟩ := exists_finset_forall_mem_adjoinSubring (R := R) (X := (γ : Set C))
    (t.image b) (fun c _ => by rw [hγ]; exact Algebra.mem_top)
  obtain ⟨s₂, hs₂⟩ := hA₂
  let s : Finset S := s₂ ∪ F₁ ∪ F₂
  refine ⟨Algebra.adjoin R (s : Set S), ⟨s, rfl⟩, fun A' hA₀ => ?_⟩
  have hsA' : ∀ {z : S}, z ∈ s → z ∈ A' :=
    fun hz => hA₀ (Algebra.subset_adjoin (Finset.mem_coe.2 hz))
  have hA₂A' : A₂ ≤ A' := by
    rw [← hs₂, Algebra.adjoin_le_iff]
    exact fun z hz => hsA' (by simp [s, Finset.mem_coe.1 hz])
  intro M _ _ φ hφ hinj hγφ hgen
  have hφa : ∀ a : A', φ (algebraMap A' M a) = algebraMap S C a :=
    fun a => RingHom.congr_fun hφ a
  let _ : Algebra A₂ A' := (Subalgebra.inclusion hA₂A').toRingHom.toAlgebra
  let ι : A' →ₐ[A₂] S := { toRingHom := A'.val.toRingHom, commutes' := fun _ => rfl }
  let ψ : A' ⊗[A₂] B₀ →+* C :=
    e.symm.toAlgHom.toRingHom.comp (Algebra.TensorProduct.map ι (AlgHom.id A₂ B₀)).toRingHom
  have hψinj : Function.Injective ψ :=
    e.symm.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M := B₀)
      ι.toLinearMap Subtype.val_injective)
  have hψa : ∀ a : A', ψ (a ⊗ₜ 1) = algebraMap S C a := by
    intro a
    have h : (Algebra.TensorProduct.map ι (AlgHom.id A₂ B₀)) (a ⊗ₜ 1) =
        algebraMap S (S ⊗[A₂] B₀) (a : S) := by
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.algebraMap_apply]
      rfl
    change e.symm ((Algebra.TensorProduct.map ι (AlgHom.id A₂ B₀)) (a ⊗ₜ 1)) = _
    rw [h, AlgEquiv.commutes]
  have hψb : ∀ β : B₀, ψ (1 ⊗ₜ β) = b β := by
    intro β
    change e.symm ((Algebra.TensorProduct.map ι (AlgHom.id A₂ B₀)) (1 ⊗ₜ β)) =
      e.symm (Algebra.TensorProduct.includeRight β)
    rw [Algebra.TensorProduct.map_tmul, map_one, Algebra.TensorProduct.includeRight_apply]
    rfl
  -- the image of `M` is contained in the image of the model
  have hsubψ : adjoinSubring A' (b '' (t : Set B₀)) ≤ ψ.range := by
    refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      exact RingHom.mem_range.2 ⟨⟨a, ha⟩ ⊗ₜ 1, hψa ⟨a, ha⟩⟩
    · rintro _ ⟨β, -, rfl⟩
      exact RingHom.mem_range.2 ⟨1 ⊗ₜ β, hψb β⟩
  have hγψ : ∀ c ∈ γ, c ∈ ψ.range := fun c hc =>
    hsubψ (hF₁ A' (fun z hz => hsA' (by simp [s, Finset.mem_coe.1 hz])) c hc)
  have hφψ : ∀ m : M, ∃ z, ψ z = φ m := by
    intro m
    have hm : m ∈ Algebra.adjoin A' (φ ⁻¹' (γ : Set C)) := by
      rw [hgen]; exact Algebra.mem_top
    induction hm using Algebra.adjoin_induction with
    | mem x hx => exact RingHom.mem_range.1 (hγψ _ (Finset.mem_coe.1 hx))
    | algebraMap a => exact ⟨a ⊗ₜ 1, (hψa a).trans (hφa a).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨z₁, h₁⟩ := hx
      obtain ⟨z₂, h₂⟩ := hy
      exact ⟨z₁ + z₂, by rw [map_add, map_add, h₁, h₂]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨z₁, h₁⟩ := hx
      obtain ⟨z₂, h₂⟩ := hy
      exact ⟨z₁ * z₂, by rw [map_mul, map_mul, h₁, h₂]⟩
  -- the image of the model is contained in the image of `M`
  have hsubφ : adjoinSubring A' (γ : Set C) ≤ φ.range := by
    refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩
      exact RingHom.mem_range.2 ⟨algebraMap A' M ⟨a, ha⟩, hφa ⟨a, ha⟩⟩
    · intro c hc
      exact RingHom.mem_range.2 (hγφ hc)
  have hbφ : ∀ β : B₀, b β ∈ φ.range := by
    intro β
    have hβ : β ∈ Algebra.adjoin A₂ (t : Set B₀) := by
      rw [ht]; exact Algebra.mem_top
    induction hβ using Algebra.adjoin_induction with
    | mem x hx =>
      exact hsubφ (hF₂ A' (fun z hz => hsA' (by simp [s, Finset.mem_coe.1 hz])) (b x)
        (Finset.mem_image_of_mem b hx))
    | algebraMap r =>
      refine RingHom.mem_range.2 ⟨algebraMap A' M (Subalgebra.inclusion hA₂A' r), ?_⟩
      rw [hφa]
      change algebraMap S C (r : S) =
        e.symm (Algebra.TensorProduct.includeRight (A := S) (algebraMap A₂ B₀ r))
      rw [AlgHom.commutes]
      change algebraMap S C (r : S) = e.symm ((r : S) ⊗ₜ[A₂] (1 : B₀))
      rw [← e.symm.commutes (r : S), Algebra.TensorProduct.algebraMap_apply]
      rfl
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
  have hψφ : ∀ z, ∃ m : M, φ m = ψ z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a β =>
      obtain ⟨m, hm⟩ := RingHom.mem_range.1 (hbφ β)
      refine ⟨algebraMap A' M a * m, ?_⟩
      rw [map_mul, hφa, hm, ← hψa, ← hψb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
    | add x y hx hy =>
      obtain ⟨m₁, h₁⟩ := hx
      obtain ⟨m₂, h₂⟩ := hy
      exact ⟨m₁ + m₂, by rw [map_add, map_add, h₁, h₂]⟩
  -- the comparison isomorphism
  choose f hf using hφψ
  let fA : M →ₐ[A'] A' ⊗[A₂] B₀ :=
    { toFun := f
      map_one' := hψinj (by rw [hf, map_one, map_one])
      map_mul' := fun x y => hψinj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hψinj (by rw [hf, map_zero, map_zero])
      map_add' := fun x y => hψinj (by rw [hf, map_add, map_add, hf, hf])
      commutes' := fun a => hψinj (by
        rw [hf, hφa, Algebra.TensorProduct.algebraMap_apply]
        exact (hψa a).symm) }
  have hbij : Function.Bijective fA := by
    refine ⟨fun x y h => hinj ?_, fun z => ?_⟩
    · rw [← hf x, ← hf y]
      exact congrArg ψ h
    · obtain ⟨m, hm⟩ := hψφ z
      exact ⟨m, hψinj ((hf m).trans hm)⟩
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv n (AlgEquiv.ofBijective fA hbij).symm

end Spreading

section GenericSmoothness

variable {K : Type u} [Field K] [CharZero K]

/-- A finitely generated `ℤ`-subalgebra of a field of characteristic zero is smooth over `ℤ` at its
generic point: its fraction field is finitely generated over the perfect field `ℚ`. -/
theorem isSmoothAt_bot_of_charZero (A : Subalgebra ℤ K) (hA : A.FG) :
    Algebra.IsSmoothAt ℤ (⊥ : Ideal A) := by
  have : Algebra.FiniteType ℤ A := Subalgebra.fg_iff_finiteType A |>.1 hA
  have : IsLocalization (nonZeroDivisors A) (Localization.AtPrime (⊥ : Ideal A)) := by
    convert! (inferInstance :
      IsLocalization (⊥ : Ideal A).primeCompl (Localization.AtPrime (⊥ : Ideal A)))
    ext; simp [Ideal.primeCompl]
  have : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing A) (nonZeroDivisors A)
  have := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := FractionRing A)
    (RingHom.ext_int _ _)
  have : Algebra.EssFiniteType ℤ (FractionRing A) :=
    Algebra.EssFiniteType.comp ℤ A (FractionRing A)
  have : Algebra.EssFiniteType ℚ (FractionRing A) :=
    Algebra.EssFiniteType.of_comp ℤ ℚ (FractionRing A)
  have : Algebra.FormallySmooth ℤ ℚ :=
    Algebra.FormallySmooth.of_isLocalization (Rₘ := ℚ) (nonZeroDivisors ℤ)
  have : Algebra.FormallySmooth ℤ (FractionRing A) :=
    Algebra.FormallySmooth.comp ℤ ℚ (FractionRing A)
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv (nonZeroDivisors A) (FractionRing A)
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars ℤ)

/-- **A smooth base.** Every finitely generated `ℤ`-subalgebra of a field of characteristic zero is
contained in a finitely generated `ℤ`-subalgebra that is smooth over `ℤ` (the image of a
localization `A_f`, `f ≠ 0`, in the field). -/
theorem exists_fg_smooth_int_of_charZero (A : Subalgebra ℤ K) (hA : A.FG) :
    ∃ A' : Subalgebra ℤ K, A ≤ A' ∧ A'.FG ∧ Algebra.Smooth ℤ A' := by
  have : Algebra.FiniteType ℤ A := Subalgebra.fg_iff_finiteType A |>.1 hA
  have : Algebra.FinitePresentation ℤ A := Algebra.FinitePresentation.of_finiteType.1 this
  have := isSmoothAt_bot_of_charZero A hA
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth ℤ (⊥ : Ideal A)
  have hf0 : f ≠ 0 := fun h => hf (h ▸ Ideal.zero_mem _)
  have hunit : IsUnit (A.val.toRingHom f) :=
    isUnit_iff_ne_zero.2 (fun h => hf0 (Subtype.val_injective h))
  let φ : Localization.Away f →+* K := IsLocalization.Away.lift f hunit
  have hφ : ∀ a : A, φ (algebraMap A (Localization.Away f) a) = a :=
    fun a => IsLocalization.Away.lift_eq f hunit a
  have hloc : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have hinj : Function.Injective φ := by
    refine (IsLocalization.lift_injective_iff _).2 fun x y => ?_
    exact ⟨fun h => congrArg _ (hloc h), fun h => congrArg _ (Subtype.val_injective h)⟩
  let φA : Localization.Away f →ₐ[ℤ] K :=
    { φ with
      commutes' := fun z => RingHom.congr_fun
        (RingHom.ext_int (φ.comp (algebraMap ℤ (Localization.Away f))) (algebraMap ℤ K)) z }
  have hft : Algebra.FiniteType ℤ (Localization.Away f) := inferInstance
  refine ⟨φA.range, fun a ha => ⟨algebraMap A (Localization.Away f) ⟨a, ha⟩, hφ ⟨a, ha⟩⟩,
    ?_, ?_⟩
  · rw [← Algebra.map_top]
    exact hft.out.map φA
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φA hinj)

end GenericSmoothness

end MixedFujita
