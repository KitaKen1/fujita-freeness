/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ConeStepHomology

/-!
Iterated cones of the rows of a double complex (step 10).

Let `R_0, R_1, …` be cochain complexes of vector spaces with chain maps `δ_j : R_j ⟶ R_{j+1}` and
`δ_j ≫ δ_{j+1} = 0` (the rows of a double complex with vertical differential `δ`). For `v : A ⟶ A'`
and `ψ : A' ⟶ B'` with `v ≫ ψ = 0`, the degreewise map `a ↦ (v a, 0)` is a chain map from `A` to
the cone of `ψ` (`coneStepLift`), and it kills every chain map killed by `v`. Hence the cones can be
iterated: `iteratedCone n j` is the cone of `R_j ⟶ T'`, with `T'` the iterated cone of the rows
`R_{j+1}, …, R_{j+n}` and the map induced by `δ_j` (`iteratedConeData` carries the recursion).
In degree `m` it is `R_j^m ⊞ R_{j+1}^{m-1} ⊞ ⋯`, the total complex of the double complex, and
`dim H^m(iteratedCone n j) ≤ Σ_{b ≤ n, b ≤ m} dim H^{m-b}(R_{j+b})`
(`finrank_iteratedCone_homology_le`, from the cone step bounds of check 433). The cone of the zero
map splits as a complex (`coneStepZeroSnd`, `coneStepLift (𝟙 A) 0`), so with zero vertical maps the
iterated cone is the direct sum `⊕_b R_{j+b}[-b]` and the bound is an equality
(`finrank_coneStep_zero_homology`, `finrank_iteratedCone_zero_homology`); this is the shape of the
source `⊕_b Č(Ω^b(D))[-b]` of the Deligne–Illusie map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace MixedFujita

universe u v

variable {k : Type u} [Field k]

section Lift

variable {W A A' B' : CochainComplex (ModuleCat.{v} k) ℕ}

theorem comp_coneStepPsi_eq_zero (ψ : A' ⟶ B') (u : W ⟶ A') (hu : u ≫ ψ = 0) (m : ℕ) :
    u.f m ≫ coneStepPsi ψ m = 0 := by
  rw [coneStepPsi, Preadditive.comp_zsmul, ← Category.assoc, ← HomologicalComplex.comp_f, hu,
    HomologicalComplex.zero_f, zero_comp, smul_zero]

/-- For `v : A ⟶ A'` and `ψ : A' ⟶ B'` with `v ≫ ψ = 0`, the chain map `a ↦ (v a, 0)` from `A`
to the cone of `ψ`. -/
noncomputable def coneStepLift (v : A ⟶ A') (ψ : A' ⟶ B') (h : v ≫ ψ = 0) :
    A ⟶ coneStep ψ where
  f m := ModuleCat.ofHom (LinearMap.inl k _ _ ∘ₗ (v.f m).hom)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [coneStep_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have h1 := congrArg (fun f => f.hom a) (v.comm i (i + 1))
    have h2 := congrArg (fun f => f.hom a) (comp_coneStepPsi_eq_zero ψ v h i)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h1 h2
    change ((A'.d i (i + 1)).hom ((v.f i).hom a),
      (coneStepPsi ψ i).hom ((v.f i).hom a) + ((shiftOne B').d i (i + 1)).hom 0) =
        ((v.f (i + 1)).hom ((A.d i (i + 1)).hom a), 0)
    rw [h1, h2, map_zero, add_zero]

theorem comp_coneStepLift_eq_zero (v : A ⟶ A') (ψ : A' ⟶ B') (h : v ≫ ψ = 0) (u : W ⟶ A)
    (hu : u ≫ v = 0) : u ≫ coneStepLift v ψ h = 0 := by
  ext m : 1
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  have h1 := congrArg (fun f => (f.f m).hom a) hu
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply] at h1
  change ((v.f m).hom ((u.f m).hom a), 0) = (0, 0)
  rw [h1]

end Lift

section ZeroCone

variable {A B : CochainComplex (ModuleCat.{v} k) ℕ}

theorem coneStepPsi_zero (m : ℕ) : coneStepPsi (0 : A ⟶ B) m = 0 := by
  rw [coneStepPsi, HomologicalComplex.zero_f, zero_comp, smul_zero]

/-- For the zero map the projection `A ⊞ B[1] → B[1]` is a chain map. -/
noncomputable def coneStepZeroSnd : coneStep (0 : A ⟶ B) ⟶ shiftOne B where
  f m := ModuleCat.ofHom (LinearMap.snd k _ _)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [coneStep_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change ((shiftOne B).d i (i + 1)).hom x.2 =
      (coneStepPsi (0 : A ⟶ B) i).hom x.1 + ((shiftOne B).d i (i + 1)).hom x.2
    rw [coneStepPsi_zero, ModuleCat.hom_zero, LinearMap.zero_apply, zero_add]

theorem coneStepInr_comp_zeroSnd : coneStepInr (0 : A ⟶ B) ≫ coneStepZeroSnd = 𝟙 _ := by
  ext m : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun s => rfl)

theorem coneStepLift_id_comp_fst :
    coneStepLift (𝟙 A) (0 : A ⟶ B) comp_zero ≫ coneStepFst (0 : A ⟶ B) = 𝟙 _ := by
  ext m : 1
  exact ModuleCat.hom_ext (LinearMap.ext fun s => rfl)

/-- **The cone of the zero map is a direct sum:**
`dim H^i(A ⊞ B[1]) = dim H^i(B[1]) + dim H^i(A)`. -/
theorem finrank_coneStep_zero_homology (i : ℕ) [FiniteDimensional k ((shiftOne B).homology i)]
    [FiniteDimensional k (A.homology i)] :
    FiniteDimensional k ((coneStep (0 : A ⟶ B)).homology i) ∧
      Module.finrank k ((coneStep (0 : A ⟶ B)).homology i) =
        Module.finrank k ((shiftOne B).homology i) + Module.finrank k (A.homology i) := by
  have hS := coneStep_shortExact (0 : A ⟶ B)
  have : FiniteDimensional k ((coneStepShortComplex (0 : A ⟶ B)).X₁.homology i) :=
    (inferInstance : FiniteDimensional k ((shiftOne B).homology i))
  have : FiniteDimensional k ((coneStepShortComplex (0 : A ⟶ B)).X₃.homology i) :=
    (inferInstance : FiniteDimensional k (A.homology i))
  have hfin := (finrank_homology_le_of_shortExact hS i).1
  change FiniteDimensional k ((coneStep (0 : A ⟶ B)).homology i) at hfin
  have hex : LinearMap.range (HomologicalComplex.homologyMap (coneStepInr (0 : A ⟶ B)) i).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (coneStepFst (0 : A ⟶ B)) i).hom :=
    (hS.homology_exact₂ i).moduleCat_range_eq_ker
  have hinj : Function.Injective
      (HomologicalComplex.homologyMap (coneStepInr (0 : A ⟶ B)) i).hom := by
    refine Function.LeftInverse.injective (g := (HomologicalComplex.homologyMap
      (coneStepZeroSnd (A := A) (B := B)) i).hom) fun z => ?_
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      coneStepInr_comp_zeroSnd, HomologicalComplex.homologyMap_id]
    rfl
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (coneStepFst (0 : A ⟶ B)) i).hom := by
    refine Function.RightInverse.surjective (g := (HomologicalComplex.homologyMap
      (coneStepLift (𝟙 A) (0 : A ⟶ B) comp_zero) i).hom) fun z => ?_
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp,
      coneStepLift_id_comp_fst, HomologicalComplex.homologyMap_id]
    rfl
  refine ⟨hfin, ?_⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker
    (HomologicalComplex.homologyMap (coneStepFst (0 : A ⟶ B)) i).hom
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, ← hex,
    LinearMap.finrank_range_of_inj hinj] at h1
  omega

end ZeroCone

theorem zeroComplex_homology_subsingleton (m : ℕ) :
    Subsingleton ((HomologicalComplex.zero : CochainComplex (ModuleCat.{v} k) ℕ).homology m) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (ShortComplex.isZero_homology_of_isZero_X₂ _ (Limits.isZero_zero (ModuleCat.{v} k)))

section Tower

variable (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0)

/-- The iterated cone of the rows `R_{j+1}, …, R_{j+n}` together with the chain map from `R_j`
induced by `δ_j`; the map kills every chain map killed by `δ_j`. -/
noncomputable def iteratedConeData : (n j : ℕ) → Σ T : CochainComplex (ModuleCat.{v} k) ℕ,
    {ψ : R j ⟶ T // ∀ (W : CochainComplex (ModuleCat.{v} k) ℕ) (u : W ⟶ R j),
      u ≫ δ j = 0 → u ≫ ψ = 0}
  | 0, _ => ⟨HomologicalComplex.zero, 0, fun _ _ _ => comp_zero⟩
  | n + 1, j =>
    ⟨coneStep (iteratedConeData n (j + 1)).2.1,
      coneStepLift (δ j) (iteratedConeData n (j + 1)).2.1
        ((iteratedConeData n (j + 1)).2.2 _ (δ j) (hδ j)),
      fun _ u hu => comp_coneStepLift_eq_zero _ _ _ u hu⟩

/-- **The iterated cone** of the rows `R_j, …, R_{j+n}`. -/
noncomputable def iteratedCone (n j : ℕ) : CochainComplex (ModuleCat.{v} k) ℕ :=
  coneStep (iteratedConeData R δ hδ n j).2.1

theorem iteratedConeData_zero_fst (j : ℕ) :
    (iteratedConeData R δ hδ 0 j).1 = HomologicalComplex.zero := rfl

theorem iteratedConeData_succ_fst (n j : ℕ) :
    (iteratedConeData R δ hδ (n + 1) j).1 = iteratedCone R δ hδ n (j + 1) := rfl

/-- **Row-filtration inequality for the iterated cone:**
`dim H^m(iteratedCone n j) ≤ Σ_{b ≤ n, b ≤ m} dim H^{m-b}(R_{j+b})`. -/
theorem finrank_iteratedCone_homology_le (hR : ∀ j m, FiniteDimensional k ((R j).homology m))
    (n : ℕ) : ∀ j m, FiniteDimensional k ((iteratedCone R δ hδ n j).homology m) ∧
      Module.finrank k ((iteratedCone R δ hδ n j).homology m) ≤
        coneFiltrationBound R (j + n + 1) j m := by
  induction n with
  | zero =>
    intro j m
    cases m with
    | zero =>
      have := hR j 0
      obtain ⟨h1, h2⟩ := finrank_coneStep_homology_zero_le (iteratedConeData R δ hδ 0 j).2.1
      refine ⟨h1, ?_⟩
      rw [coneFiltrationBound_zero R (show j < j + 0 + 1 by omega)]
      exact h2
    | succ m =>
      have := hR j (m + 1)
      have hz : Subsingleton ((iteratedConeData R δ hδ 0 j).1.homology m) :=
        zeroComplex_homology_subsingleton m
      have : FiniteDimensional k ((iteratedConeData R δ hδ 0 j).1.homology m) := inferInstance
      obtain ⟨h1, h2⟩ := finrank_coneStep_homology_succ_le (iteratedConeData R δ hδ 0 j).2.1 m
      refine ⟨h1, ?_⟩
      rw [Module.finrank_zero_of_subsingleton (M := (iteratedConeData R δ hδ 0 j).1.homology m),
        zero_add] at h2
      rw [coneFiltrationBound_succ R (show j < j + 0 + 1 by omega), Nat.add_zero,
        coneFiltrationBound_top, zero_add]
      exact h2
  | succ n ih =>
    intro j m
    cases m with
    | zero =>
      have := hR j 0
      obtain ⟨h1, h2⟩ := finrank_coneStep_homology_zero_le (iteratedConeData R δ hδ (n + 1) j).2.1
      refine ⟨h1, ?_⟩
      rw [coneFiltrationBound_zero R (show j < j + (n + 1) + 1 by omega)]
      exact h2
    | succ m =>
      have := hR j (m + 1)
      have : FiniteDimensional k ((iteratedConeData R δ hδ (n + 1) j).1.homology m) :=
        (ih (j + 1) m).1
      obtain ⟨h1, h2⟩ :=
        finrank_coneStep_homology_succ_le (iteratedConeData R δ hδ (n + 1) j).2.1 m
      refine ⟨h1, ?_⟩
      rw [coneFiltrationBound_succ R (show j < j + (n + 1) + 1 by omega),
        show j + (n + 1) + 1 = j + 1 + n + 1 by omega]
      exact h2.trans (Nat.add_le_add_right (ih (j + 1) m).2 _)


/-- With zero vertical maps every map of the recursion is zero. -/
theorem iteratedConeData_zero_snd (n j : ℕ) :
    (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) n j).2.1 = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
    ext m : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun a => rfl)

/-- **With zero vertical maps the iterated cone is a direct sum:**
`dim H^m = Σ_{b ≤ n, b ≤ m} dim H^{m-b}(R_{j+b})`. -/
theorem finrank_iteratedCone_zero_homology (hR : ∀ j m, FiniteDimensional k ((R j).homology m))
    (n : ℕ) : ∀ j m,
      FiniteDimensional k ((iteratedCone R (fun _ => 0) (fun _ => comp_zero) n j).homology m) ∧
      Module.finrank k ((iteratedCone R (fun _ => 0) (fun _ => comp_zero) n j).homology m) =
        coneFiltrationBound R (j + n + 1) j m := by
  induction n with
  | zero =>
    intro j m
    have := hR j m
    have key : ∀ i, FiniteDimensional k
        ((shiftOne (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1).homology i) ∧
        Module.finrank k
          ((shiftOne (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1).homology i) = 0 := by
      intro i
      cases i with
      | zero =>
        have := shiftOne_homology_zero_subsingleton
          (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1
        exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩
      | succ i =>
        have : Subsingleton
            ((iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1.homology i) :=
          zeroComplex_homology_subsingleton i
        let e := (shiftOneHomologyIso
          (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1 i).toLinearEquiv
        have : FiniteDimensional k
            ((iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1.homology i) :=
          inferInstance
        refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
        rw [e.finrank_eq]
        exact Module.finrank_zero_of_subsingleton
    have := (key m).1
    unfold iteratedCone
    rw [iteratedConeData_zero_snd]
    obtain ⟨h1, h2⟩ := finrank_coneStep_zero_homology
      (A := R j) (B := (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) 0 j).1) m
    refine ⟨h1, ?_⟩
    rw [h2, (key m).2, zero_add]
    cases m with
    | zero => rw [coneFiltrationBound_zero R (show j < j + 0 + 1 by omega)]; rfl
    | succ m =>
      rw [coneFiltrationBound_succ R (show j < j + 0 + 1 by omega), Nat.add_zero,
        coneFiltrationBound_top, zero_add]
      rfl
  | succ n ih =>
    intro j m
    have := hR j m
    have key : ∀ i, FiniteDimensional k
        ((shiftOne (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) (n + 1) j).1).homology i) ∧
        Module.finrank k
          ((shiftOne (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) (n + 1) j).1).homology i) =
          if i = 0 then 0 else coneFiltrationBound R (j + 1 + n + 1) (j + 1) (i - 1) := by
      intro i
      cases i with
      | zero =>
        have := shiftOne_homology_zero_subsingleton
          (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) (n + 1) j).1
        exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩
      | succ i =>
        have := (ih (j + 1) i).1
        let e := (shiftOneHomologyIso
          (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) (n + 1) j).1 i).toLinearEquiv
        have : FiniteDimensional k
            ((iteratedConeData R (fun _ => 0) (fun _ => comp_zero) (n + 1) j).1.homology i) :=
          (ih (j + 1) i).1
        refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        rw [e.finrank_eq]
        exact (ih (j + 1) i).2
    have := (key m).1
    unfold iteratedCone
    rw [iteratedConeData_zero_snd]
    obtain ⟨h1, h2⟩ := finrank_coneStep_zero_homology
      (A := R j) (B := (iteratedConeData R (fun _ => 0) (fun _ => comp_zero) (n + 1) j).1) m
    refine ⟨h1, ?_⟩
    rw [h2, (key m).2]
    cases m with
    | zero =>
      simp only [↓reduceIte, zero_add]
      rw [coneFiltrationBound_zero R (show j < j + (n + 1) + 1 by omega)]
      rfl
    | succ m =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [coneFiltrationBound_succ R (show j < j + (n + 1) + 1 by omega),
        show j + (n + 1) + 1 = j + 1 + n + 1 by omega]
      rfl
end Tower

end MixedFujita
