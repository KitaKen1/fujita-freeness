/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HomologyDimensionInequality
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
The cone step of the row filtration (step 10).

For a chain map `φ : A ⟶ B` of `ℕ`-indexed cochain complexes of vector spaces, let `B[1]` be `B`
shifted by one (`0, B⁰, B¹, …`, Mathlib's extension along `i ↦ i + 1`, `shiftOne`). The complex
`T = A ⊞ B[1]` with differential `D(a, s) = (d a, (-1)^m φ a + d s)` in degree `m` (`coneStep`;
`d ∘ d = 0` because `φ` is a chain map) sits in the degreewise split short exact sequence
`0 → B[1] → T → A → 0` (`coneStep_shortExact`). Hence
`dim H^{j+1}(T) ≤ dim H^j(B) + dim H^{j+1}(A)` and `dim H^0(T) ≤ dim H^0(A)`
(`finrank_coneStep_homology_succ_le`, `finrank_coneStep_homology_zero_le`). For iterated cones,
i.e. short exact sequences `0 → T_{j+1}[1] → T_j → R_j → 0` for `j < N` with `T_N` acyclic, induction
gives the row-filtration inequality `dim H^m(T_0) ≤ Σ_{b < N, b ≤ m} dim H^{m-b}(R_b)`
(`finrank_homology_le_of_coneFiltration`). With `R_b` the Čech complex of `Ω^b(D)` this is the
Hodge-to-de Rham bound used by Deligne–Illusie for the Čech–de Rham total complex.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace MixedFujita

universe u v

variable {k : Type u} [Field k]

/-- The shift `i ↦ i + 1` of `ℕ`-indexed cochain complexes. -/
abbrev shiftOneEmbedding : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.embeddingUp'Add (1 : ℕ) 1

/-- `B` shifted by one: `0, B⁰, B¹, …`. -/
noncomputable abbrev shiftOne (B : CochainComplex (ModuleCat.{v} k) ℕ) :
    CochainComplex (ModuleCat.{v} k) ℕ :=
  B.extend shiftOneEmbedding

variable {A B : CochainComplex (ModuleCat.{v} k) ℕ} (φ : A ⟶ B)

/-- The component `(-1)^m φ_m : A^m → (B[1])^{m+1}` of the cone differential. -/
noncomputable def coneStepPsi (m : ℕ) : A.X m ⟶ (shiftOne B).X (m + 1) :=
  ((-1 : ℤ) ^ m) • (φ.f m ≫
    (B.extendXIso shiftOneEmbedding (show shiftOneEmbedding.f m = m + 1 from rfl)).inv)

theorem coneStepPsi_comp_d (m : ℕ) :
    A.d m (m + 1) ≫ coneStepPsi φ (m + 1) + coneStepPsi φ m ≫ (shiftOne B).d (m + 1) (m + 1 + 1) =
      0 := by
  have hd := B.extend_d_eq shiftOneEmbedding (show shiftOneEmbedding.f m = m + 1 from rfl)
    (show shiftOneEmbedding.f (m + 1) = m + 1 + 1 from rfl)
  have hc := φ.comm m (m + 1)
  simp only [coneStepPsi, hd, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc (A.d m (m + 1)), ← hc, Category.assoc, pow_succ, mul_neg_one, neg_smul,
    neg_add_cancel]

/-- The cone differential `D(a, s) = (d a, (-1)^m φ a + d s)`. -/
noncomputable def coneStepD (m : ℕ) :
    ModuleCat.of k (A.X m × (shiftOne B).X m) ⟶
      ModuleCat.of k (A.X (m + 1) × (shiftOne B).X (m + 1)) :=
  ModuleCat.ofHom (LinearMap.prod ((A.d m (m + 1)).hom ∘ₗ LinearMap.fst k _ _)
    ((coneStepPsi φ m).hom ∘ₗ LinearMap.fst k _ _ +
      ((shiftOne B).d m (m + 1)).hom ∘ₗ LinearMap.snd k _ _))

theorem coneStepD_apply (m : ℕ) (x : A.X m × (shiftOne B).X m) :
    (coneStepD φ m).hom x =
      ((A.d m (m + 1)).hom x.1, (coneStepPsi φ m).hom x.1 + ((shiftOne B).d m (m + 1)).hom x.2) :=
  rfl

theorem coneStepD_comp (m : ℕ) : coneStepD φ m ≫ coneStepD φ (m + 1) = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have h1 := congrArg (fun f => f.hom x.1) (A.d_comp_d m (m + 1) (m + 1 + 1))
  have h2 := congrArg (fun f => f.hom x.2) ((shiftOne B).d_comp_d m (m + 1) (m + 1 + 1))
  have h3 := congrArg (fun f => f.hom x.1) (coneStepPsi_comp_d φ m)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
    ModuleCat.hom_add, LinearMap.add_apply] at h1 h2 h3
  change ((A.d (m + 1) (m + 1 + 1)).hom ((A.d m (m + 1)).hom x.1),
    (coneStepPsi φ (m + 1)).hom ((A.d m (m + 1)).hom x.1) +
      ((shiftOne B).d (m + 1) (m + 1 + 1)).hom
        ((coneStepPsi φ m).hom x.1 + ((shiftOne B).d m (m + 1)).hom x.2)) = (0, 0)
  rw [map_add, h1, h2, add_zero, h3]

/-- **The cone step** `T = A ⊞ B[1]`. -/
noncomputable def coneStep : CochainComplex (ModuleCat.{v} k) ℕ :=
  CochainComplex.of (fun m => ModuleCat.of k (A.X m × (shiftOne B).X m)) (coneStepD φ)
    (coneStepD_comp φ)

theorem coneStep_d (m : ℕ) : (coneStep φ).d m (m + 1) = coneStepD φ m := by
  unfold coneStep
  exact CochainComplex.of_d (fun m => ModuleCat.of k (A.X m × (shiftOne B).X m)) (coneStepD φ) m

/-- The inclusion `B[1] → T`. -/
noncomputable def coneStepInr : shiftOne B ⟶ coneStep φ where
  f m := ModuleCat.ofHom (LinearMap.inr k _ _)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [coneStep_d]
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    change ((A.d i (i + 1)).hom 0, (coneStepPsi φ i).hom 0 + ((shiftOne B).d i (i + 1)).hom s) =
      (0, ((shiftOne B).d i (i + 1)).hom s)
    rw [map_zero, map_zero, zero_add]

/-- The projection `T → A`. -/
noncomputable def coneStepFst : coneStep φ ⟶ A where
  f m := ModuleCat.ofHom (LinearMap.fst k _ _)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [coneStep_d]
    rfl

/-- **The short exact sequence `0 → B[1] → T → A → 0`.** -/
noncomputable def coneStepShortComplex : ShortComplex (CochainComplex (ModuleCat.{v} k) ℕ) :=
  ShortComplex.mk (coneStepInr φ) (coneStepFst φ) (by
    ext m : 1
    exact ModuleCat.hom_ext (LinearMap.ext fun s => rfl))

theorem coneStep_shortExact : (coneStepShortComplex φ).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun m => ?_
  exact ShortComplex.Splitting.shortExact
    { r := ModuleCat.ofHom (LinearMap.snd k _ _)
      s := ModuleCat.ofHom (LinearMap.inl k _ _)
      f_r := ModuleCat.hom_ext (LinearMap.ext fun s => rfl)
      s_g := ModuleCat.hom_ext (LinearMap.ext fun s => rfl)
      id := ModuleCat.hom_ext (LinearMap.ext fun x => by
        change (0, x.2) + (x.1, 0) = x
        exact Prod.ext (zero_add x.1) (add_zero x.2)) }

section Homology

variable {B' X R : CochainComplex (ModuleCat.{v} k) ℕ}

/-- `H^{j+1}(B[1]) ≅ H^j(B)`. -/
noncomputable def shiftOneHomologyIso (B' : CochainComplex (ModuleCat.{v} k) ℕ) (j : ℕ) :
    (shiftOne B').homology (j + 1) ≅ B'.homology j :=
  B'.extendHomologyIso shiftOneEmbedding (show shiftOneEmbedding.f j = j + 1 from rfl)

/-- `H^0(B[1]) = 0`. -/
theorem shiftOne_homology_zero_subsingleton (B' : CochainComplex (ModuleCat.{v} k) ℕ) :
    Subsingleton ((shiftOne B').homology 0) := by
  have h := B'.extend_exactAt shiftOneEmbedding 0 (fun j => by
    change j + 1 ≠ 0
    omega)
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h
  exact ModuleCat.isZero_iff_subsingleton.mp h

/-- For a short exact sequence `0 → B[1] → X → R → 0`:
`dim H^{j+1}(X) ≤ dim H^j(B) + dim H^{j+1}(R)`. -/
theorem finrank_homology_succ_le_of_shiftOne (f : shiftOne B' ⟶ X) (g : X ⟶ R) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) (j : ℕ) [FiniteDimensional k (B'.homology j)]
    [FiniteDimensional k (R.homology (j + 1))] :
    FiniteDimensional k (X.homology (j + 1)) ∧
      Module.finrank k (X.homology (j + 1)) ≤
        Module.finrank k (B'.homology j) + Module.finrank k (R.homology (j + 1)) := by
  let e := (shiftOneHomologyIso B' j).toLinearEquiv
  have : FiniteDimensional k ((shiftOne B').homology (j + 1)) := LinearEquiv.finiteDimensional e.symm
  obtain ⟨hfin, hle⟩ := finrank_homology_le_of_shortExact hS (j + 1)
  refine ⟨hfin, ?_⟩
  have he : Module.finrank k ((shiftOne B').homology (j + 1)) = Module.finrank k (B'.homology j) :=
    e.finrank_eq
  change Module.finrank k (X.homology (j + 1)) ≤
    Module.finrank k ((shiftOne B').homology (j + 1)) + Module.finrank k (R.homology (j + 1)) at hle
  rw [he] at hle
  exact hle

/-- For a short exact sequence `0 → B[1] → X → R → 0`: `dim H^0(X) ≤ dim H^0(R)`. -/
theorem finrank_homology_zero_le_of_shiftOne (f : shiftOne B' ⟶ X) (g : X ⟶ R) (w : f ≫ g = 0)
    (hS : (ShortComplex.mk f g w).ShortExact) [FiniteDimensional k (R.homology 0)] :
    FiniteDimensional k (X.homology 0) ∧
      Module.finrank k (X.homology 0) ≤ Module.finrank k (R.homology 0) := by
  have := shiftOne_homology_zero_subsingleton B'
  have : FiniteDimensional k ((shiftOne B').homology 0) := inferInstance
  obtain ⟨hfin, hle⟩ := finrank_homology_le_of_shortExact hS 0
  refine ⟨hfin, ?_⟩
  change Module.finrank k (X.homology 0) ≤
    Module.finrank k ((shiftOne B').homology 0) + Module.finrank k (R.homology 0) at hle
  rw [Module.finrank_zero_of_subsingleton (M := (shiftOne B').homology 0), zero_add] at hle
  exact hle

/-- **The cone step bound** `dim H^{j+1}(T) ≤ dim H^j(B) + dim H^{j+1}(A)`. -/
theorem finrank_coneStep_homology_succ_le (j : ℕ) [FiniteDimensional k (B.homology j)]
    [FiniteDimensional k (A.homology (j + 1))] :
    FiniteDimensional k ((coneStep φ).homology (j + 1)) ∧
      Module.finrank k ((coneStep φ).homology (j + 1)) ≤
        Module.finrank k (B.homology j) + Module.finrank k (A.homology (j + 1)) :=
  finrank_homology_succ_le_of_shiftOne (coneStepInr φ) (coneStepFst φ) _ (coneStep_shortExact φ) j

/-- The cone step bound in degree `0`: `dim H^0(T) ≤ dim H^0(A)`. -/
theorem finrank_coneStep_homology_zero_le [FiniteDimensional k (A.homology 0)] :
    FiniteDimensional k ((coneStep φ).homology 0) ∧
      Module.finrank k ((coneStep φ).homology 0) ≤ Module.finrank k (A.homology 0) :=
  finrank_homology_zero_le_of_shiftOne (coneStepInr φ) (coneStepFst φ) _ (coneStep_shortExact φ)

end Homology

section ConeFiltration

/-- `dim H^m(R_j)`. -/
noncomputable def rowHomologyRank (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (j m : ℕ) : ℕ :=
  Module.finrank k ((R j).homology m)

/-- The bound `Σ_{b < N - j, b ≤ m} dim H^{m-b}(R_{j+b})` of an iterated cone. -/
noncomputable def coneFiltrationBound (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (N j m : ℕ) :
    ℕ :=
  ∑ b ∈ Finset.range (N - j), if b ≤ m then rowHomologyRank R (j + b) (m - b) else 0

theorem coneFiltrationBound_top (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (N m : ℕ) :
    coneFiltrationBound R N N m = 0 := by
  rw [coneFiltrationBound, Nat.sub_self, Finset.sum_range_zero]

theorem coneFiltrationBound_succ (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) {N j : ℕ}
    (hj : j < N) (m : ℕ) :
    coneFiltrationBound R N j (m + 1) =
      coneFiltrationBound R N (j + 1) m + rowHomologyRank R j (m + 1) := by
  unfold coneFiltrationBound
  rw [show N - j = (N - (j + 1)) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.zero_le, ↓reduceIte, add_zero, Nat.sub_zero]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ≤ m
  · simp only [show b + 1 ≤ m + 1 by omega, hb, ↓reduceIte]
    rw [show j + (b + 1) = j + 1 + b by omega, show m + 1 - (b + 1) = m - b by omega]
  · simp only [show ¬ b + 1 ≤ m + 1 by omega, hb, ↓reduceIte]

theorem coneFiltrationBound_zero (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) {N j : ℕ}
    (hj : j < N) :
    coneFiltrationBound R N j 0 = rowHomologyRank R j 0 := by
  unfold coneFiltrationBound
  rw [show N - j = (N - (j + 1)) + 1 by omega, Finset.sum_range_succ']
  simp only [le_refl, ↓reduceIte, add_zero, Nat.sub_zero]
  rw [Finset.sum_eq_zero fun b _ => by simp only [show ¬ b + 1 ≤ 0 by omega, ↓reduceIte],
    zero_add]

/-- **Row-filtration inequality for iterated cones.** If `0 → T_{j+1}[1] → T_j → R_j → 0` are short
exact for `j < N` and `T_N` is acyclic, then
`dim H^m(T_0) ≤ Σ_{b < N, b ≤ m} dim H^{m-b}(R_b)`. -/
theorem finrank_homology_le_of_coneFiltration {N : ℕ}
    (T R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (incl : ∀ j, shiftOne (T (j + 1)) ⟶ T j)
    (proj : ∀ j, T j ⟶ R j) (w : ∀ j, incl j ≫ proj j = 0)
    (hses : ∀ j < N, (ShortComplex.mk (incl j) (proj j) (w j)).ShortExact)
    (htop : ∀ m, Subsingleton ((T N).homology m))
    (hR : ∀ j < N, ∀ m, FiniteDimensional k ((R j).homology m)) (m : ℕ) :
    FiniteDimensional k ((T 0).homology m) ∧
      Module.finrank k ((T 0).homology m) ≤ coneFiltrationBound R N 0 m := by
  have key : ∀ a, a ≤ N → ∀ m, FiniteDimensional k ((T (N - a)).homology m) ∧
      Module.finrank k ((T (N - a)).homology m) ≤ coneFiltrationBound R N (N - a) m := by
    intro a
    induction a with
    | zero =>
      intro _ m
      rw [Nat.sub_zero, coneFiltrationBound_top]
      have := htop m
      refine ⟨inferInstance, ?_⟩
      rw [Module.finrank_zero_of_subsingleton]
    | succ a ih =>
      intro ha m
      have hP := ih (by omega)
      rw [show N - a = (N - (a + 1)) + 1 by omega] at hP
      have hlt : N - (a + 1) < N := by omega
      generalize N - (a + 1) = j at hP hlt ⊢
      cases m with
      | zero =>
        have := hR j hlt 0
        obtain ⟨hfin, hle⟩ := finrank_homology_zero_le_of_shiftOne (incl j) (proj j) (w j)
          (hses j hlt)
        exact ⟨hfin, (coneFiltrationBound_zero R hlt).symm ▸ hle⟩
      | succ m =>
        have := (hP m).1
        have := hR j hlt (m + 1)
        obtain ⟨hfin, hle⟩ := finrank_homology_succ_le_of_shiftOne (incl j) (proj j) (w j)
          (hses j hlt) m
        refine ⟨hfin, ?_⟩
        rw [coneFiltrationBound_succ R hlt]
        exact hle.trans (Nat.add_le_add_right (hP m).2 _)
  have h0 := key N le_rfl m
  rwa [Nat.sub_self] at h0

end ConeFiltration

end MixedFujita
