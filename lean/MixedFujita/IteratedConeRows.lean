/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IteratedCone

/-!
The rows of an iterated cone (step 10).

The iterated cone `T(n, j)` of the rows `R_j, …, R_{j+n}` (check 434) is in degree `m` the
product `R_j^m × R_{j+1}^{m-1} × ⋯`. The component of row `i = j + b` in degree `q = m - b`
(`coneRowComp`) and the inclusion of that row (`coneRowIncl`) are linear maps; the row indices and
degrees are carried by equations `j + b = i`, `q + b = m`, so that no casts appear in the
recursion. A row component of an included row is the identity on the same row
(`coneRowComp_coneRowIncl_self`) and zero on the other rows (`coneRowComp_coneRowIncl_of_ne`), and
an element is determined by its row components (`coneRow_ext`). The differential of the iterated
cone in row components is `(D x)_0 = d(x_0)` and `(D x)_{b+1} = d(x_{b+1}) + (-1)^{q+1} δ(x_b)` with
`q + 1` the degree of `x_b` (`coneRowComp_zero_d`, `coneRowComp_succ_d`, and
`coneRowComp_succ_d_zero` in degree `0`). This is the elementwise description of the Čech–de Rham
total complex used to define the Deligne–Illusie map by components and to run the staircase
argument for its injectivity.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace MixedFujita

universe u v

variable {k : Type u} [Field k]

section Rows

variable (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0)

/-- The identification of `(R i).X q` with `(R j).X m` along `i = j` and `q = m`. -/
noncomputable def rowCast {i j q m : ℕ} (hi : i = j) (hq : q = m) :
    (R i).X q →ₗ[k] (R j).X m := by
  subst hi hq
  exact LinearMap.id

theorem rowCast_apply_self {i q : ℕ} (hi : i = i) (hq : q = q) (y : (R i).X q) :
    rowCast R hi hq y = y := rfl

theorem rowCast_rowCast {i j l q m r : ℕ} (hi : i = j) (hq : q = m) (hj : j = l) (hm : m = r)
    (y : (R i).X q) :
    rowCast R hj hm (rowCast R hi hq y) = rowCast R (hi.trans hj) (hq.trans hm) y := by
  subst hi hq hj hm
  rfl

/-- The first component `T(n, j)^m → R_j^m` of an iterated cone. -/
noncomputable def coneFstMap (n j m : ℕ) : (iteratedCone R δ hδ n j).X m →ₗ[k] (R j).X m :=
  LinearMap.fst k _ _

/-- The inclusion `R_j^m → T(n, j)^m` of the first row. -/
noncomputable def coneInlMap (n j m : ℕ) : (R j).X m →ₗ[k] (iteratedCone R δ hδ n j).X m :=
  LinearMap.inl k _ _

/-- The second component `T(n + 1, j)^{m+1} → T(n, j + 1)^m` of an iterated cone. -/
noncomputable def coneSndMap (n j m : ℕ) :
    (iteratedCone R δ hδ (n + 1) j).X (m + 1) →ₗ[k] (iteratedCone R δ hδ n (j + 1)).X m :=
  ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
    (show shiftOneEmbedding.f m = m + 1 from rfl)).hom.hom ∘ₗ LinearMap.snd k _ _

/-- The inclusion `T(n, j + 1)^m → T(n + 1, j)^{m+1}` of the higher rows. -/
noncomputable def coneInrMap (n j m : ℕ) :
    (iteratedCone R δ hδ n (j + 1)).X m →ₗ[k] (iteratedCone R δ hδ (n + 1) j).X (m + 1) :=
  LinearMap.inr k _ _ ∘ₗ ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
    (show shiftOneEmbedding.f m = m + 1 from rfl)).inv.hom

theorem coneFstMap_coneInlMap (n j m : ℕ) (y : (R j).X m) :
    coneFstMap R δ hδ n j m (coneInlMap R δ hδ n j m y) = y := rfl

theorem coneFstMap_coneInrMap (n j m : ℕ) (z : (iteratedCone R δ hδ n (j + 1)).X m) :
    coneFstMap R δ hδ (n + 1) j (m + 1) (coneInrMap R δ hδ n j m z) = 0 := rfl

theorem coneSndMap_coneInlMap (n j m : ℕ) (y : (R j).X (m + 1)) :
    coneSndMap R δ hδ n j m (coneInlMap R δ hδ (n + 1) j (m + 1) y) = 0 := by
  change ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
    (show shiftOneEmbedding.f m = m + 1 from rfl)).hom.hom 0 = 0
  exact map_zero _

theorem coneSndMap_coneInrMap (n j m : ℕ) (z : (iteratedCone R δ hδ n (j + 1)).X m) :
    coneSndMap R δ hδ n j m (coneInrMap R δ hδ n j m z) = z := by
  change ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
    (show shiftOneEmbedding.f m = m + 1 from rfl)).hom.hom
      (((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
        (show shiftOneEmbedding.f m = m + 1 from rfl)).inv.hom z) = z
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
    LinearMap.id_apply]

/-- An element of `T(n + 1, j)^{m+1}` is determined by its two components. -/
theorem cone_ext_succ (n j m : ℕ) (x x' : (iteratedCone R δ hδ (n + 1) j).X (m + 1))
    (h1 : coneFstMap R δ hδ (n + 1) j (m + 1) x = coneFstMap R δ hδ (n + 1) j (m + 1) x')
    (h2 : coneSndMap R δ hδ n j m x = coneSndMap R δ hδ n j m x') : x = x' := by
  have h2' := congrArg ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
    (show shiftOneEmbedding.f m = m + 1 from rfl)).inv.hom h2
  change ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
      (show shiftOneEmbedding.f m = m + 1 from rfl)).inv.hom
      (((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
        (show shiftOneEmbedding.f m = m + 1 from rfl)).hom.hom x.2) =
    ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
      (show shiftOneEmbedding.f m = m + 1 from rfl)).inv.hom
      (((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
        (show shiftOneEmbedding.f m = m + 1 from rfl)).hom.hom x'.2) at h2'
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
    LinearMap.id_apply, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id,
    ModuleCat.hom_id, LinearMap.id_apply] at h2'
  exact Prod.ext h1 h2'

/-- An element of `T(n, j)^0` is determined by its first component. -/
theorem cone_ext_zero (n j : ℕ) (x x' : (iteratedCone R δ hδ n j).X 0)
    (h1 : coneFstMap R δ hδ n j 0 x = coneFstMap R δ hδ n j 0 x') : x = x' := by
  have hz := shiftOne_homology_zero_subsingleton (iteratedConeData R δ hδ n j).1
  have hX : IsZero ((shiftOne (iteratedConeData R δ hδ n j).1).X 0) :=
    (iteratedConeData R δ hδ n j).1.isZero_extend_X shiftOneEmbedding 0 (fun i => by
      change i + 1 ≠ 0
      omega)
  have hs : Subsingleton ((shiftOne (iteratedConeData R δ hδ n j).1).X 0) :=
    ModuleCat.isZero_iff_subsingleton.mp hX
  exact Prod.ext h1 (Subsingleton.elim _ _)

/-- **The inclusion of row `i = j + b` in degree `q`** into the iterated cone `T(n, j)` in degree
`m = q + b`. -/
noncomputable def coneRowIncl : (n j b i q m : ℕ) → j + b = i → q + b = m →
    ((R i).X q →ₗ[k] (iteratedCone R δ hδ n j).X m)
  | n, j, 0, _, _, m, hi, hq => coneInlMap R δ hδ n j m ∘ₗ rowCast R (by omega) (by omega)
  | 0, _, _ + 1, _, _, _, _, _ => 0
  | _ + 1, _, _ + 1, _, _, 0, _, hq => absurd hq (by omega)
  | n + 1, j, b + 1, i, q, m + 1, hi, hq =>
    coneInrMap R δ hδ n j m ∘ₗ coneRowIncl n (j + 1) b i q m (by omega) (by omega)

/-- **The component of row `i = j + b` in degree `q`** of an element of `T(n, j)` in degree
`m = q + b`. -/
noncomputable def coneRowComp : (n j b i q m : ℕ) → j + b = i → q + b = m →
    ((iteratedCone R δ hδ n j).X m →ₗ[k] (R i).X q)
  | n, j, 0, _, _, m, hi, hq => rowCast R (by omega) (by omega) ∘ₗ coneFstMap R δ hδ n j m
  | 0, _, _ + 1, _, _, _, _, _ => 0
  | _ + 1, _, _ + 1, _, _, 0, _, hq => absurd hq (by omega)
  | n + 1, j, b + 1, i, q, m + 1, hi, hq =>
    coneRowComp n (j + 1) b i q m (by omega) (by omega) ∘ₗ coneSndMap R δ hδ n j m

theorem coneRowComp_coneRowIncl_self (b : ℕ) : ∀ (n j i q m : ℕ) (hi hi' : j + b = i)
    (hq hq' : q + b = m), b ≤ n → ∀ y : (R i).X q,
    coneRowComp R δ hδ n j b i q m hi hq (coneRowIncl R δ hδ n j b i q m hi' hq' y) = y := by
  induction b with
  | zero =>
    intro n j i q m hi hi' hq hq' _ y
    subst hi hq
    simp only [coneRowComp, coneRowIncl, LinearMap.comp_apply, coneFstMap_coneInlMap,
      rowCast_rowCast, rowCast_apply_self]
  | succ b ih =>
    intro n j i q m hi hi' hq hq' hb y
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [coneRowComp, coneRowIncl, LinearMap.comp_apply, coneSndMap_coneInrMap]
    exact ih n (j + 1) i q m _ _ _ _ (by omega) y

theorem coneRowComp_succ_coneInlMap (b : ℕ) : ∀ (n j i q m : ℕ) (hi : j + (b + 1) = i)
    (hq : q + (b + 1) = m) (y : (R j).X m),
    coneRowComp R δ hδ n j (b + 1) i q m hi hq (coneInlMap R δ hδ n j m y) = 0 := by
  intro n j i q m hi hq y
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  cases n with
  | zero => rfl
  | succ n =>
    simp only [coneRowComp, LinearMap.comp_apply, coneSndMap_coneInlMap, map_zero]

theorem coneRowComp_zero_coneInrMap (n j i q m : ℕ) (hi : j + 0 = i) (hq : q + 0 = m + 1)
    (z : (iteratedCone R δ hδ n (j + 1)).X m) :
    coneRowComp R δ hδ (n + 1) j 0 i q (m + 1) hi hq (coneInrMap R δ hδ n j m z) = 0 := by
  simp only [coneRowComp, LinearMap.comp_apply, coneFstMap_coneInrMap, map_zero]

/-- **A row component of a different row vanishes.** -/
theorem coneRowComp_coneRowIncl_of_ne (b : ℕ) : ∀ (b' n j i i' q q' m : ℕ) (hi : j + b = i)
    (hq : q + b = m) (hi' : j + b' = i') (hq' : q' + b' = m), b ≠ b' → ∀ y : (R i).X q,
    coneRowComp R δ hδ n j b' i' q' m hi' hq' (coneRowIncl R δ hδ n j b i q m hi hq y) = 0 := by
  induction b with
  | zero =>
    intro b' n j i i' q q' m hi hq hi' hq' hne y
    obtain ⟨b', rfl⟩ : ∃ b'', b' = b'' + 1 := ⟨b' - 1, by omega⟩
    simp only [coneRowIncl, LinearMap.comp_apply]
    exact coneRowComp_succ_coneInlMap R δ hδ b' n j i' q' m hi' hq' _
  | succ b ih =>
    intro b' n j i i' q q' m hi hq hi' hq' hne y
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases n with
    | zero =>
      simp only [coneRowIncl, LinearMap.zero_apply, map_zero]
    | succ n =>
      cases b' with
      | zero =>
        simp only [coneRowIncl, LinearMap.comp_apply]
        exact coneRowComp_zero_coneInrMap R δ hδ n j i' q' m hi' hq' _
      | succ b' =>
        simp only [coneRowIncl, coneRowComp, LinearMap.comp_apply, coneSndMap_coneInrMap]
        exact ih b' n (j + 1) i i' q q' m _ _ _ _ (by omega) y

/-- The iterated cone of a single row: the second component is zero. -/
theorem cone_ext_zero_rows (j m : ℕ) (x x' : (iteratedCone R δ hδ 0 j).X m)
    (h1 : coneFstMap R δ hδ 0 j m x = coneFstMap R δ hδ 0 j m x') : x = x' := by
  have hX : IsZero ((shiftOne (iteratedConeData R δ hδ 0 j).1).X m) := by
    cases m with
    | zero =>
      exact (iteratedConeData R δ hδ 0 j).1.isZero_extend_X shiftOneEmbedding 0 (fun i => by
        change i + 1 ≠ 0
        omega)
    | succ m =>
      exact IsZero.of_iso (Limits.isZero_zero (ModuleCat.{v} k))
        ((iteratedConeData R δ hδ 0 j).1.extendXIso shiftOneEmbedding
          (show shiftOneEmbedding.f m = m + 1 from rfl))
  have hs : Subsingleton ((shiftOne (iteratedConeData R δ hδ 0 j).1).X m) :=
    ModuleCat.isZero_iff_subsingleton.mp hX
  exact Prod.ext h1 (Subsingleton.elim _ _)

/-- **An element of an iterated cone is determined by its row components.** -/
theorem coneRow_ext (n : ℕ) : ∀ (j m : ℕ) (x x' : (iteratedCone R δ hδ n j).X m),
    (∀ (b i q : ℕ) (hi : j + b = i) (hq : q + b = m), b ≤ n →
      coneRowComp R δ hδ n j b i q m hi hq x = coneRowComp R δ hδ n j b i q m hi hq x') →
    x = x' := by
  induction n with
  | zero =>
    intro j m x x' h
    refine cone_ext_zero_rows R δ hδ j m x x' ?_
    have := h 0 j m rfl rfl le_rfl
    simpa only [coneRowComp, LinearMap.comp_apply, rowCast_apply_self] using this
  | succ n ih =>
    intro j m x x' h
    have h0 := h 0 j m rfl rfl (Nat.zero_le _)
    simp only [coneRowComp, LinearMap.comp_apply, rowCast_apply_self] at h0
    cases m with
    | zero => exact cone_ext_zero R δ hδ (n + 1) j x x' h0
    | succ m =>
      refine cone_ext_succ R δ hδ n j m x x' h0 (ih (j + 1) m _ _ fun b i q hi hq hb => ?_)
      have := h (b + 1) i q (by omega) (by omega) (by omega)
      simpa only [coneRowComp, LinearMap.comp_apply] using this

theorem coneFstMap_d (n j m : ℕ) (x : (iteratedCone R δ hδ n j).X m) :
    coneFstMap R δ hδ n j (m + 1) (((iteratedCone R δ hδ n j).d m (m + 1)).hom x) =
      ((R j).d m (m + 1)).hom (coneFstMap R δ hδ n j m x) := by
  have h := coneStep_d (iteratedConeData R δ hδ n j).2.1 m
  change coneFstMap R δ hδ n j (m + 1)
    (((coneStep (iteratedConeData R δ hδ n j).2.1).d m (m + 1)).hom x) = _
  rw [h]
  rfl

theorem coneSndMap_d (n j m : ℕ) (x : (iteratedCone R δ hδ (n + 1) j).X (m + 1)) :
    coneSndMap R δ hδ n j (m + 1) (((iteratedCone R δ hδ (n + 1) j).d (m + 1) (m + 1 + 1)).hom x) =
      ((-1 : ℤ) ^ (m + 1)) • coneInlMap R δ hδ n (j + 1) (m + 1)
          (((δ j).f (m + 1)).hom (coneFstMap R δ hδ (n + 1) j (m + 1) x)) +
        ((iteratedCone R δ hδ n (j + 1)).d m (m + 1)).hom (coneSndMap R δ hδ n j m x) := by
  have h := coneStep_d (iteratedConeData R δ hδ (n + 1) j).2.1 (m + 1)
  have hd := (iteratedConeData R δ hδ (n + 1) j).1.extend_d_eq shiftOneEmbedding
    (show shiftOneEmbedding.f m = m + 1 from rfl)
    (show shiftOneEmbedding.f (m + 1) = m + 1 + 1 from rfl)
  have hinv : ∀ z, ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
      (show shiftOneEmbedding.f (m + 1) = m + 1 + 1 from rfl)).hom.hom
      (((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
        (show shiftOneEmbedding.f (m + 1) = m + 1 + 1 from rfl)).inv.hom z) = z := fun z => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
      LinearMap.id_apply]
  change coneSndMap R δ hδ n j (m + 1)
    (((coneStep (iteratedConeData R δ hδ (n + 1) j).2.1).d (m + 1) (m + 1 + 1)).hom x) = _
  rw [h]
  change ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
      (show shiftOneEmbedding.f (m + 1) = m + 1 + 1 from rfl)).hom.hom
      ((coneStepPsi (iteratedConeData R δ hδ (n + 1) j).2.1 (m + 1)).hom x.1 +
        (((shiftOne (iteratedConeData R δ hδ (n + 1) j).1).d (m + 1) (m + 1 + 1)).hom x.2)) = _
  rw [map_add, hd, coneStepPsi]
  simp only [ModuleCat.hom_zsmul, ModuleCat.hom_comp, LinearMap.smul_apply, LinearMap.comp_apply,
    map_zsmul, hinv]
  rfl

theorem coneSndMap_d_zero (n j : ℕ) (x : (iteratedCone R δ hδ (n + 1) j).X 0) :
    coneSndMap R δ hδ n j 0 (((iteratedCone R δ hδ (n + 1) j).d 0 1).hom x) =
      coneInlMap R δ hδ n (j + 1) 0 (((δ j).f 0).hom (coneFstMap R δ hδ (n + 1) j 0 x)) := by
  have h := coneStep_d (iteratedConeData R δ hδ (n + 1) j).2.1 0
  have hinv : ∀ z, ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
      (show shiftOneEmbedding.f 0 = 0 + 1 from rfl)).hom.hom
      (((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
        (show shiftOneEmbedding.f 0 = 0 + 1 from rfl)).inv.hom z) = z := fun z => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.inv_hom_id, ModuleCat.hom_id,
      LinearMap.id_apply]
  have hX : IsZero ((shiftOne (iteratedConeData R δ hδ (n + 1) j).1).X 0) :=
    (iteratedConeData R δ hδ (n + 1) j).1.isZero_extend_X shiftOneEmbedding 0 (fun i => by
      change i + 1 ≠ 0
      omega)
  have hs : Subsingleton ((shiftOne (iteratedConeData R δ hδ (n + 1) j).1).X 0) :=
    ModuleCat.isZero_iff_subsingleton.mp hX
  change coneSndMap R δ hδ n j 0
    (((coneStep (iteratedConeData R δ hδ (n + 1) j).2.1).d 0 (0 + 1)).hom x) = _
  rw [h]
  change ((iteratedConeData R δ hδ (n + 1) j).1.extendXIso shiftOneEmbedding
      (show shiftOneEmbedding.f 0 = 0 + 1 from rfl)).hom.hom
      ((coneStepPsi (iteratedConeData R δ hδ (n + 1) j).2.1 0).hom x.1 +
        (((shiftOne (iteratedConeData R δ hδ (n + 1) j).1).d 0 (0 + 1)).hom x.2)) = _
  rw [Subsingleton.elim x.2 0, map_zero, add_zero, coneStepPsi]
  simp only [pow_zero, one_smul, ModuleCat.hom_comp, LinearMap.comp_apply, hinv]
  rfl

/-- **The row-`0` component of the differential** is the differential of the row. -/
theorem coneRowComp_zero_d (n j q : ℕ) (x : (iteratedCone R δ hδ n j).X q) :
    coneRowComp R δ hδ n j 0 j (q + 1) (q + 1) rfl rfl
        (((iteratedCone R δ hδ n j).d q (q + 1)).hom x) =
      ((R j).d q (q + 1)).hom (coneRowComp R δ hδ n j 0 j q q rfl rfl x) := by
  simp only [coneRowComp, LinearMap.comp_apply]
  rw [coneFstMap_d]
  rfl

/-- **The row-`(b + 1)` component of the differential** in degree `q + 1`:
`(D x)_{b+1} = d(x_{b+1}) + (-1)^{q+1} δ(x_b)`. -/
theorem coneRowComp_succ_d (b : ℕ) : ∀ (n j i q m : ℕ) (hi : j + b = i) (hm : q + 1 + b = m),
    b + 1 ≤ n → ∀ x : (iteratedCone R δ hδ n j).X m,
    coneRowComp R δ hδ n j (b + 1) (i + 1) (q + 1) (m + 1) (by omega) (by omega)
        (((iteratedCone R δ hδ n j).d m (m + 1)).hom x) =
      ((R (i + 1)).d q (q + 1)).hom
          (coneRowComp R δ hδ n j (b + 1) (i + 1) q m (by omega) (by omega) x) +
        ((-1 : ℤ) ^ (q + 1)) • ((δ i).f (q + 1)).hom
          (coneRowComp R δ hδ n j b i (q + 1) m hi hm x) := by
  induction b with
  | zero =>
    intro n j i q m hi hm hb x
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain rfl : i = j := by omega
    obtain rfl : m = q + 1 := by omega
    simp only [coneRowComp, LinearMap.comp_apply]
    rw [coneSndMap_d, map_add, map_zsmul, coneFstMap_coneInlMap, coneFstMap_d, map_add,
      map_zsmul]
    exact add_comm _ _
  | succ b ih =>
    intro n j i q m hi hm hb x
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h := ih n (j + 1) i q m (by omega) (by omega) (by omega) (coneSndMap R δ hδ n j m x)
    simp only [coneRowComp, LinearMap.comp_apply]
    rw [coneSndMap_d, map_add, map_zsmul, coneRowComp_succ_coneInlMap, smul_zero, zero_add]
    exact h

/-- The row-`(b + 1)` component of the differential in degree `0` is `δ(x_b)`. -/
theorem coneRowComp_succ_d_zero (b : ℕ) : ∀ (n j i : ℕ) (hi : j + b = i), b + 1 ≤ n →
    ∀ x : (iteratedCone R δ hδ n j).X b,
    coneRowComp R δ hδ n j (b + 1) (i + 1) 0 (b + 1) (by omega) (by omega)
        (((iteratedCone R δ hδ n j).d b (b + 1)).hom x) =
      ((δ i).f 0).hom (coneRowComp R δ hδ n j b i 0 b hi (by omega) x) := by
  induction b with
  | zero =>
    intro n j i hi hb x
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain rfl : i = j := by omega
    simp only [coneRowComp, LinearMap.comp_apply]
    rw [coneSndMap_d_zero, coneFstMap_coneInlMap]
    rfl
  | succ b ih =>
    intro n j i hi hb x
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have h := ih n (j + 1) i (by omega) (by omega) (coneSndMap R δ hδ n j b x)
    simp only [coneRowComp, LinearMap.comp_apply]
    rw [coneSndMap_d, map_add, map_zsmul, coneRowComp_succ_coneInlMap, smul_zero, zero_add]
    exact h

end Rows

end MixedFujita
