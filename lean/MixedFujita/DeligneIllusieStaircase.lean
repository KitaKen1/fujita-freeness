/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.IteratedConeRows

/-!
The staircase argument of Deligne–Illusie (step 10).

Let `T` be the iterated cone of rows `R_0, …, R_n` with vertical maps `δ` (check 434), for example
the Čech–de Rham total complex with `δ = d`, and `S` the iterated cone of rows `R'_b` with zero
vertical maps, i.e. `⊕_b R'_b[-b]`. Let `φ : S → T` be an additive chain map which does not raise
the row (`ConeRowsLE`) and acts on the top row of an element as additive maps `Φ_c`. Assume the
Cartier condition: `Φ_c` maps `R'_c` onto the elements of `R_c` killed by `δ` modulo the image of
`δ` from the row below, injectively (`hsurj`, `hinj`, and `hsurj0`, `hinj0` for the row `0`).
Then every cocycle of `S` whose image is a coboundary of `T` is a coboundary
(`deligneIllusie_staircase`, by induction on the top row: the top row of the cocycle is a
coboundary by the Cartier condition, and subtracting it and correcting the primitive by the image of
`δ` moves the problem down one row; `deligneIllusie_injective` for the whole complex when the
vertical map out of the top row vanishes, `deligneIllusie_injective_zero` in degree `0`). This is the
τ-filtration argument of Deligne–Illusie, done elementwise on the row components of check 438;
with `Φ_c` the twisted Deligne–Illusie map of check 437 on Čech cochains, it gives the injectivity
needed in check 436.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace MixedFujita

universe u v

variable {k : Type u} [Field k]

section Helpers

variable (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0)

/-- Rows beyond the last one have zero components. -/
theorem coneRowComp_of_lt (b : ℕ) : ∀ (n j i q m : ℕ) (hi : j + b = i) (hq : q + b = m),
    n < b → coneRowComp R δ hδ n j b i q m hi hq = 0 := by
  induction b with
  | zero => intro n j i q m hi hq h; omega
  | succ b ih =>
    intro n j i q m hi hq h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases n with
    | zero => rfl
    | succ n =>
      simp only [coneRowComp]
      rw [ih n (j + 1) i q m _ _ (by omega), LinearMap.zero_comp]

/-- Included rows beyond the last one are zero. -/
theorem coneRowIncl_of_lt (b : ℕ) : ∀ (n j i q m : ℕ) (hi : j + b = i) (hq : q + b = m),
    n < b → coneRowIncl R δ hδ n j b i q m hi hq = 0 := by
  induction b with
  | zero => intro n j i q m hi hq h; omega
  | succ b ih =>
    intro n j i q m hi hq h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    cases n with
    | zero => rfl
    | succ n =>
      simp only [coneRowIncl]
      rw [ih n (j + 1) i q m _ _ (by omega), LinearMap.comp_zero]

end Helpers

section ZeroVertical

variable (R' : ℕ → CochainComplex (ModuleCat.{v} k) ℕ)

/-- With zero vertical maps, the row components of the differential are the row differentials. -/
theorem coneRowComp_d_of_zero (n b q m : ℕ) (hq : q + b = m)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m) :
    coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 b b (q + 1) (m + 1) (Nat.zero_add b)
        (by omega) (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom x) =
      ((R' b).d q (q + 1)).hom
        (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 b b q m (Nat.zero_add b) hq x) := by
  cases b with
  | zero =>
    obtain rfl : q = m := by omega
    exact coneRowComp_zero_d R' (fun _ => 0) (fun _ => comp_zero) n 0 q x
  | succ b =>
    by_cases hb : b + 1 ≤ n
    · have h := coneRowComp_succ_d R' (fun _ => 0) (fun _ => comp_zero) b n 0 b q m
        (Nat.zero_add b) (by omega) hb x
      rw [h]
      simp only [HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, smul_zero,
        add_zero]
    · rw [coneRowComp_of_lt _ _ _ (b + 1) n 0 (b + 1) (q + 1) (m + 1) _ _ (by omega),
        coneRowComp_of_lt _ _ _ (b + 1) n 0 (b + 1) q m _ _ (by omega)]
      simp only [LinearMap.zero_apply, map_zero]

/-- With zero vertical maps, the row components of the differential in degree `0` vanish. -/
theorem coneRowComp_d_zero_of_zero (n b : ℕ)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X b) :
    coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 (b + 1) (b + 1) 0 (b + 1)
        (by omega) (by omega) (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d b (b + 1)).hom x) =
      0 := by
  by_cases hb : b + 1 ≤ n
  · have h := coneRowComp_succ_d_zero R' (fun _ => 0) (fun _ => comp_zero) b n 0 b
      (Nat.zero_add b) hb x
    rw [h]
    rfl
  · rw [coneRowComp_of_lt _ _ _ (b + 1) n 0 (b + 1) 0 (b + 1) _ _ (by omega)]
    rfl

end ZeroVertical

section InclDiff

variable (R' : ℕ → CochainComplex (ModuleCat.{v} k) ℕ)

/-- With zero vertical maps, `D` of an included row is the included row differential (same row). -/
theorem coneRowComp_d_coneRowIncl_self_of_zero (n c q m : ℕ) (hq : q + c = m) (hc : c ≤ n)
    (z : (R' c).X q) :
    coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 c c (q + 1) (m + 1) (Nat.zero_add c)
        (by omega) (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom
          (coneRowIncl R' (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) hq z)) =
      ((R' c).d q (q + 1)).hom z := by
  rw [coneRowComp_d_of_zero R' n c q m hq, coneRowComp_coneRowIncl_self _ _ _ c n 0 c q m _ _ _ _
    hc]

/-- With zero vertical maps, `D` of an included row has no components in the other rows. -/
theorem coneRowComp_d_coneRowIncl_ne_of_zero (n b c q q' m : ℕ) (hq : q + c = m)
    (hq' : q' + b = m + 1) (hbc : b ≠ c) (z : (R' c).X q) :
    coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 b b q' (m + 1) (Nat.zero_add b) hq'
        (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom
          (coneRowIncl R' (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) hq z)) =
      0 := by
  cases q' with
  | zero =>
    obtain rfl : b = m + 1 := by omega
    exact coneRowComp_d_zero_of_zero R' n m _
  | succ q' =>
    rw [coneRowComp_d_of_zero R' n b q' m (by omega),
      coneRowComp_coneRowIncl_of_ne _ _ _ c b n 0 c b q q' m _ _ _ _ (Ne.symm hbc), map_zero]

variable (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0)

/-- The row-`(c + 1)` component of `D` of the included row `c` is `(-1)^q δ`. -/
theorem coneRowComp_d_coneRowIncl_succ (n c q m : ℕ) (hm : q + c = m) (hc : c + 1 ≤ n)
    (w : (R c).X q) :
    coneRowComp R δ hδ n 0 (c + 1) (c + 1) q (m + 1) (Nat.zero_add _) (by omega)
        (((iteratedCone R δ hδ n 0).d m (m + 1)).hom
          (coneRowIncl R δ hδ n 0 c c q m (Nat.zero_add c) hm w)) =
      ((-1 : ℤ) ^ q) • ((δ c).f q).hom w := by
  cases q with
  | zero =>
    obtain rfl : c = m := by omega
    have h := coneRowComp_succ_d_zero R δ hδ c n 0 c (Nat.zero_add c) hc
      (coneRowIncl R δ hδ n 0 c c 0 c (Nat.zero_add c) hm w)
    rw [pow_zero, one_smul, h, coneRowComp_coneRowIncl_self _ _ _ c n 0 c 0 c _ _ _ _ (by omega)]
  | succ q =>
    have h := coneRowComp_succ_d R δ hδ c n 0 c q m (Nat.zero_add c) hm hc
      (coneRowIncl R δ hδ n 0 c c (q + 1) m (Nat.zero_add c) hm w)
    rw [h, coneRowComp_coneRowIncl_of_ne _ _ _ c (c + 1) n 0 c (c + 1) (q + 1) q m _ _
      _ _ (by omega), map_zero, zero_add, coneRowComp_coneRowIncl_self _ _ _ c n 0 c (q + 1)
      m _ _ _ _ (by omega)]

/-- `D` of the included row `c` has no components above the row `c + 1`. -/
theorem coneRowComp_d_coneRowIncl_of_lt (n b c q q' m : ℕ) (hm : q + c = m) (hb : c + 1 < b)
    (hq' : q' + b = m + 1) (w : (R c).X q) :
    coneRowComp R δ hδ n 0 b b q' (m + 1) (Nat.zero_add b) hq'
        (((iteratedCone R δ hδ n 0).d m (m + 1)).hom
          (coneRowIncl R δ hδ n 0 c c q m (Nat.zero_add c) hm w)) = 0 := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  by_cases hbn : b + 1 ≤ n
  · cases q' with
    | zero =>
      obtain rfl : b = m := by omega
      have h := coneRowComp_succ_d_zero R δ hδ b n 0 b (Nat.zero_add _) hbn
        (coneRowIncl R δ hδ n 0 c c q b (Nat.zero_add c) hm w)
      rw [h, coneRowComp_coneRowIncl_of_ne _ _ _ c b n 0 c b q 0 b _ _ _ _ (by omega), map_zero]
    | succ q' =>
      have h := coneRowComp_succ_d R δ hδ b n 0 b q' m (Nat.zero_add b) (by omega) hbn
        (coneRowIncl R δ hδ n 0 c c q m (Nat.zero_add c) hm w)
      rw [h, coneRowComp_coneRowIncl_of_ne _ _ _ c (b + 1) n 0 c (b + 1) q q' m _ _ _ _
        (by omega), coneRowComp_coneRowIncl_of_ne _ _ _ c b n 0 c b q (q' + 1) m _ _ _ _
        (by omega), map_zero, map_zero, smul_zero, add_zero]
  · exact LinearMap.congr_fun (coneRowComp_of_lt R δ hδ (b + 1) n 0 (b + 1) q' (m + 1) _ _
      (by omega)) _

end InclDiff

section Staircase

variable (R R' : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0) (n : ℕ)

/-- `x` has no components in the rows above `c`. -/
def ConeRowsLE (c m : ℕ) (x : (iteratedCone R δ hδ n 0).X m) : Prop :=
  ∀ b q (h : q + b = m), c < b → coneRowComp R δ hδ n 0 b b q m (Nat.zero_add b) h x = 0

/-- **The staircase argument of Deligne–Illusie.** Let `φ` be an additive chain map from the
direct sum `⊕_b R'_b[-b]` (iterated cone with zero vertical maps) to the iterated cone of the rows
`R_b` with vertical maps `δ`, which does not raise the row and acts on the top row of an element
as `Φ_c`. If `Φ_c` identifies `R'_c` with the closed elements of `R_c` modulo the image of `δ`
(the Cartier condition), then every cocycle of the source whose image is a coboundary is a
coboundary; here for elements whose rows are at most `c`, with the row `c` of the primitive
closed. -/
theorem deligneIllusie_staircase
    (φ : ∀ m, (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m →+
      (iteratedCone R δ hδ n 0).X m)
    (hφ : ∀ m x, φ (m + 1) (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m
      (m + 1)).hom x) = ((iteratedCone R δ hδ n 0).d m (m + 1)).hom (φ m x))
    (htri : ∀ m c x, ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x →
      ConeRowsLE R δ hδ n c m (φ m x))
    (Φ : ∀ c q, (R' c).X q →+ (R c).X q)
    (hdiag : ∀ m c q (h : q + c = m) x, ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x →
      coneRowComp R δ hδ n 0 c c q m (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h x))
    (hsurj0 : ∀ q z, ((δ 0).f q).hom z = 0 → ∃ y, z = Φ 0 q y)
    (hsurj : ∀ c q z, ((δ (c + 1)).f q).hom z = 0 →
      ∃ y w, z = Φ (c + 1) q y + ((δ c).f q).hom w)
    (hinj0 : ∀ q y, Φ 0 q y = 0 → y = 0)
    (hinj : ∀ c q y w, Φ (c + 1) q y = ((δ c).f q).hom w → y = 0) (c : ℕ) :
    c ≤ n → ∀ (m : ℕ) (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X (m + 1))
      (y : (iteratedCone R δ hδ n 0).X m),
      ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (m + 1) (m + 1 + 1)).hom x = 0 →
      ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c (m + 1) x →
      ConeRowsLE R δ hδ n c m y →
      (∀ q (h : q + c = m),
        ((δ c).f q).hom (coneRowComp R δ hδ n 0 c c q m (Nat.zero_add c) h y) = 0) →
      φ (m + 1) x = ((iteratedCone R δ hδ n 0).d m (m + 1)).hom y →
      ∃ s, x = ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom s := by
  induction c with
  | zero =>
    intro _ m x y hx hxle hyle hycl hxy
    obtain ⟨z, hz⟩ := hsurj0 m _ (hycl m rfl)
    let v := coneRowIncl R' (fun _ => 0) (fun _ => comp_zero) n 0 0 0 m m (Nat.zero_add 0) rfl z
    have hvle : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n 0 m v := fun b q h hb =>
      coneRowComp_coneRowIncl_of_ne _ _ _ 0 b n 0 0 b m q m _ _ _ _ (by omega) z
    have hDvle : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n 0 (m + 1)
        (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom v) :=
      fun b q h hb => coneRowComp_d_coneRowIncl_ne_of_zero R' n b 0 m q m rfl h (by omega) z
    have hv_self : coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 0 0 m m
        (Nat.zero_add 0) rfl v = z :=
      coneRowComp_coneRowIncl_self _ _ _ 0 n 0 0 m m _ _ _ _ (Nat.zero_le _) z
    have hDv_self : coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 0 0 (m + 1) (m + 1)
        (Nat.zero_add 0) rfl
          (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom v) =
        ((R' 0).d m (m + 1)).hom z :=
      coneRowComp_d_coneRowIncl_self_of_zero R' n 0 m m rfl (Nat.zero_le _) z
    have h1 := congrArg (coneRowComp R δ hδ n 0 0 0 (m + 1) (m + 1) (Nat.zero_add 0) rfl) hxy
    rw [hdiag (m + 1) 0 (m + 1) rfl x hxle, coneRowComp_zero_d R δ hδ n 0 m] at h1
    have h2 := congrArg (coneRowComp R δ hδ n 0 0 0 (m + 1) (m + 1) (Nat.zero_add 0) rfl)
      (hφ m v)
    rw [hdiag (m + 1) 0 (m + 1) rfl _ hDvle, hDv_self, coneRowComp_zero_d R δ hδ n 0 m,
      hdiag m 0 m rfl v hvle, hv_self] at h2
    have h3 : Φ 0 (m + 1) (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 0 0 (m + 1) (m + 1)
        (Nat.zero_add 0) rfl x - ((R' 0).d m (m + 1)).hom z) = 0 := by
      rw [map_sub, h1, h2, ← hz, sub_self]
    have h4 := sub_eq_zero.mp (hinj0 _ _ h3)
    refine ⟨v, coneRow_ext _ _ _ n 0 (m + 1) _ _ fun b i q hi hq hb => ?_⟩
    obtain rfl : b = i := by omega
    cases b with
    | zero =>
      obtain rfl : q = m + 1 := by omega
      rw [h4, hDv_self]
    | succ b =>
      rw [hxle (b + 1) q hq (by omega), hDvle (b + 1) q hq (by omega)]
  | succ c ih =>
    intro hcn m x y hx hxle hyle hycl hxy
    rcases Nat.lt_or_ge m c with hmc | hmc
    · -- no row `c + 1` in these degrees
      refine ih (by omega) m x y hx (fun b q h hb => hxle b q h (by omega)) (fun b q h hb => ?_)
        (fun q h => by omega) hxy
      omega
    rcases Nat.eq_or_lt_of_le hmc with hmc | hmc
    · -- `m = c`: the row `c + 1` of `x` is in degree `0`
      obtain rfl : c = m := hmc
      have h1 := congrArg (coneRowComp R δ hδ n 0 (c + 1) (c + 1) 0 (c + 1) (Nat.zero_add _)
        (Nat.zero_add _)) hxy
      rw [hdiag (c + 1) (c + 1) 0 (Nat.zero_add _) x hxle,
        coneRowComp_succ_d_zero R δ hδ c n 0 c (Nat.zero_add c) hcn y] at h1
      have h2 := hinj c 0 _ _ h1
      refine ih (by omega) c x y hx (fun b q h hb => ?_) (fun b q h hb => by omega)
        (fun q h => ?_) hxy
      · rcases Nat.eq_or_lt_of_le hb with hb | hb
        · obtain rfl : b = c + 1 := hb.symm
          obtain rfl : q = 0 := by omega
          exact h2
        · exact hxle b q h hb
      · obtain rfl : q = 0 := by omega
        rw [← h1, h2, map_zero]
    · -- `m ≥ c + 1`
      obtain ⟨q, rfl⟩ : ∃ q, m = q + c + 1 := ⟨m - c - 1, by omega⟩
      obtain ⟨z, w, hzw⟩ := hsurj c q _ (hycl q (by omega))
      let v := coneRowIncl R' (fun _ => 0) (fun _ => comp_zero) n 0 (c + 1) (c + 1) q (q + c + 1)
        (Nat.zero_add _) (by omega) z
      have hvle : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n (c + 1) (q + c + 1) v :=
        fun b q' h hb => coneRowComp_coneRowIncl_of_ne _ _ _ (c + 1) b n 0 (c + 1) b q q'
          (q + c + 1) _ _ _ _ (by omega) z
      have hDvle : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n (c + 1) (q + c + 1 + 1)
          (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (q + c + 1)
            (q + c + 1 + 1)).hom v) :=
        fun b q' h hb => coneRowComp_d_coneRowIncl_ne_of_zero R' n b (c + 1) q q' (q + c + 1)
          (by omega) h (by omega) z
      have hv_self : coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 (c + 1) (c + 1) q
          (q + c + 1) (Nat.zero_add _) (by omega) v = z :=
        coneRowComp_coneRowIncl_self _ _ _ (c + 1) n 0 (c + 1) q (q + c + 1) _ _ _ _ hcn z
      have hDv_self : coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 (c + 1) (c + 1)
          (q + 1) (q + c + 1 + 1) (Nat.zero_add _) (by omega)
            (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (q + c + 1)
              (q + c + 1 + 1)).hom v) = ((R' (c + 1)).d q (q + 1)).hom z :=
        coneRowComp_d_coneRowIncl_self_of_zero R' n (c + 1) q (q + c + 1) (by omega) hcn z
      -- the row `c + 1` of `φ x = D y`
      have h1 := congrArg (coneRowComp R δ hδ n 0 (c + 1) (c + 1) (q + 1) (q + c + 1 + 1)
        (Nat.zero_add _) (by omega)) hxy
      rw [hdiag (q + c + 1 + 1) (c + 1) (q + 1) (by omega) x hxle,
        coneRowComp_succ_d R δ hδ c n 0 c q (q + c + 1) (Nat.zero_add c) (by omega) hcn y] at h1
      -- the row `c + 1` of the chain map at `v`
      have h2 := congrArg (coneRowComp R δ hδ n 0 (c + 1) (c + 1) (q + 1) (q + c + 1 + 1)
        (Nat.zero_add _) (by omega)) (hφ (q + c + 1) v)
      rw [hdiag (q + c + 1 + 1) (c + 1) (q + 1) (by omega) _ hDvle, hDv_self,
        coneRowComp_succ_d R δ hδ c n 0 c q (q + c + 1) (Nat.zero_add c) (by omega) hcn,
        hdiag (q + c + 1) (c + 1) q (by omega) v hvle, hv_self] at h2
      have hcomm : ((R (c + 1)).d q (q + 1)).hom (((δ c).f q).hom w) =
          ((δ c).f (q + 1)).hom (((R c).d q (q + 1)).hom w) := by
        rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← LinearMap.comp_apply,
          ← ModuleCat.hom_comp, (δ c).comm]
      set xt := coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 (c + 1) (c + 1) (q + 1)
        (q + c + 1 + 1) (Nat.zero_add _) (by omega) x with hxt
      set yt := coneRowComp R δ hδ n 0 (c + 1) (c + 1) q (q + c + 1) (Nat.zero_add _) (by omega)
        y with hyt
      set yc := coneRowComp R δ hδ n 0 c c (q + 1) (q + c + 1) (Nat.zero_add c) (by omega) y
        with hyc
      set u := coneRowComp R δ hδ n 0 c c (q + 1) (q + c + 1) (Nat.zero_add c) (by omega)
        (φ (q + c + 1) v) with hu
      have h3 : Φ (c + 1) (q + 1) (xt - ((R' (c + 1)).d q (q + 1)).hom z) =
          ((δ c).f (q + 1)).hom (((R c).d q (q + 1)).hom w +
            ((-1 : ℤ) ^ (q + 1)) • (yc - u)) := by
        rw [map_sub, h1, h2, hzw, map_add, map_add, hcomm, map_zsmul, map_sub, smul_sub]
        abel
      have h4 := sub_eq_zero.mp (hinj c (q + 1) _ _ h3)
      -- the correction of the primitive
      let t := coneRowIncl R δ hδ n 0 c c q (q + c) (Nat.zero_add c) rfl (((-1 : ℤ) ^ q) • w)
      have ht : coneRowComp R δ hδ n 0 (c + 1) (c + 1) q (q + c + 1) (Nat.zero_add _) (by omega)
          (((iteratedCone R δ hδ n 0).d (q + c) (q + c + 1)).hom t) = ((δ c).f q).hom w := by
        have h := coneRowComp_d_coneRowIncl_succ R δ hδ n c q (q + c) rfl hcn
          (((-1 : ℤ) ^ q) • w)
        rw [map_zsmul ((δ c).f q).hom, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow,
          one_smul] at h
        exact h
      have htlt : ∀ b q' (h : q' + b = q + c + 1), c + 1 < b →
          coneRowComp R δ hδ n 0 b b q' (q + c + 1) (Nat.zero_add b) h
            (((iteratedCone R δ hδ n 0).d (q + c) (q + c + 1)).hom t) = 0 :=
        fun b q' h hb => coneRowComp_d_coneRowIncl_of_lt R δ hδ n b c q q' (q + c) rfl hb h _
      let x' := x - ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (q + c + 1)
        (q + c + 1 + 1)).hom v
      let y' := y - φ (q + c + 1) v - ((iteratedCone R δ hδ n 0).d (q + c) (q + c + 1)).hom t
      have hx' : ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (q + c + 1 + 1)
          (q + c + 1 + 1 + 1)).hom x' = 0 := by
        have hdd := congrArg (fun f => f.hom v)
          ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d_comp_d (q + c + 1)
            (q + c + 1 + 1) (q + c + 1 + 1 + 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] at hdd
        change ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (q + c + 1 + 1)
          (q + c + 1 + 1 + 1)).hom (x - _) = 0
        rw [map_sub, hx, hdd, sub_zero]
      have hφx' : φ (q + c + 1 + 1) x' = ((iteratedCone R δ hδ n 0).d (q + c + 1)
          (q + c + 1 + 1)).hom y' := by
        have hdd := congrArg (fun f => f.hom t)
          ((iteratedCone R δ hδ n 0).d_comp_d (q + c) (q + c + 1) (q + c + 1 + 1))
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
          LinearMap.zero_apply] at hdd
        change φ _ (x - _) = ((iteratedCone R δ hδ n 0).d (q + c + 1) (q + c + 1 + 1)).hom
          (y - φ (q + c + 1) v - ((iteratedCone R δ hδ n 0).d (q + c) (q + c + 1)).hom t)
        rw [map_sub, hxy, hφ, map_sub, map_sub, hdd, sub_zero]
      have hx'le : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c (q + c + 1 + 1) x' := by
        intro b q' h hb
        change coneRowComp _ _ _ n 0 b b q' _ _ h (x - _) = 0
        rw [map_sub]
        rcases Nat.eq_or_lt_of_le hb with hb | hb
        · obtain rfl : b = c + 1 := hb.symm
          obtain rfl : q' = q + 1 := by omega
          rw [← hxt, h4, hDv_self, sub_self]
        · rw [hxle b q' h hb, hDvle b q' h hb, sub_self]
      have hy'top : ∀ b q' (h : q' + b = q + c + 1), c < b →
          coneRowComp R δ hδ n 0 b b q' (q + c + 1) (Nat.zero_add b) h y' = 0 := by
        intro b q' h hb
        change coneRowComp _ _ _ n 0 b b q' _ _ h (y - _ - _) = 0
        rw [map_sub, map_sub]
        rcases Nat.eq_or_lt_of_le hb with hb | hb
        · obtain rfl : b = c + 1 := hb.symm
          obtain rfl : q = q' := by omega
          rw [← hyt, hdiag (q + c + 1) (c + 1) q h v hvle, hv_self, ht, hzw,
            add_sub_cancel_left, sub_self]
        · rw [hyle b q' h hb, htri (q + c + 1) (c + 1) v hvle b q' h hb, htlt b q' h hb,
            sub_zero, sub_zero]
      have hy'cl : ∀ q' (h : q' + c = q + c + 1),
          ((δ c).f q').hom (coneRowComp R δ hδ n 0 c c q' (q + c + 1) (Nat.zero_add c) h y') =
            0 := by
        intro q' h
        obtain rfl : q' = q + 1 := by omega
        have h5 := congrArg (coneRowComp R δ hδ n 0 (c + 1) (c + 1) (q + 1) (q + c + 1 + 1)
          (Nat.zero_add _) (by omega)) hφx'
        rw [htri (q + c + 1 + 1) c x' hx'le (c + 1) (q + 1) (by omega) (by omega),
          coneRowComp_succ_d R δ hδ c n 0 c q (q + c + 1) (Nat.zero_add c) (by omega) hcn,
          hy'top (c + 1) q (by omega) (by omega), map_zero, zero_add] at h5
        have h6 := congrArg (fun e => ((-1 : ℤ) ^ (q + 1)) • e) h5
        simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul,
          smul_zero] at h6
        exact h6.symm
      obtain ⟨s', hs'⟩ := ih (by omega) (q + c + 1) x' y' hx' hx'le hy'top hy'cl hφx'
      refine ⟨s' + v, ?_⟩
      rw [map_add, ← hs']
      exact (sub_add_cancel x _).symm


/-- **Injectivity of the Deligne–Illusie map on cohomology** (elementwise): if the vertical map out
of the top row vanishes, every cocycle of `⊕_b R'_b[-b]` in positive degree whose image is a
coboundary is a coboundary. -/
theorem deligneIllusie_injective
    (φ : ∀ m, (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m →+
      (iteratedCone R δ hδ n 0).X m)
    (hφ : ∀ m x, φ (m + 1) (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m
      (m + 1)).hom x) = ((iteratedCone R δ hδ n 0).d m (m + 1)).hom (φ m x))
    (htri : ∀ m c x, ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x →
      ConeRowsLE R δ hδ n c m (φ m x))
    (Φ : ∀ c q, (R' c).X q →+ (R c).X q)
    (hdiag : ∀ m c q (h : q + c = m) x, ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x →
      coneRowComp R δ hδ n 0 c c q m (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h x))
    (hsurj0 : ∀ q z, ((δ 0).f q).hom z = 0 → ∃ y, z = Φ 0 q y)
    (hsurj : ∀ c q z, ((δ (c + 1)).f q).hom z = 0 →
      ∃ y w, z = Φ (c + 1) q y + ((δ c).f q).hom w)
    (hinj0 : ∀ q y, Φ 0 q y = 0 → y = 0)
    (hinj : ∀ c q y w, Φ (c + 1) q y = ((δ c).f q).hom w → y = 0)
    (hδn : ∀ q z, ((δ n).f q).hom z = 0) (m : ℕ)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X (m + 1))
    (y : (iteratedCone R δ hδ n 0).X m)
    (hx : ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d (m + 1) (m + 1 + 1)).hom x = 0)
    (hxy : φ (m + 1) x = ((iteratedCone R δ hδ n 0).d m (m + 1)).hom y) :
    ∃ s, x = ((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom s :=
  deligneIllusie_staircase R R' δ hδ n φ hφ htri Φ hdiag hsurj0 hsurj hinj0 hinj n le_rfl m x y hx
    (fun b q h hb => LinearMap.congr_fun (coneRowComp_of_lt R' (fun _ => 0) (fun _ => comp_zero) b
      n 0 b q (m + 1) _ h hb) x)
    (fun b q h hb => LinearMap.congr_fun (coneRowComp_of_lt R δ hδ b n 0 b q m _ h hb) y)
    (fun q _ => hδn q _) hxy

/-- **Injectivity of the Deligne–Illusie map in degree `0`.** -/
theorem deligneIllusie_injective_zero
    (φ : ∀ m, (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m →+
      (iteratedCone R δ hδ n 0).X m)
    (Φ : ∀ c q, (R' c).X q →+ (R c).X q)
    (hdiag : ∀ m c q (h : q + c = m) x, ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x →
      coneRowComp R δ hδ n 0 c c q m (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h x))
    (hinj0 : ∀ q y, Φ 0 q y = 0 → y = 0)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X 0) (hx : φ 0 x = 0) :
    x = 0 := by
  have hle : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n 0 0 x := fun b q h hb => by omega
  have h1 := hdiag 0 0 0 rfl x hle
  rw [hx, map_zero] at h1
  have h2 := hinj0 _ _ h1.symm
  refine coneRow_ext _ _ _ n 0 0 x 0 fun b i q hi hq hb => ?_
  obtain rfl : b = 0 := by omega
  obtain rfl : i = 0 := by omega
  obtain rfl : q = 0 := by omega
  rw [map_zero]
  exact h2

end Staircase

end MixedFujita
