/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieStaircase
public import MixedFujita.DeligneIllusieHomologyInjective

/-!
Assembling chain maps of iterated cones from components (step 10).

An element of the iterated cone `T(n, j)` is determined by its row components, and every family of
row components occurs (`coneRowMk`, `coneRowComp_coneRowMk`). Given components
`Ψ_{b → i} : R'_b^q → R_i^{q'}` (`q + b = q' + i`), the map `⊕_b R'_b[-b] → Tot(R, δ)` whose row-`i`
component is `Σ_b Ψ_{b → i}(x_b)` (`coneAssemble`, additive) does not raise the row when no
component does (`coneAssemble_rowsLE`), acts on the top row by the diagonal component
(`coneAssemble_diag`), and is a chain map when the diagonal components have closed values and
`d Ψ_{b → 0} = Ψ_{b → 0} d'`, `d Ψ_{b → i+1} + (-1)^{q'+1} δ Ψ_{b → i} = Ψ_{b → i+1} d'`
(`coneAssemble_d`; sums over `Finset.antidiagonal`, whose shift by one degree is
`coneAssembleRow_d`). Hence the Deligne–Illusie comparison data of check 440 follow from components
on the Čech cochains with these relations whose diagonal satisfies the Cartier condition
(`deligneIllusieStaircaseData_of_components`): what remains of the global Deligne–Illusie argument
is the construction of the components (alternating cup products of `(Φ_i, h_{ij})`) and the
verification of these relations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u v

variable {k : Type u} [Field k]

section RowMk

variable (R : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0)

/-- **The element of `T(n, j)^m` with prescribed row components** `v b i q` (row `i = j + b` in
degree `q = m - b`). -/
noncomputable def coneRowMk : (n j m : ℕ) → (∀ b i q, j + b = i → q + b = m → (R i).X q) →
    (iteratedCone R δ hδ n j).X m
  | n, j, 0, v => coneInlMap R δ hδ n j 0 (v 0 j 0 (Nat.add_zero j) rfl)
  | 0, j, m + 1, v => coneInlMap R δ hδ 0 j (m + 1) (v 0 j (m + 1) (Nat.add_zero j) rfl)
  | n + 1, j, m + 1, v => coneInlMap R δ hδ (n + 1) j (m + 1) (v 0 j (m + 1) (Nat.add_zero j) rfl) +
      coneInrMap R δ hδ n j m
        (coneRowMk n (j + 1) m (fun b i q hi hq => v (b + 1) i q (by omega) (by omega)))

theorem coneRowComp_coneRowMk (b : ℕ) : ∀ (n j i q m : ℕ) (hi : j + b = i) (hq : q + b = m)
    (v : ∀ b i q, j + b = i → q + b = m → (R i).X q), b ≤ n →
    coneRowComp R δ hδ n j b i q m hi hq (coneRowMk R δ hδ n j m v) = v b i q hi hq := by
  induction b with
  | zero =>
    intro n j i q m hi hq v _
    obtain rfl : j = i := by omega
    obtain rfl : q = m := by omega
    cases q with
    | zero =>
      simp only [coneRowComp, coneRowMk, LinearMap.comp_apply, coneFstMap_coneInlMap,
        rowCast_apply_self]
    | succ q =>
      cases n with
      | zero =>
        simp only [coneRowComp, coneRowMk, LinearMap.comp_apply, coneFstMap_coneInlMap,
          rowCast_apply_self]
      | succ n =>
        simp only [coneRowComp, coneRowMk, LinearMap.comp_apply, map_add, coneFstMap_coneInlMap,
          coneFstMap_coneInrMap, add_zero, rowCast_apply_self]
  | succ b ih =>
    intro n j i q m hi hq v hb
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [coneRowComp, coneRowMk, LinearMap.comp_apply, map_add, coneSndMap_coneInlMap,
      coneSndMap_coneInrMap, map_zero, zero_add]
    exact ih n (j + 1) i q m (by omega) (by omega) _ (by omega)

end RowMk

section Assembly

variable (R R' : ℕ → CochainComplex (ModuleCat.{v} k) ℕ) (δ : ∀ j, R j ⟶ R (j + 1))
  (hδ : ∀ j, δ j ≫ δ (j + 1) = 0) (n : ℕ)
  (Ψ : ∀ b i q q', q + b = q' + i → (R' b).X q →+ (R i).X q')

/-- The row-`i` component in degree `q'` of the assembled map:
`Σ_{a + b = m} Ψ_{b → i}(x_b)` with `x_b` the row-`b` component of `x` in degree `a`. -/
noncomputable def coneAssembleRow (m : ℕ)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m) (i q' : ℕ)
    (hq : q' + i = m) : (R i).X q' :=
  ∑ p ∈ Finset.antidiagonal m, if h : p.1 + p.2 = m then
    Ψ p.2 i p.1 q' (by omega) (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 p.2 p.2 p.1 m
      (Nat.zero_add _) h x) else 0

theorem coneAssembleRow_add (m : ℕ)
    (x y : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m) (i q' : ℕ)
    (hq : q' + i = m) :
    coneAssembleRow R R' n Ψ m (x + y) i q' hq =
      coneAssembleRow R R' n Ψ m x i q' hq + coneAssembleRow R R' n Ψ m y i q' hq := by
  simp only [coneAssembleRow, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h := Finset.mem_antidiagonal.mp hp
  rw [dite_eq_left h, dite_eq_left h, dite_eq_left h, map_add, map_add]

theorem coneAssembleRow_zero (m : ℕ) (i q' : ℕ) (hq : q' + i = m) :
    coneAssembleRow R R' n Ψ m 0 i q' hq = 0 := by
  simp only [coneAssembleRow]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.mem_antidiagonal.mp hp
  rw [dite_eq_left h, map_zero, map_zero]

/-- **The assembled map** `⊕_b R'_b[-b] → Tot(R, δ)` with components `Ψ_{b → i}`. -/
noncomputable def coneAssemble (m : ℕ) :
    (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m →+
      (iteratedCone R δ hδ n 0).X m where
  toFun x := coneRowMk R δ hδ n 0 m fun _ i q' hi hq =>
    coneAssembleRow R R' n Ψ m x i q' (by omega)
  map_zero' := by
    refine coneRow_ext R δ hδ n 0 m _ _ fun b i q hi hq hb => ?_
    rw [coneRowComp_coneRowMk R δ hδ b n 0 i q m hi hq _ hb, coneAssembleRow_zero, map_zero]
  map_add' x y := by
    refine coneRow_ext R δ hδ n 0 m _ _ fun b i q hi hq hb => ?_
    rw [map_add, coneRowComp_coneRowMk R δ hδ b n 0 i q m hi hq _ hb,
      coneRowComp_coneRowMk R δ hδ b n 0 i q m hi hq _ hb,
      coneRowComp_coneRowMk R δ hδ b n 0 i q m hi hq _ hb, coneAssembleRow_add]

theorem coneRowComp_coneAssemble (m b i q : ℕ) (hi : 0 + b = i) (hq : q + b = m) (hb : b ≤ n)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m) :
    coneRowComp R δ hδ n 0 b i q m hi hq (coneAssemble R R' δ hδ n Ψ m x) =
      coneAssembleRow R R' n Ψ m x i q (by omega) :=
  coneRowComp_coneRowMk R δ hδ b n 0 i q m hi hq _ hb


/-- **The assembled map does not raise the row**, when no component raises the row. -/
theorem coneAssemble_rowsLE (hΨlt : ∀ b i q q' h, b < i → Ψ b i q q' h = 0) (m c : ℕ)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m)
    (hx : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x) :
    ConeRowsLE R δ hδ n c m (coneAssemble R R' δ hδ n Ψ m x) := by
  intro b q h hcb
  by_cases hbn : b ≤ n
  · rw [coneRowComp_coneAssemble R R' δ hδ n Ψ m b b q (Nat.zero_add b) h hbn]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpm := Finset.mem_antidiagonal.mp hp
    rw [dite_eq_left hpm]
    by_cases hpc : p.2 ≤ c
    · rw [hΨlt p.2 b p.1 q _ (by omega), AddMonoidHom.zero_apply]
    · rw [hx p.2 p.1 hpm (by omega), map_zero]
  · exact LinearMap.congr_fun (coneRowComp_of_lt R δ hδ b n 0 b q m _ h (by omega)) _

/-- **The top-row component of the assembled map is the diagonal component** `Ψ_{c → c}`. -/
theorem coneAssemble_diag (hΨlt : ∀ b i q q' h, b < i → Ψ b i q q' h = 0) (m c q : ℕ)
    (h : q + c = m) (hc : c ≤ n)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m)
    (hx : ConeRowsLE R' (fun _ => 0) (fun _ => comp_zero) n c m x) :
    coneRowComp R δ hδ n 0 c c q m (Nat.zero_add c) h (coneAssemble R R' δ hδ n Ψ m x) =
      Ψ c c q q rfl (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 c c q m
        (Nat.zero_add c) h x) := by
  rw [coneRowComp_coneAssemble R R' δ hδ n Ψ m c c q (Nat.zero_add c) h hc, coneAssembleRow,
    Finset.sum_eq_single (q, c)]
  · rw [dite_eq_left h]
  · intro p hp hne
    have hpm := Finset.mem_antidiagonal.mp hp
    rw [dite_eq_left hpm]
    rcases Nat.lt_trichotomy p.2 c with hpc | hpc | hpc
    · rw [hΨlt p.2 c p.1 q _ hpc, AddMonoidHom.zero_apply]
    · exact absurd (Prod.ext (by omega) hpc) hne
    · rw [hx p.2 p.1 hpm hpc, map_zero]
  · intro hq
    exact absurd (Finset.mem_antidiagonal.mpr h) hq


/-- The rows of the assembled map on a coboundary of the source: the sum shifts by one degree. -/
theorem coneAssembleRow_d (m i q : ℕ) (hq : q + i = m + 1)
    (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m) :
    coneAssembleRow R R' n Ψ (m + 1)
        (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom x) i q hq =
      ∑ p ∈ Finset.antidiagonal m, if h : p.1 + p.2 = m then
        Ψ p.2 i (p.1 + 1) q (by omega) (((R' p.2).d p.1 (p.1 + 1)).hom
          (coneRowComp R' (fun _ => 0) (fun _ => comp_zero) n 0 p.2 p.2 p.1 m (Nat.zero_add _) h x))
        else 0 := by
  rw [coneAssembleRow, Finset.Nat.sum_antidiagonal_succ]
  dsimp only
  rw [dite_eq_left (by omega : 0 + (m + 1) = m + 1), coneRowComp_d_zero_of_zero R' n m x, map_zero,
    zero_add]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm := Finset.mem_antidiagonal.mp hp
  rw [dite_eq_left (by omega : p.1 + 1 + p.2 = m + 1), dite_eq_left hpm,
    coneRowComp_d_of_zero R' n p.2 p.1 m hpm x]


/-- **The assembled map is a chain map**, when the components do not raise the row, the diagonal
components have closed values, and the components satisfy the relations
`d Ψ_{b → 0} = Ψ_{b → 0} d'` and `d Ψ_{b → i+1} + (-1)^{q'+1} δ Ψ_{b → i} = Ψ_{b → i+1} d'`. -/
theorem coneAssemble_d (hΨlt : ∀ b i q q' h, b < i → Ψ b i q q' h = 0)
    (hΨclosed : ∀ b q q' h y, ((δ b).f q').hom (Ψ b b q q' h y) = 0)
    (hΨ0 : ∀ b q q' h h' y, ((R 0).d q' (q' + 1)).hom (Ψ b 0 q q' h y) =
      Ψ b 0 (q + 1) (q' + 1) h' (((R' b).d q (q + 1)).hom y))
    (hΨsucc : ∀ b i q q' h h' h'' y,
      ((R (i + 1)).d q' (q' + 1)).hom (Ψ b (i + 1) q q' h y) +
          ((-1 : ℤ) ^ (q' + 1)) • ((δ i).f (q' + 1)).hom (Ψ b i q (q' + 1) h' y) =
        Ψ b (i + 1) (q + 1) (q' + 1) h'' (((R' b).d q (q + 1)).hom y))
    (m : ℕ) (x : (iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).X m) :
    coneAssemble R R' δ hδ n Ψ (m + 1)
        (((iteratedCone R' (fun _ => 0) (fun _ => comp_zero) n 0).d m (m + 1)).hom x) =
      ((iteratedCone R δ hδ n 0).d m (m + 1)).hom (coneAssemble R R' δ hδ n Ψ m x) := by
  refine coneRow_ext R δ hδ n 0 (m + 1) _ _ fun c i q hi hq hc => ?_
  obtain rfl : c = i := by omega
  rw [coneRowComp_coneAssemble R R' δ hδ n Ψ (m + 1) c c q hi hq hc, coneAssembleRow_d]
  cases c with
  | zero =>
    obtain rfl : q = m + 1 := by omega
    rw [coneRowComp_zero_d R δ hδ n 0 m,
      coneRowComp_coneAssemble R R' δ hδ n Ψ m 0 0 m rfl rfl hc, coneAssembleRow, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpm := Finset.mem_antidiagonal.mp hp
    rw [dite_eq_left hpm, dite_eq_left hpm, hΨ0]
  | succ c =>
    cases q with
    | zero =>
      obtain rfl : m = c := by omega
      rw [coneRowComp_succ_d_zero R δ hδ m n 0 m (Nat.zero_add m) hc,
        coneRowComp_coneAssemble R R' δ hδ n Ψ m m m 0 (Nat.zero_add m) (by omega) (by omega),
        coneAssembleRow, map_sum]
      refine (Finset.sum_eq_zero fun p hp => ?_).trans (Finset.sum_eq_zero fun p hp => ?_).symm
      · have hpm := Finset.mem_antidiagonal.mp hp
        rw [dite_eq_left hpm, hΨlt p.2 (m + 1) (p.1 + 1) 0 _ (by omega), AddMonoidHom.zero_apply]
      · have hpm := Finset.mem_antidiagonal.mp hp
        rw [dite_eq_left hpm]
        rcases Nat.lt_or_ge p.2 m with hpc | hpc
        · rw [hΨlt p.2 m p.1 0 _ hpc, AddMonoidHom.zero_apply, map_zero]
        · obtain ⟨p1, p2⟩ := p
          obtain rfl : p2 = m := by simp only at hpm hpc; omega
          obtain rfl : p1 = 0 := by simp only at hpm; omega
          exact hΨclosed p2 0 0 _ _
    | succ q =>
      rw [coneRowComp_succ_d R δ hδ c n 0 c q m (Nat.zero_add c) (by omega) hc,
        coneRowComp_coneAssemble R R' δ hδ n Ψ m (c + 1) (c + 1) q (by omega) (by omega) hc,
        coneRowComp_coneAssemble R R' δ hδ n Ψ m c c (q + 1) (Nat.zero_add c) (by omega)
          (by omega), coneAssembleRow, coneAssembleRow, map_sum, map_sum, Finset.smul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpm := Finset.mem_antidiagonal.mp hp
      rw [dite_eq_left hpm, dite_eq_left hpm, dite_eq_left hpm, hΨsucc]

end Assembly

section Geometric

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra sectionsBaseModule

variable [IsIntegral X]

/-- **The Deligne–Illusie comparison data from components**: components
`Ψ_{b → i} : Č^q(Ω^b(D)) → Č^{q'}(Ω^i(p • D))` (`q + b = q' + i`) which do not raise the row, have
closed diagonal values and satisfy the relations of `coneAssemble_d`, and whose diagonal satisfies
the Cartier condition, give `DeligneIllusieStaircaseData`. -/
theorem deligneIllusieStaircaseData_of_components {n : ℕ} (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (D : CartierDivisor X) {N : ℕ} (𝒰 : Fin N → X.Opens)
    (Ψ : ∀ b i q q', q + b = q' + i → (cechComplexLinear K (twistedFormsSheaf K D b) 𝒰).X q →+
      (cechComplexLinear K (twistedFormsSheaf K (p • D) i) 𝒰).X q')
    (hΨlt : ∀ b i q q' h, b < i → Ψ b i q q' h = 0)
    (hΨclosed : ∀ b q q' h y,
      ((twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰).f q').hom (Ψ b b q q' h y) = 0)
    (hΨ0 : ∀ b q q' h h' y,
      ((cechComplexLinear K (twistedFormsSheaf K (p • D) 0) 𝒰).d q' (q' + 1)).hom
          (Ψ b 0 q q' h y) =
        Ψ b 0 (q + 1) (q' + 1) h'
          (((cechComplexLinear K (twistedFormsSheaf K D b) 𝒰).d q (q + 1)).hom y))
    (hΨsucc : ∀ b i q q' h h' h'' y,
      ((cechComplexLinear K (twistedFormsSheaf K (p • D) (i + 1)) 𝒰).d q' (q' + 1)).hom
          (Ψ b (i + 1) q q' h y) + ((-1 : ℤ) ^ (q' + 1)) •
          ((twistedFormsCechDiffLinearMap p c₀ hcover D i 𝒰).f (q' + 1)).hom (Ψ b i q (q' + 1) h' y) =
        Ψ b (i + 1) (q + 1) (q' + 1) h''
          (((cechComplexLinear K (twistedFormsSheaf K D b) 𝒰).d q (q + 1)).hom y))
    (hsurj0 : ∀ q z, ((twistedFormsCechDiffLinearMap p c₀ hcover D 0 𝒰).f q).hom z = 0 →
      ∃ y, z = Ψ 0 0 q q rfl y)
    (hsurj : ∀ c q z, ((twistedFormsCechDiffLinearMap p c₀ hcover D (c + 1) 𝒰).f q).hom z = 0 →
      ∃ y w, z = Ψ (c + 1) (c + 1) q q rfl y +
        ((twistedFormsCechDiffLinearMap p c₀ hcover D c 𝒰).f q).hom w)
    (hinj0 : ∀ q y, Ψ 0 0 q q rfl y = 0 → y = 0)
    (hinj : ∀ c q y w, Ψ (c + 1) (c + 1) q q rfl y =
      ((twistedFormsCechDiffLinearMap p c₀ hcover D c 𝒰).f q).hom w → y = 0) :
    DeligneIllusieStaircaseData K p c₀ hcover D 𝒰 := by
  refine ⟨coneAssemble (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
      (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰)
      (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
      (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n Ψ,
    fun c q => Ψ c c q q rfl, ?_, ?_, ?_, hsurj0, hsurj, hinj0, hinj⟩
  · exact coneAssemble_d _ _ _ _ n Ψ hΨlt hΨclosed hΨ0 hΨsucc
  · exact fun m c x hx => coneAssemble_rowsLE _ _ _ _ n Ψ hΨlt m c x hx
  · intro m c q h x hx
    by_cases hc : c ≤ n
    · exact coneAssemble_diag _ _ _ _ n Ψ hΨlt m c q h hc x hx
    · rw [LinearMap.congr_fun (coneRowComp_of_lt _ _ _ c n 0 c q m _ h (by omega)) _,
        LinearMap.congr_fun (coneRowComp_of_lt _ _ _ c n 0 c q m _ h (by omega)) x,
        LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

end Geometric

end MixedFujita
