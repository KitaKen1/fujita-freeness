/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieSourceReduction
public import MixedFujita.DeligneIllusieStaircase
public import MixedFujita.DifferentialFormsVanishingDegree
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
From the staircase argument to the Deligne–Illusie inequality (step 10).

Over a finite field, an additive map on the middle terms of two short complexes of vector spaces
which sends cycles to cycles and detects boundaries (a cycle whose image is a boundary is a
boundary) bounds the dimension of homology: choosing representatives gives an injective function
between the concrete homologies `ker g ⧸ im f`, and we compare cardinalities
(`finrank_homology_le_of_additive`; no well-definedness on classes is needed). For `ℕ`-indexed
cochain complexes this applies in positive degrees (`finrank_homology_succ_le_of_additive`).

With the staircase argument of check 439, the Deligne–Illusie inequality in degrees `m > n`
follows from an additive chain map `⊕_b Č(Ω^b(D))[-b] → Čech–de Rham(Ω^•(p • D))` which does not
raise the de Rham degree and whose leading components `Φ_c` satisfy the Cartier condition on the
Čech cochains (`deligneIllusieInequality_of_staircase`; the vertical map out of the top row
vanishes because `Ω^{n+1} = 0`). Packaging these data as `DeligneIllusieStaircaseData`, Kodaira-type
vanishing `H^j(O(K_X + D)) = 0` (`j ≥ 1`, `D` ample) follows from the data for all `p^k • D`
(`canonical_vanishing_of_staircaseData`, with check 423): the global remainder of step 10 over a
finite field is the construction of these data from a lift modulo `p²`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u v

section ShortComplexes

variable {k : Type u} [Field k] [Finite k]

/-- **An additive map detecting boundaries bounds the dimension of homology**, over a finite
field. -/
theorem finrank_homology_le_of_additive {S₁ S₂ : ShortComplex (ModuleCat.{v} k)}
    (φ : S₁.X₂ →+ S₂.X₂) (hg : ∀ x, S₁.g.hom x = 0 → S₂.g.hom (φ x) = 0)
    (hinj : ∀ x, S₁.g.hom x = 0 → φ x ∈ LinearMap.range S₂.f.hom →
      x ∈ LinearMap.range S₁.f.hom)
    [FiniteDimensional k S₂.homology] :
    FiniteDimensional k S₁.homology ∧
      Module.finrank k S₁.homology ≤ Module.finrank k S₂.homology := by
  let e₁ := S₁.moduleCatHomologyIso.toLinearEquiv
  let e₂ := S₂.moduleCatHomologyIso.toLinearEquiv
  have : FiniteDimensional k S₂.moduleCatLeftHomologyData.H := LinearEquiv.finiteDimensional e₂
  have : Finite S₂.moduleCatLeftHomologyData.H := Module.finite_of_finite k
  let rep : S₁.moduleCatLeftHomologyData.H → LinearMap.ker S₁.g.hom :=
    Function.surjInv (Submodule.Quotient.mk_surjective _)
  have hrep : ∀ c, Submodule.Quotient.mk (rep c) = c :=
    Function.surjInv_eq (Submodule.Quotient.mk_surjective _)
  let g : S₁.moduleCatLeftHomologyData.H → S₂.moduleCatLeftHomologyData.H := fun c =>
    Submodule.Quotient.mk (⟨φ (rep c).1, hg _ (rep c).2⟩ : LinearMap.ker S₂.g.hom)
  have hginj : Function.Injective g := by
    intro c c' hcc'
    rw [← hrep c, ← hrep c']
    change Submodule.Quotient.mk (p := LinearMap.range S₂.moduleCatToCycles)
        (⟨φ (rep c).1, hg _ (rep c).2⟩ : LinearMap.ker S₂.g.hom) =
      Submodule.Quotient.mk (⟨φ (rep c').1, hg _ (rep c').2⟩ : LinearMap.ker S₂.g.hom) at hcc'
    rw [Submodule.Quotient.eq] at hcc' ⊢
    obtain ⟨a, ha⟩ := hcc'
    have hb : φ ((rep c).1 - (rep c').1) ∈ LinearMap.range S₂.f.hom :=
      ⟨a, by rw [map_sub]; exact congrArg Subtype.val ha⟩
    have hcyc : S₁.g.hom ((rep c).1 - (rep c').1) = 0 := by
      rw [map_sub, LinearMap.mem_ker.mp (rep c).2, LinearMap.mem_ker.mp (rep c').2, sub_zero]
    obtain ⟨b, hb'⟩ := hinj _ hcyc hb
    exact ⟨b, Subtype.ext hb'⟩
  have : Finite S₁.moduleCatLeftHomologyData.H := Finite.of_injective g hginj
  have : FiniteDimensional k S₁.moduleCatLeftHomologyData.H := Module.Finite.of_finite
  have hcard := Nat.card_le_card_of_injective g hginj
  have hc1 := Module.natCard_eq_pow_finrank (K := k) (V := S₁.moduleCatLeftHomologyData.H)
  have hc2 := Module.natCard_eq_pow_finrank (K := k) (V := S₂.moduleCatLeftHomologyData.H)
  rw [hc1, hc2] at hcard
  have hK : 1 < Nat.card k := Finite.one_lt_card
  have hle := (Nat.pow_le_pow_iff_right hK).mp hcard
  refine ⟨LinearEquiv.finiteDimensional e₁.symm, ?_⟩
  rw [e₁.finrank_eq, e₂.finrank_eq]
  exact hle

/-- **The same for `ℕ`-indexed cochain complexes in positive degrees.** -/
theorem finrank_homology_succ_le_of_additive {S T : CochainComplex (ModuleCat.{v} k) ℕ}
    (φ : ∀ m, S.X m →+ T.X m)
    (hφ : ∀ m x, φ (m + 1) ((S.d m (m + 1)).hom x) = (T.d m (m + 1)).hom (φ m x)) (m : ℕ)
    (hinj : ∀ x, (S.d (m + 1) (m + 1 + 1)).hom x = 0 →
      φ (m + 1) x ∈ LinearMap.range (T.d m (m + 1)).hom →
        x ∈ LinearMap.range (S.d m (m + 1)).hom)
    [FiniteDimensional k (T.homology (m + 1))] :
    FiniteDimensional k (S.homology (m + 1)) ∧
      Module.finrank k (S.homology (m + 1)) ≤ Module.finrank k (T.homology (m + 1)) := by
  let eS := (S.homologyIsoSc' m (m + 1) (m + 1 + 1) (CochainComplex.prev_nat_succ m)
    ((ComplexShape.up ℕ).next_eq' rfl)).toLinearEquiv
  let eT := (T.homologyIsoSc' m (m + 1) (m + 1 + 1) (CochainComplex.prev_nat_succ m)
    ((ComplexShape.up ℕ).next_eq' rfl)).toLinearEquiv
  have : FiniteDimensional k (T.sc' m (m + 1) (m + 1 + 1)).homology :=
    LinearEquiv.finiteDimensional eT
  obtain ⟨h1, h2⟩ := finrank_homology_le_of_additive (S₁ := S.sc' m (m + 1) (m + 1 + 1))
    (S₂ := T.sc' m (m + 1) (m + 1 + 1)) (φ (m + 1))
    (fun x hx => by
      have h := hφ (m + 1) x
      change (S.d (m + 1) (m + 1 + 1)).hom x = 0 at hx
      change (T.d (m + 1) (m + 1 + 1)).hom (φ (m + 1) x) = 0
      rw [← h, hx, map_zero]) hinj
  refine ⟨LinearEquiv.finiteDimensional eS.symm, ?_⟩
  rw [eS.finrank_eq, eT.finrank_eq]
  exact h2

end ShortComplexes

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra sectionsBaseModule

variable [IsIntegral X]

/-- **The vertical map out of the top row vanishes:** `Ω^{n+1}(p • D) = 0`. -/
theorem twistedFormsCechDiffLinearMap_top_apply {n : ℕ} (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (D : CartierDivisor X) {N : ℕ} (𝒰 : Fin N → X.Opens) (q : ℕ)
    (z : (cechComplexLinear K (twistedFormsSheaf K (p • D) n) 𝒰).X q) :
    ((twistedFormsCechDiffLinearMap p c₀ hcover D n 𝒰).f q).hom z = 0 := by
  have hs : ∀ U : X.Opens, Subsingleton Γ(twistedFormsSheaf K (p • D) (n + 1), U) := fun U =>
    twistedFormsSheaf_sections_subsingleton_of_lt c₀ (p • D) (Nat.lt_succ_self n) U
  have : Subsingleton (TopCat.Presheaf.CechCochain 𝒰
      (twistedFormsSheaf K (p • D) (n + 1)).presheaf q) :=
    ⟨fun a b => funext fun x => @Subsingleton.elim _ (hs _) _ _⟩
  exact @Subsingleton.elim _ this _ _

/-- **The Deligne–Illusie inequality from the staircase hypotheses**: an additive chain map
`⊕_b Č(Ω^b(D))[-b] → Čech–de Rham(Ω^•(p • D))` which does not raise the de Rham degree and whose
leading components `Φ_c` satisfy the Cartier condition on the Čech cochains gives
`Σ_{b ≤ n} h^{m-b}(Ω^b(D)) ≤ Σ_{b ≤ n} h^{m-b}(Ω^b(p • D))` for `m > n`, over a finite field. -/
theorem deligneIllusieInequality_of_staircase [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    {n : ℕ} (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤)
    (φ : ∀ m, (diSource K D 𝒰 n).X m →+ (cechDeRhamCone K p c₀ hcover D 𝒰).X m)
    (hφ : ∀ m x, φ (m + 1) (((diSource K D 𝒰 n).d m (m + 1)).hom x) =
      ((cechDeRhamCone K p c₀ hcover D 𝒰).d m (m + 1)).hom (φ m x))
    (htri : ∀ m c x,
      ConeRowsLE (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰) (fun _ => 0)
        (fun _ => comp_zero) n c m x →
      ConeRowsLE (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
        (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
        (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n c m (φ m x))
    (Φ : ∀ c q, (cechComplexLinear K (twistedFormsSheaf K D c) 𝒰).X q →+
      (cechComplexLinear K (twistedFormsSheaf K (p • D) c) 𝒰).X q)
    (hdiag : ∀ m c q (h : q + c = m) x,
      ConeRowsLE (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰) (fun _ => 0)
        (fun _ => comp_zero) n c m x →
      coneRowComp (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
          (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
          (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n 0 c c q m
          (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰)
          (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h x))
    (hsurj0 : ∀ q z, ((twistedFormsCechDiffLinearMap p c₀ hcover D 0 𝒰).f q).hom z = 0 →
      ∃ y, z = Φ 0 q y)
    (hsurj : ∀ c q z, ((twistedFormsCechDiffLinearMap p c₀ hcover D (c + 1) 𝒰).f q).hom z = 0 →
      ∃ y w, z = Φ (c + 1) q y + ((twistedFormsCechDiffLinearMap p c₀ hcover D c 𝒰).f q).hom w)
    (hinj0 : ∀ q y, Φ 0 q y = 0 → y = 0)
    (hinj : ∀ c q y w,
      Φ (c + 1) q y = ((twistedFormsCechDiffLinearMap p c₀ hcover D c 𝒰).f q).hom w → y = 0)
    {m : ℕ} (hm : n < m) : DeligneIllusieInequality K D p n m := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hinjS : ∀ x, ((diSource K D 𝒰 n).d (m + 1) (m + 1 + 1)).hom x = 0 →
      φ (m + 1) x ∈ LinearMap.range ((cechDeRhamCone K p c₀ hcover D 𝒰).d m (m + 1)).hom →
        x ∈ LinearMap.range ((diSource K D 𝒰 n).d m (m + 1)).hom := by
    rintro x hx ⟨y, hy⟩
    obtain ⟨s, hs⟩ := deligneIllusie_injective
      (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
      (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰)
      (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
      (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n φ hφ htri Φ hdiag hsurj0
      hsurj hinj0 hinj (fun q z => twistedFormsCechDiffLinearMap_top_apply p c₀ hcover D 𝒰 q z)
      m x y hx hy.symm
    exact ⟨s, hs.symm⟩
  obtain ⟨_, hS⟩ := finrank_diSource_homology hcover D 𝒰 h𝒰 hcov (m := m + 1) (by omega)
  obtain ⟨_, hTle⟩ := finrank_cechDeRhamCone_homology_le p c₀ hcover D 𝒰 h𝒰 hcov (m + 1)
  have hST := (finrank_homology_succ_le_of_additive φ hφ m hinjS).2
  unfold DeligneIllusieInequality
  omega

variable (K) in
/-- **The data of the Deligne–Illusie comparison** for `D` on the cover `𝒰`: an additive chain map
`⊕_b Č(Ω^b(D))[-b] → Čech–de Rham(Ω^•(p • D))` not raising the de Rham degree, whose leading
components satisfy the Cartier condition on the Čech cochains. -/
def DeligneIllusieStaircaseData {n : ℕ} (p : ℕ) [CharP K p] (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) : Prop :=
  ∃ (φ : ∀ m, (diSource K D 𝒰 n).X m →+ (cechDeRhamCone K p c₀ hcover D 𝒰).X m)
    (Φ : ∀ c q, (cechComplexLinear K (twistedFormsSheaf K D c) 𝒰).X q →+
      (cechComplexLinear K (twistedFormsSheaf K (p • D) c) 𝒰).X q),
    (∀ m x, φ (m + 1) (((diSource K D 𝒰 n).d m (m + 1)).hom x) =
      ((cechDeRhamCone K p c₀ hcover D 𝒰).d m (m + 1)).hom (φ m x)) ∧
    (∀ m c x,
      ConeRowsLE (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰) (fun _ => 0)
        (fun _ => comp_zero) n c m x →
      ConeRowsLE (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
        (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
        (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n c m (φ m x)) ∧
    (∀ m c q (h : q + c = m) x,
      ConeRowsLE (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰) (fun _ => 0)
        (fun _ => comp_zero) n c m x →
      coneRowComp (fun b => cechComplexLinear K (twistedFormsSheaf K (p • D) b) 𝒰)
          (fun b => twistedFormsCechDiffLinearMap p c₀ hcover D b 𝒰)
          (fun b => twistedFormsCechDiffLinearMap_comp p c₀ hcover D b 𝒰) n 0 c c q m
          (Nat.zero_add c) h (φ m x) =
        Φ c q (coneRowComp (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰)
          (fun _ => 0) (fun _ => comp_zero) n 0 c c q m (Nat.zero_add c) h x)) ∧
    (∀ q z, ((twistedFormsCechDiffLinearMap p c₀ hcover D 0 𝒰).f q).hom z = 0 →
      ∃ y, z = Φ 0 q y) ∧
    (∀ c q z, ((twistedFormsCechDiffLinearMap p c₀ hcover D (c + 1) 𝒰).f q).hom z = 0 →
      ∃ y w, z = Φ (c + 1) q y + ((twistedFormsCechDiffLinearMap p c₀ hcover D c 𝒰).f q).hom w) ∧
    (∀ q y, Φ 0 q y = 0 → y = 0) ∧
    (∀ c q y w,
      Φ (c + 1) q y = ((twistedFormsCechDiffLinearMap p c₀ hcover D c 𝒰).f q).hom w → y = 0)

/-- **Kodaira-type vanishing from the Deligne–Illusie comparison data**: over a finite field, if
the comparison data exist for all the divisors `p^k • D`, then `H^j(O(K_X + D)) = 0` for `j ≥ 1`
and ample `D`. -/
theorem canonical_vanishing_of_staircaseData [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    {n : ℕ} (p : ℕ) [CharP K p] (hp : 2 ≤ p) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X)
    (hD : CartierIsAmpleProj K D) {N : ℕ} (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i))
    (hcov : ⨆ i, 𝒰 i = ⊤)
    (hdata : ∀ k, DeligneIllusieStaircaseData K p c₀ hcover ((p ^ k) • D) 𝒰) {j : ℕ}
    (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + D).sheaf j) :=
  canonical_vanishing_of_deligneIllusie c₀ hcover p hp D hD (fun k m hm => by
    obtain ⟨φ, Φ, hφ, htri, hdiag, hsurj0, hsurj, hinj0, hinj⟩ := hdata k
    exact deligneIllusieInequality_of_staircase p c₀ hcover ((p ^ k) • D) 𝒰 h𝒰 hcov φ hφ htri Φ
      hdiag hsurj0 hsurj hinj0 hinj hm) hj

end MixedFujita
