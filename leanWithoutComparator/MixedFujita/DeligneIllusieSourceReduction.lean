/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CechDeRhamConeBound
public import MixedFujita.CanonicalTwistedForms

/-!
The source of the Deligne–Illusie map and the reduction of the vanishing theorem (step 10).

The source of the Deligne–Illusie map is `⊕_{b ≤ n} Č(Ω^b(D))[-b]`, the iterated cone of the rows
`Č(Ω^b(D))` with zero vertical maps (`diSource`). By the direct-sum case of check 434 and the
dimension comparison of check 435, `dim H^m(diSource) = Σ_{b ≤ n} h^{m-b}(Ω^b(D))` for `m ≥ n`
(`finrank_diSource_homology`), the left-hand side of the Deligne–Illusie inequality. Over a finite
field an injective additive map between finite-dimensional spaces bounds the dimension
(`finrank_le_of_injective_addMonoidHom`). So the Deligne–Illusie inequality in degree `m ≥ n`
follows from an injective additive map `H^m(diSource D) → H^m(cechDeRhamCone (p • D))`
(`deligneIllusieInequality_of_injective`), and with check 423 the vanishing
`H^j(O(K_X + D)) = 0` for `j ≥ 1` and ample `D` follows from such maps for the divisors `p^k • D`
(`canonical_vanishing_of_injective_deligneIllusie`). The global Deligne–Illusie map need only be
additive (it is Frobenius-semilinear) and injective on cohomology.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

section FiniteField

variable {K : Type u} [Field K] [Finite K]

/-- **Over a finite field an injective additive map bounds the dimension.** -/
theorem finrank_le_of_injective_addMonoidHom {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K N] (f : M →+ N) (hf : Function.Injective f) :
    Module.Finite K M ∧ Module.finrank K M ≤ Module.finrank K N := by
  have : Finite N := Module.finite_of_finite K
  have : Finite M := Finite.of_injective f hf
  have hM : Module.Finite K M := Module.Finite.of_finite
  refine ⟨hM, ?_⟩
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := M)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := N)
  have h3 : Nat.card M ≤ Nat.card N := Nat.card_le_card_of_injective f hf
  have hK : 1 < Nat.card K := Finite.one_lt_card
  rw [h1, h2] at h3
  exact (Nat.pow_le_pow_iff_right hK).mp h3

end FiniteField

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra sectionsBaseModule

variable [IsIntegral X]

variable (K) in
/-- **The source of the Deligne–Illusie map**, `⊕_{b ≤ n} Č(Ω^b(D))[-b]`: the iterated cone of the
rows `Č(Ω^b(D))` with zero vertical maps. -/
noncomputable def diSource (D : CartierDivisor X) {N : ℕ} (𝒰 : Fin N → X.Opens) (n : ℕ) :
    CochainComplex (ModuleCat.{u} K) ℕ :=
  iteratedCone (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰) (fun _ => 0)
    (fun _ => comp_zero) n 0

/-- **The left-hand side of the Deligne–Illusie inequality:** for `m ≥ n`,
`dim H^m(diSource) = Σ_{b ≤ n} h^{m-b}(Ω^b(D))`, over a finite field. -/
theorem finrank_diSource_homology [Finite K] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (pullback.diagonal (terminal.from X))] {n : ℕ}
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i)) (hcov : ⨆ i, 𝒰 i = ⊤) {m : ℕ}
    (hm : n ≤ m) :
    FiniteDimensional K ((diSource K D 𝒰 n).homology m) ∧
      Module.finrank K ((diSource K D 𝒰 n).homology m) = twistedHodgeCount K D n m := by
  obtain ⟨h1, h2⟩ := finrank_iteratedCone_zero_homology
    (fun b => cechComplexLinear K (twistedFormsSheaf K D b) 𝒰)
    (fun b q => (finrank_cechComplexLinear_twistedForms_homology hcover D b 𝒰 h𝒰 hcov q).1) n 0 m
  refine ⟨h1, h2.trans ?_⟩
  rw [coneFiltrationBound, twistedHodgeCount, Nat.sub_zero, zero_add]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbm : b ≤ m := by
    rw [Finset.mem_range] at hb
    omega
  simp only [hbm, ↓reduceIte]
  rw [zero_add]
  exact (finrank_cechComplexLinear_twistedForms_homology hcover D b 𝒰 h𝒰 hcov (m - b)).2

/-- **The Deligne–Illusie inequality from an injective map on cohomology:** an injective additive
map `H^m(⊕_b Č(Ω^b(D))[-b]) → H^m(Čech–de Rham(Ω^•(p • D)))` gives
`Σ_{b ≤ n} h^{m-b}(Ω^b(D)) ≤ Σ_{b ≤ n} h^{m-b}(Ω^b(p • D))` for `m ≥ n`, over a finite field. -/
theorem deligneIllusieInequality_of_injective [Finite K] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [IsAffineHom (pullback.diagonal (terminal.from X))] {n : ℕ} (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (D : CartierDivisor X) {N : ℕ} (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i))
    (hcov : ⨆ i, 𝒰 i = ⊤) {m : ℕ} (hm : n ≤ m)
    (f : (diSource K D 𝒰 n).homology m →+ (cechDeRhamCone K p c₀ hcover D 𝒰).homology m)
    (hf : Function.Injective f) : DeligneIllusieInequality K D p n m := by
  obtain ⟨_, hS⟩ := finrank_diSource_homology hcover D 𝒰 h𝒰 hcov hm
  obtain ⟨_, hTle⟩ := finrank_cechDeRhamCone_homology_le p c₀ hcover D 𝒰 h𝒰 hcov m
  have hST := (finrank_le_of_injective_addMonoidHom (K := K) f hf).2
  unfold DeligneIllusieInequality
  omega

/-- **Kodaira-type vanishing from injective Deligne–Illusie maps:** over a finite field, if for
every `k` and `m > n` there is an injective additive map
`H^m(⊕_b Č(Ω^b(p^k • D))[-b]) → H^m(Čech–de Rham(Ω^•(p^{k+1} • D)))`, then
`H^j(O(K_X + D)) = 0` for `j ≥ 1` and ample `D`. -/
theorem canonical_vanishing_of_injective_deligneIllusie [Finite K]
    [IsProper (X ↘ Spec (CommRingCat.of K))] [IsAffineHom (pullback.diagonal (terminal.from X))]
    {n : ℕ} (p : ℕ) [CharP K p] (hp : 2 ≤ p) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X)
    (hD : CartierIsAmpleProj K D) {N : ℕ} (𝒰 : Fin N → X.Opens) (h𝒰 : ∀ i, IsAffineOpen (𝒰 i))
    (hcov : ⨆ i, 𝒰 i = ⊤)
    (hinj : ∀ k m, n < m → ∃ f : (diSource K ((p ^ k) • D) 𝒰 n).homology m →+
      (cechDeRhamCone K p c₀ hcover ((p ^ k) • D) 𝒰).homology m, Function.Injective f)
    {j : ℕ} (hj : 1 ≤ j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology
      (canonicalDivisor n c₀ hcover + D).sheaf j) :=
  canonical_vanishing_of_deligneIllusie c₀ hcover p hp D hD (fun k m hm => by
    obtain ⟨f, hf⟩ := hinj k m hm
    exact deligneIllusieInequality_of_injective p c₀ hcover ((p ^ k) • D) 𝒰 h𝒰 hcov hm.le f hf)
    hj

end MixedFujita
