/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedChartDIRestriction

/-!
The twisted Deligne–Illusie components depend only on the first vertices, and the top cocycle
relation (step 10).

* The component of Čech degree `a` of the Deligne–Illusie map on `b`-forms only depends on the
  first `a + 1` vertices of the sequence (`seqSupported_diSeqAlt`, from check 452 on generators),
  hence so does the twisted component `Θ^{b,a}_s` (`twistedChartDIComponent_congr`).
* In the top degree `a = b` the next component vanishes (check 453), so the cocycle relation of
  check 461 becomes `Σ_{k ≤ b+1} (-1)^k Θ^{b,b}_{s ∘ skip k}(ω) = 0`
  (`twistedChartDIComponent_cocycle_top`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u w

section Support

variable {J : Type*} {A : Type*} [Ring A]

theorem seqSupported_zero_fun (a : ℕ) : SeqSupported a (fun _ : ℕ → J => (0 : A)) :=
  fun _ _ _ => rfl

theorem seqSupported_add_fun {a : ℕ} {α β : (ℕ → J) → A} (hα : SeqSupported a α)
    (hβ : SeqSupported a β) : SeqSupported a (fun s => α s + β s) :=
  fun s t h => by
    show α s + β s = α t + β t
    rw [hα s t h, hβ s t h]

end Support

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Algebra

variable {K' : Type u} [Field K'] {S : Type*} [CommRing S] [Algebra K' S] {m : ℕ}
  (y : MvPolynomial (Fin m) K' →ₐ[K'] S) (hy : y.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime]
  [CharP K' p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- **The components of the Deligne–Illusie map on `b`-forms only depend on the first vertices.** -/
theorem seqSupported_diSeqAlt (b : ℕ) (x : ⋀[S]^b Ω[S⁄K']) (a : ℕ) :
    SeqSupported a (twistedPiHom K' S p J (diSeqAlt y hy π hπ p F hF hker b x) a) := by
  induction span_ιMulti_mem b x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    rw [diSeqAlt_ιMulti, map_sum]
    intro s t h
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Units.smul_def, map_zsmul, Pi.smul_apply]
    congr 1
    exact seqSupported_diSeqProd y hy π hπ p F hF hker _ a s t h
  | zero =>
    rw [map_zero, map_zero]
    exact seqSupported_zero_fun a
  | add x z _ _ hx hz =>
    rw [map_add, map_add]
    exact seqSupported_add_fun hx hz
  | smul f x _ hx =>
    rw [map_smul, twistedPiHom_smul]
    intro s t h
    simp only
    rw [hx s t h]

end Algebra

section Chart

variable (c : EtaleChart K X n) {L : Type w} [CommRing L] (π : L →+* Γ(X, c.U))
  (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime] [CharP K p] {J : Type*}
  (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  {D : CartierDivisor X} {g : X.functionFieldˣ}

omit [IsIntegral X] in
theorem diSeqAltComponent_congr (b i a : ℕ) (h : i + a = b) {s t : ℕ → J}
    (hst : ∀ k ≤ a, s k = t k) (z : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    diSeqAltComponent c π hπ p F hF hker b i a h s z =
      diSeqAltComponent c π hπ p F hF hker b i a h t z :=
  Subtype.ext (seqSupported_diSeqAlt c.coords c.formallyEtale π hπ p F hF hker b z a s t hst)

/-- **The twisted components only depend on the first `a + 1` vertices.** -/
theorem twistedChartDIComponent_congr (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b i a : ℕ)
    (h : i + a = b) {s t : ℕ → J} (hst : ∀ k ≤ a, s k = t k) (ω : twistedFormsSections K D b c.U) :
    twistedChartDIComponent c π hπ p F hF hker hg b i a h s ω =
      twistedChartDIComponent c π hπ p F hF hker hg b i a h t ω := by
  rw [twistedChartDIComponent_eq, twistedChartDIComponent_eq,
    diSeqAltComponent_congr c π hπ p F hF hker b i a h hst]

variable (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hK : ∀ k : K, ∃ k' : L, π k' = algebraMap K Γ(X, c.U) k ∧ ∀ j, F j k' = k' ^ p)

omit [IsIntegral X] in
include hann hp2 hK in
/-- The top cocycle relation of the components of the Deligne–Illusie map. -/
theorem diSeqAltComponent_cocycle_top [Algebra.FiniteType K Γ(X, c.U)] (b : ℕ) (s : ℕ → J)
    (x : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    ∑ k ∈ Finset.range (b + 2), (-1 : ℤ) ^ k •
        diSeqAltComponent c π hπ p F hF hker b 0 b (zero_add b) (s ∘ seqSkip k) x = 0 := by
  have hD := congrFun (congrFun (seqTotalD_diSeqAlt c.coords c.formallyEtale π hπ p F hF hker hann
    hp2 hK b x) (b + 1)) s
  have htop := (seqTotalHomogeneous_diSeqAlt c.coords c.formallyEtale π hπ p F hF hker b x (b + 1)
    s).2 (Nat.lt_succ_self b)
  simp only [seqTotalD, seqTotalCechD, seqTotalDeRham, seqCechD, Pi.zero_apply,
    LinearMap.toAddMonoidHom_coe] at hD
  rw [htop, map_zero, mul_zero, add_zero] at hD
  apply Subtype.ext
  rw [Submodule.coe_sum, Submodule.coe_zero]
  simp only [Submodule.coe_smul_of_tower, diSeqAltComponent_coe]
  have hsum : ∀ (k : ℕ) (w : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]),
      (-1 : ℤ) ^ k • w = (-1 : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) ^ k * w := fun k w => by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  simp only [hsum]
  exact hD

include hann hp2 hK in
/-- **The top cocycle relation of the twisted components**:
`Σ_{k ≤ b+1} (-1)^k Θ^{b,b}_{s ∘ skip k}(ω) = 0`. -/
theorem twistedChartDIComponent_cocycle_top [Algebra.FiniteType K Γ(X, c.U)]
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b : ℕ) (s : ℕ → J)
    (ω : twistedFormsSections K D b c.U) :
    ∑ k ∈ Finset.range (b + 2), (-1 : ℤ) ^ k •
        twistedChartDIComponent c π hπ p F hF hker hg b 0 b (zero_add b) (s ∘ seqSkip k) ω = 0 := by
  simp only [twistedChartDIComponent_eq]
  have e : ∀ (j : ℕ) (z : ⋀[Γ(X, c.U)]^j Ω[Γ(X, c.U)⁄K]),
      twistBackForms c p hg j z = twistBackFormsHom c p hg j z := fun _ _ => rfl
  simp only [e, ← map_zsmul, ← map_sum]
  rw [diSeqAltComponent_cocycle_top c π hπ p F hF hker hann hp2 hK b s, map_zero]

end Chart

end MixedFujita
