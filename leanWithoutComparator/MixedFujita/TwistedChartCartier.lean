/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartDeligneIllusieSections
public import MixedFujita.TwistedDifferentialForms

/-!
The Cartier isomorphism for `Ω^•(p • D)` on the sections over an étale chart (step 10).

On an étale chart `c` on which `D` has the equation `g` at every point, multiplication by `g` sends
the sections of `Ω^b(D)` to regular sections (`twistToRegularForms`), and `g^p` is an equation of
`p • D`. The twisted Deligne–Illusie map `Φ_D ω = g^{-p} Φ_F (g ω)`
(`twistedChartFrobeniusLiftForms`, additive) sends `Ω^b(D)` to `Ω^b(p • D)`; its values are
closed for the de Rham differential of `Ω^•(p • D)` (`twistedFormsDiff_twistedChartFrobeniusLiftForms`,
as `d(g^{-p} θ) = g^{-p} dθ` in characteristic `p`), and the Cartier isomorphism holds on the
sections: every closed section of `Ω^{k+1}(p • D)` is `Φ_D ω + dη`
(`twisted_chart_cartier_sections`), and `Φ_D ω` is exact only for `ω = 0`
(`twistedChartFrobeniusLiftForms_eq_zero_of_exact`, from the untwisted
`chartFrobeniusLiftForms_eq_zero_of_exact`). This is the chart input of the Deligne–Illusie
comparison on the Čech cochains of `Ω^•(p • D)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u w

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

variable (c : EtaleChart K X n) {L : Type w} [CommRing L] (π : L →+* Γ(X, c.U))
  (hπ : Function.Surjective π) (p : ℕ) [Fact p.Prime] [CharP K p] (F : L →+* L)
  (hF : ∀ x, π (F x) = π x ^ p) (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hann : ∀ z, (p : L) * z = 0 → π z = 0) (hp2 : (p : L) * p = 0)
  (hK : ∀ a : K, ∃ a' : L, π a' = algebraMap K Γ(X, c.U) a ∧ F a' = a' ^ p)

include hann hp2 hK in
/-- **`Φ_F ω` is exact only for `ω = 0`**, on the sections over an étale chart. -/
theorem chartFrobeniusLiftForms_eq_zero_of_exact [PerfectRing K p]
    [Algebra.FiniteType K Γ(X, c.U)] (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0)
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (k : ℕ)
    (s : regularFormsSections K (k + 1) c.U) (η : regularFormsSections K k c.U)
    (h : chartFrobeniusLiftForms c π hπ p F hF hker (k + 1) s =
      regularFormsDiff c₀ hcover k c.U η) :
    s = 0 := by
  have h1 := congrArg (fun t => (chartFormsEquiv c (k + 1) t :
    ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K])) h
  rw [chartFormsEquiv_chartFrobeniusLiftForms, chartFormsEquiv_regularFormsDiff] at h1
  have h2 := frobeniusLiftExterior_eq_zero_of_mem_range c.coords c.formallyEtale p π hπ F hF hker
    hann hp2 hK hy0 (chartFormsEquiv c (k + 1) s) (LinearMap.mem_range.mpr ⟨_, h1.symm⟩)
  have h3 : chartFormsEquiv c (k + 1) s = 0 := Subtype.ext h2
  exact (chartFormsEquiv c (k + 1)).injective (h3.trans (chartFormsEquiv c (k + 1)).map_zero.symm)

section Twist

variable {D : CartierDivisor X} {g : X.functionFieldˣ}

/-- Multiplying a section of `Ω^b(D)` by the equation `g` gives a regular section. -/
theorem smul_mem_regularFormsSections_of_twisted (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    {b : ℕ} (ω : Γ(rationalFormsSheaf K X b, c.U)) (hω : ω ∈ twistedFormsSections K D b c.U) :
    (rationalFormsSectionsEquiv K b c.U).symm
        ((g : X.functionField) • rationalFormsSectionsEquiv K b c.U ω) ∈
      regularFormsSections K b c.U := by
  intro x hx
  rw [AddEquiv.apply_symm_apply]
  exact hω x hx g (hg x hx)

/-- Dividing a regular section by the equation `g` gives a section of `Ω^b(D)`. -/
theorem inv_smul_mem_twisted (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (s : regularFormsSections K b c.U) :
    (rationalFormsSectionsEquiv K b c.U).symm
        ((g : X.functionField)⁻¹ • rationalFormsSectionsEquiv K b c.U s.1) ∈
      twistedFormsSections K D b c.U := by
  intro x hx f hf
  rw [AddEquiv.apply_symm_apply, smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf
    (hg x hx), smul_smul, mul_inv_cancel₀ g.ne_zero, one_smul]
  exact s.2 x hx

omit [Fact p.Prime] [CharP K p] in
/-- Dividing a regular section by `g ^ p` gives a section of `Ω^b(p • D)`. -/
theorem inv_pow_smul_mem_twisted (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (s : regularFormsSections K b c.U) :
    (rationalFormsSectionsEquiv K b c.U).symm
        (((g : X.functionField)⁻¹) ^ p • rationalFormsSectionsEquiv K b c.U s.1) ∈
      twistedFormsSections K (p • D) b c.U := by
  intro x hx f hf
  rw [AddEquiv.apply_symm_apply, smul_mem_range_stalkFormsMap_iff_of_isLocalEquationAt hf
    (isLocalEquationAt_nsmul_pow (hg x hx) p), Units.val_pow_eq_pow_val, smul_smul, ← mul_pow,
    mul_inv_cancel₀ g.ne_zero, one_pow, one_smul]
  exact s.2 x hx

omit [Fact p.Prime] [CharP K p] in
/-- Multiplying a section of `Ω^b(p • D)` by `g ^ p` gives a regular section. -/
theorem pow_smul_mem_regularFormsSections_of_twisted
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ} (θ : Γ(rationalFormsSheaf K X b, c.U))
    (hθ : θ ∈ twistedFormsSections K (p • D) b c.U) :
    (rationalFormsSectionsEquiv K b c.U).symm
        ((g : X.functionField) ^ p • rationalFormsSectionsEquiv K b c.U θ) ∈
      regularFormsSections K b c.U := by
  intro x hx
  rw [AddEquiv.apply_symm_apply]
  have h := hθ x hx (g ^ p) (isLocalEquationAt_nsmul_pow (hg x hx) p)
  rwa [Units.val_pow_eq_pow_val] at h

/-- The regular section `g • ω` of a section `ω` of `Ω^b(D)`. -/
noncomputable def twistToRegularForms (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (ω : twistedFormsSections K D b c.U) : regularFormsSections K b c.U :=
  ⟨_, smul_mem_regularFormsSections_of_twisted c hg ω.1 ω.2⟩

theorem twistToRegularForms_val (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (ω : twistedFormsSections K D b c.U) :
    rationalFormsSectionsEquiv K b c.U (twistToRegularForms c hg ω).1 =
      (g : X.functionField) • rationalFormsSectionsEquiv K b c.U ω.1 :=
  AddEquiv.apply_symm_apply _ _

theorem twistToRegularForms_add (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) {b : ℕ}
    (ω ω' : twistedFormsSections K D b c.U) :
    twistToRegularForms c hg (ω + ω') = twistToRegularForms c hg ω + twistToRegularForms c hg ω' := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K b c.U).injective
  rw [Submodule.coe_add, map_add, twistToRegularForms_val, twistToRegularForms_val,
    twistToRegularForms_val, Submodule.coe_add, map_add, smul_add]

/-- **The twisted Deligne–Illusie map** `Φ_D ω = g^{-p} Φ_F (g ω)` from `Ω^b(D)` to
`Ω^b(p • D)` over an étale chart on which `g` is an equation of `D`. -/
noncomputable def twistedChartFrobeniusLiftForms (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (b : ℕ) (ω : twistedFormsSections K D b c.U) : twistedFormsSections K (p • D) b c.U :=
  ⟨_, inv_pow_smul_mem_twisted c p hg
    (chartFrobeniusLiftForms c π hπ p F hF hker b (twistToRegularForms c hg ω))⟩

theorem twistedChartFrobeniusLiftForms_val (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b : ℕ)
    (ω : twistedFormsSections K D b c.U) :
    rationalFormsSectionsEquiv K b c.U (twistedChartFrobeniusLiftForms c π hπ p F hF hker hg b ω).1 =
      ((g : X.functionField)⁻¹) ^ p • rationalFormsSectionsEquiv K b c.U
        (chartFrobeniusLiftForms c π hπ p F hF hker b (twistToRegularForms c hg ω)).1 :=
  AddEquiv.apply_symm_apply _ _

theorem twistedChartFrobeniusLiftForms_add (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b : ℕ)
    (ω ω' : twistedFormsSections K D b c.U) :
    twistedChartFrobeniusLiftForms c π hπ p F hF hker hg b (ω + ω') =
      twistedChartFrobeniusLiftForms c π hπ p F hF hker hg b ω +
        twistedChartFrobeniusLiftForms c π hπ p F hF hker hg b ω' := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K b c.U).injective
  rw [Submodule.coe_add, map_add, twistedChartFrobeniusLiftForms_val,
    twistedChartFrobeniusLiftForms_val, twistedChartFrobeniusLiftForms_val, twistToRegularForms_add,
    chartFrobeniusLiftForms_add, Submodule.coe_add, map_add, smul_add]

include hann hp2 hK in
/-- **The values of the twisted Deligne–Illusie map are closed.** -/
theorem twistedFormsDiff_twistedChartFrobeniusLiftForms [Algebra.FiniteType K Γ(X, c.U)]
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ)
    (ω : twistedFormsSections K D b c.U) :
    twistedFormsDiff p c₀ hcover D b c.U (twistedChartFrobeniusLiftForms c π hπ p F hF hker hg b ω) =
      0 := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K (b + 1) c.U).injective
  rw [rationalFormsSectionsEquiv_twistedFormsDiff, twistedChartFrobeniusLiftForms_val,
    rationalFormsDiff_smul_pow_char p c₀ b, ← regularFormsValue_apply,
    ← regularFormsValue_regularFormsDiff c₀ hcover,
    regularFormsDiff_chartFrobeniusLiftForms c π hπ p F hF hker hann hp2 hK c₀ hcover, map_zero,
    smul_zero, Submodule.coe_zero, map_zero]

include hann hp2 hK in
/-- **The Cartier isomorphism for `Ω^•(p • D)` on the sections over an étale chart**: every closed
section of `Ω^{k+1}(p • D)` is `Φ_D ω + dη`. -/
theorem twisted_chart_cartier_sections [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)]
    (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0) (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (k : ℕ)
    (θ : twistedFormsSections K (p • D) (k + 1) c.U)
    (hθ : twistedFormsDiff p c₀ hcover D (k + 1) c.U θ = 0) :
    ∃ ω : twistedFormsSections K D (k + 1) c.U, ∃ η : twistedFormsSections K (p • D) k c.U,
      θ = twistedChartFrobeniusLiftForms c π hπ p F hF hker hg (k + 1) ω +
        twistedFormsDiff p c₀ hcover D k c.U η := by
  let z : regularFormsSections K (k + 1) c.U :=
    ⟨_, pow_smul_mem_regularFormsSections_of_twisted c p hg θ.1 θ.2⟩
  have hzval : rationalFormsSectionsEquiv K (k + 1) c.U z.1 =
      (g : X.functionField) ^ p • rationalFormsSectionsEquiv K (k + 1) c.U θ.1 :=
    AddEquiv.apply_symm_apply _ _
  have hθ' : rationalFormsDiff c₀ (k + 1) (rationalFormsSectionsEquiv K (k + 1) c.U θ.1) = 0 := by
    rw [← rationalFormsSectionsEquiv_twistedFormsDiff p c₀ hcover D (k + 1) c.U θ, hθ,
      Submodule.coe_zero, map_zero]
  have hz : regularFormsDiff c₀ hcover (k + 1) c.U z = 0 := by
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (k + 2) c.U).injective
    rw [← regularFormsValue_apply, regularFormsValue_regularFormsDiff, regularFormsValue_apply,
      hzval, rationalFormsDiff_smul_pow_char p c₀ (k + 1), hθ', smul_zero, Submodule.coe_zero,
      map_zero]
  obtain ⟨ω₀, η₀, h⟩ := chart_frobeniusLift_cartier_sections c π hπ p F hF hker hann hp2 hK hy0 c₀
    hcover k z hz
  refine ⟨⟨_, inv_smul_mem_twisted c hg ω₀⟩, ⟨_, inv_pow_smul_mem_twisted c p hg η₀⟩, ?_⟩
  have hreg : twistToRegularForms c hg ⟨_, inv_smul_mem_twisted c hg ω₀⟩ = ω₀ := by
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (k + 1) c.U).injective
    rw [twistToRegularForms_val]
    change (g : X.functionField) • rationalFormsSectionsEquiv K (k + 1) c.U
      ((rationalFormsSectionsEquiv K (k + 1) c.U).symm
        ((g : X.functionField)⁻¹ • rationalFormsSectionsEquiv K (k + 1) c.U ω₀.1)) = _
    rw [AddEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ g.ne_zero, one_smul]
  have hzθ : rationalFormsSectionsEquiv K (k + 1) c.U θ.1 =
      ((g : X.functionField)⁻¹) ^ p • rationalFormsSectionsEquiv K (k + 1) c.U z.1 := by
    rw [hzval, smul_smul, ← mul_pow, inv_mul_cancel₀ g.ne_zero, one_pow, one_smul]
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K (k + 1) c.U).injective
  rw [Submodule.coe_add, map_add, twistedChartFrobeniusLiftForms_val, hreg,
    rationalFormsSectionsEquiv_twistedFormsDiff, hzθ, h, Submodule.coe_add, map_add, smul_add]
  congr 1
  change _ = rationalFormsDiff c₀ k (rationalFormsSectionsEquiv K k c.U
    ((rationalFormsSectionsEquiv K k c.U).symm
      (((g : X.functionField)⁻¹) ^ p • rationalFormsSectionsEquiv K k c.U η₀.1)))
  rw [AddEquiv.apply_symm_apply, rationalFormsDiff_smul_pow_char p c₀ k, ← regularFormsValue_apply,
    ← regularFormsValue_apply, regularFormsValue_regularFormsDiff]

include hann hp2 hK in
/-- **`Φ_D ω` is exact only for `ω = 0`**, on the sections over an étale chart. -/
theorem twistedChartFrobeniusLiftForms_eq_zero_of_exact [PerfectRing K p]
    [Algebra.FiniteType K Γ(X, c.U)] (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0)
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (k : ℕ)
    (ω : twistedFormsSections K D (k + 1) c.U) (η : twistedFormsSections K (p • D) k c.U)
    (h : twistedChartFrobeniusLiftForms c π hπ p F hF hker hg (k + 1) ω =
      twistedFormsDiff p c₀ hcover D k c.U η) :
    ω = 0 := by
  let η' : regularFormsSections K k c.U :=
    ⟨_, pow_smul_mem_regularFormsSections_of_twisted c p hg η.1 η.2⟩
  have hη'val : rationalFormsSectionsEquiv K k c.U η'.1 =
      (g : X.functionField) ^ p • rationalFormsSectionsEquiv K k c.U η.1 :=
    AddEquiv.apply_symm_apply _ _
  have h1 := congrArg (fun t : twistedFormsSections K (p • D) (k + 1) c.U =>
    (g : X.functionField) ^ p • rationalFormsSectionsEquiv K (k + 1) c.U t.1) h
  rw [twistedChartFrobeniusLiftForms_val, smul_smul, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow,
    one_smul, rationalFormsSectionsEquiv_twistedFormsDiff, ← rationalFormsDiff_smul_pow_char p c₀ k,
    ← hη'val, ← regularFormsValue_apply K k c.U η', ← regularFormsValue_regularFormsDiff c₀ hcover,
    regularFormsValue_apply] at h1
  have h2 : chartFrobeniusLiftForms c π hπ p F hF hker (k + 1) (twistToRegularForms c hg ω) =
      regularFormsDiff c₀ hcover k c.U η' :=
    Subtype.ext ((rationalFormsSectionsEquiv K (k + 1) c.U).injective h1)
  have h3 := chartFrobeniusLiftForms_eq_zero_of_exact c π hπ p F hF hker hann hp2 hK hy0 c₀ hcover
    k _ η' h2
  have h4 := congrArg (fun t : regularFormsSections K (k + 1) c.U =>
    rationalFormsSectionsEquiv K (k + 1) c.U t.1) h3
  rw [twistToRegularForms_val, Submodule.coe_zero, map_zero, smul_eq_zero] at h4
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K (k + 1) c.U).injective
  rw [Submodule.coe_zero, map_zero]
  exact h4.resolve_left g.ne_zero

end Twist

end MixedFujita
