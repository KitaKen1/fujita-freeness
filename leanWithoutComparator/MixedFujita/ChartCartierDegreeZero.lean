/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedChartCartier

/-!
The Cartier isomorphism in degree `0` and injectivity of the Deligne–Illusie map (step 10).

On an étale chart with a mod-`p²` Frobenius lift, a closed function is in the image of the
Deligne–Illusie map `Φ_F` (`chart_frobeniusLift_cartier_sections_zero`): the Cartier isomorphism of
check 421 in degree `0` leaves an exact error `dη`, which lies in degree `1` and so vanishes. The
same holds for `Ω^0(p • D)` with the twisted map `Φ_D` of check 437
(`twisted_chart_cartier_sections_zero`). In every degree, `Φ_F` and `Φ_D` are injective
(`chartFrobeniusLiftForms_eq_zero`, `twistedChartFrobeniusLiftForms_eq_zero`). These are the
degree-`0` and injectivity parts of the Cartier condition of the Deligne–Illusie comparison.
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
/-- **`Φ_F` is injective** on the sections of `Ω^b_X` over an étale chart. -/
theorem chartFrobeniusLiftForms_eq_zero [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)]
    (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0) (b : ℕ) (s : regularFormsSections K b c.U)
    (h : chartFrobeniusLiftForms c π hπ p F hF hker b s = 0) : s = 0 := by
  have h1 := congrArg (fun t => (chartFormsEquiv c b t :
    ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K])) h
  rw [chartFormsEquiv_chartFrobeniusLiftForms] at h1
  change _ = ((chartFormsEquiv c b 0 : ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K]) :
    ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) at h1
  rw [(chartFormsEquiv c b).map_zero, Submodule.coe_zero] at h1
  have h2 := frobeniusLiftExterior_eq_zero_of_mem_range c.coords c.formallyEtale p π hπ F hF hker
    hann hp2 hK hy0 (chartFormsEquiv c b s) (LinearMap.mem_range.mpr ⟨0, by rw [map_zero, h1]⟩)
  have h3 : chartFormsEquiv c b s = 0 := Subtype.ext h2
  exact (chartFormsEquiv c b).injective (h3.trans (chartFormsEquiv c b).map_zero.symm)

include hann hp2 hK in
/-- **The Cartier isomorphism in degree `0`**: a closed function on an étale chart is `Φ_F ω`. -/
theorem chart_frobeniusLift_cartier_sections_zero [PerfectRing K p]
    [Algebra.FiniteType K Γ(X, c.U)] (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0)
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (z : regularFormsSections K 0 c.U) (hz : regularFormsDiff c₀ hcover 0 c.U z = 0) :
    ∃ ω : regularFormsSections K 0 c.U, z = chartFrobeniusLiftForms c π hπ p F hF hker 0 ω := by
  have hz' : kaehlerDeRhamDiff c.coords c.formallyEtale
      (chartFormsEquiv c 0 z : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) = 0 := by
    have h := congrArg (fun t => (chartFormsEquiv c (0 + 1) t :
      ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K])) hz
    rw [chartFormsEquiv_regularFormsDiff, (chartFormsEquiv c (0 + 1)).map_zero] at h
    exact h
  obtain ⟨ω, hω, η, -, h⟩ := frobeniusLift_cartier_isomorphism_deg c.coords c.formallyEtale p π hπ
    F hF hker hann hp2 hK hy0 (chartFormsEquiv c 0 z) (chartFormsEquiv c 0 z).2 hz'
  have hmem : (chartFormsEquiv c 0 z : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) -
      frobeniusLiftExterior c.coords c.formallyEtale π hπ p F hF hker ω ∈
        ⋀[Γ(X, c.U)]^0 Ω[Γ(X, c.U)⁄K] :=
    Submodule.sub_mem _ (chartFormsEquiv c 0 z).2
      (frobeniusLiftExterior_mem_exteriorPower _ _ π hπ p F hF hker hω)
  have hzero : (chartFormsEquiv c 0 z : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) -
      frobeniusLiftExterior c.coords c.formallyEtale π hπ p F hF hker ω = 0 := by
    rw [← formsProj_of_mem_same hmem, h]
    exact formsProj_zero_kaehlerDeRhamDiff _ _ _
  refine ⟨(chartFormsEquiv c 0).symm ⟨ω, hω⟩, ?_⟩
  apply (chartFormsEquiv c 0).injective
  apply Subtype.ext
  rw [chartFormsEquiv_chartFrobeniusLiftForms, AddEquiv.apply_symm_apply]
  exact sub_eq_zero.mp hzero

section Twist

variable {D : CartierDivisor X} {g : X.functionFieldˣ}

include hann hp2 hK in
/-- **`Φ_D` is injective** on the sections of `Ω^b(D)` over an étale chart. -/
theorem twistedChartFrobeniusLiftForms_eq_zero [PerfectRing K p]
    [Algebra.FiniteType K Γ(X, c.U)] (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0)
    (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g) (b : ℕ) (ω : twistedFormsSections K D b c.U)
    (h : twistedChartFrobeniusLiftForms c π hπ p F hF hker hg b ω = 0) : ω = 0 := by
  have h1 := congrArg (fun t : twistedFormsSections K (p • D) b c.U =>
    (g : X.functionField) ^ p • rationalFormsSectionsEquiv K b c.U t.1) h
  rw [twistedChartFrobeniusLiftForms_val, smul_smul, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow,
    one_smul, Submodule.coe_zero, map_zero, smul_zero] at h1
  have h2 : chartFrobeniusLiftForms c π hπ p F hF hker b (twistToRegularForms c hg ω) = 0 :=
    Subtype.ext ((rationalFormsSectionsEquiv K b c.U).injective (h1.trans (map_zero _).symm))
  have h3 := chartFrobeniusLiftForms_eq_zero c π hπ p F hF hker hann hp2 hK hy0 b _ h2
  have h4 := congrArg (fun t : regularFormsSections K b c.U =>
    rationalFormsSectionsEquiv K b c.U t.1) h3
  rw [twistToRegularForms_val, Submodule.coe_zero, map_zero, smul_eq_zero] at h4
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K b c.U).injective
  rw [Submodule.coe_zero, map_zero]
  exact h4.resolve_left g.ne_zero

include hann hp2 hK in
/-- **The twisted Cartier isomorphism in degree `0`**: a closed section of `Ω^0(p • D)` over an
étale chart is `Φ_D ω`. -/
theorem twisted_chart_cartier_sections_zero [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)]
    (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0) (hg : ∀ x ∈ c.U, D.IsLocalEquationAt x g)
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤)
    (θ : twistedFormsSections K (p • D) 0 c.U)
    (hθ : twistedFormsDiff p c₀ hcover D 0 c.U θ = 0) :
    ∃ ω : twistedFormsSections K D 0 c.U,
      θ = twistedChartFrobeniusLiftForms c π hπ p F hF hker hg 0 ω := by
  let z : regularFormsSections K 0 c.U :=
    ⟨_, pow_smul_mem_regularFormsSections_of_twisted c p hg θ.1 θ.2⟩
  have hzval : rationalFormsSectionsEquiv K 0 c.U z.1 =
      (g : X.functionField) ^ p • rationalFormsSectionsEquiv K 0 c.U θ.1 :=
    AddEquiv.apply_symm_apply _ _
  have hθ' : rationalFormsDiff c₀ 0 (rationalFormsSectionsEquiv K 0 c.U θ.1) = 0 := by
    rw [← rationalFormsSectionsEquiv_twistedFormsDiff p c₀ hcover D 0 c.U θ, hθ,
      Submodule.coe_zero, map_zero]
  have hz : regularFormsDiff c₀ hcover 0 c.U z = 0 := by
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (0 + 1) c.U).injective
    rw [← regularFormsValue_apply, regularFormsValue_regularFormsDiff, regularFormsValue_apply,
      hzval, rationalFormsDiff_smul_pow_char p c₀ 0, hθ', smul_zero, Submodule.coe_zero,
      map_zero]
  obtain ⟨ω₀, h⟩ := chart_frobeniusLift_cartier_sections_zero c π hπ p F hF hker hann hp2 hK hy0
    c₀ hcover z hz
  refine ⟨⟨_, inv_smul_mem_twisted c hg ω₀⟩, ?_⟩
  have hreg : twistToRegularForms c hg ⟨_, inv_smul_mem_twisted c hg ω₀⟩ = ω₀ := by
    apply Subtype.ext
    apply (rationalFormsSectionsEquiv K 0 c.U).injective
    rw [twistToRegularForms_val]
    change (g : X.functionField) • rationalFormsSectionsEquiv K 0 c.U
      ((rationalFormsSectionsEquiv K 0 c.U).symm
        ((g : X.functionField)⁻¹ • rationalFormsSectionsEquiv K 0 c.U ω₀.1)) = _
    rw [AddEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ g.ne_zero, one_smul]
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K 0 c.U).injective
  rw [twistedChartFrobeniusLiftForms_val, hreg, ← h, hzval, smul_smul, ← mul_pow,
    inv_mul_cancel₀ g.ne_zero, one_pow, one_smul]

end Twist

end MixedFujita
