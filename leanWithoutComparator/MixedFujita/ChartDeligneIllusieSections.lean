/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GradedCartierIsomorphism
public import MixedFujita.DifferentialFormsDeRham

/-!
The Deligne–Illusie map on the sections of `Ω^•_X` over an étale chart (step 10).

On an étale chart `c`, with a mod-`p²` Frobenius lift of `Γ(X, U)` (the data of check-407), the
Deligne–Illusie map `Φ_F` of the exterior algebra (check-408) preserves the degrees (check-413), so
through the chart identification `Γ(U, Ω^b_X) ≅ ⋀^b Ω[Γ(U)⁄K]` (check-415) it acts on the sections
of `Ω^b_X` (`chartFrobeniusLiftForms`, additive). Its values are closed for the de Rham
differential of `Ω^•_X` (`regularFormsDiff_chartFrobeniusLiftForms`, check-416), and the
Cartier isomorphism holds on sections degree by degree (check-421): every closed section of
`Ω^{k+1}_X` over the chart is `Φ_F ω + dη` with `ω` a section of `Ω^{k+1}_X` and `η` one of
`Ω^k_X` (`chart_frobeniusLift_cartier_sections`). These are the local components of the global
Deligne–Illusie map, and the chart input of its quasi-isomorphism.
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

/-- **The Deligne–Illusie map of a Frobenius lift on the sections of `Ω^b_X` over an étale
chart.** -/
noncomputable def chartFrobeniusLiftForms (b : ℕ) (s : regularFormsSections K b c.U) :
    regularFormsSections K b c.U :=
  (chartFormsEquiv c b).symm
    ⟨frobeniusLiftExterior c.coords c.formallyEtale π hπ p F hF hker (chartFormsEquiv c b s),
      frobeniusLiftExterior_mem_exteriorPower _ _ π hπ p F hF hker (chartFormsEquiv c b s).2⟩

theorem chartFormsEquiv_chartFrobeniusLiftForms (b : ℕ) (s : regularFormsSections K b c.U) :
    (chartFormsEquiv c b (chartFrobeniusLiftForms c π hπ p F hF hker b s) :
        ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) =
      frobeniusLiftExterior c.coords c.formallyEtale π hπ p F hF hker (chartFormsEquiv c b s) := by
  rw [chartFrobeniusLiftForms, AddEquiv.apply_symm_apply]

theorem chartFrobeniusLiftForms_add (b : ℕ) (s t : regularFormsSections K b c.U) :
    chartFrobeniusLiftForms c π hπ p F hF hker b (s + t) =
      chartFrobeniusLiftForms c π hπ p F hF hker b s +
        chartFrobeniusLiftForms c π hπ p F hF hker b t := by
  apply (chartFormsEquiv c b).injective
  apply Subtype.ext
  rw [(chartFormsEquiv c b).map_add, Submodule.coe_add, chartFormsEquiv_chartFrobeniusLiftForms,
    chartFormsEquiv_chartFrobeniusLiftForms, chartFormsEquiv_chartFrobeniusLiftForms,
    (chartFormsEquiv c b).map_add, Submodule.coe_add, frobeniusLiftExterior_add]

include hann hp2 hK in
/-- **The values of the Deligne–Illusie map are closed sections.** -/
theorem regularFormsDiff_chartFrobeniusLiftForms [Algebra.FiniteType K Γ(X, c.U)]
    (c₀ : EtaleChart K X n) (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ)
    (s : regularFormsSections K b c.U) :
    regularFormsDiff c₀ hcover b c.U (chartFrobeniusLiftForms c π hπ p F hF hker b s) = 0 := by
  apply (chartFormsEquiv c (b + 1)).injective
  rw [chartFormsEquiv_regularFormsDiff, (chartFormsEquiv c (b + 1)).map_zero]
  apply Subtype.ext
  change kaehlerDeRhamDiff c.coords c.formallyEtale
    ((chartFormsEquiv c b (chartFrobeniusLiftForms c π hπ p F hF hker b s) :
      ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K])) = 0
  rw [chartFormsEquiv_chartFrobeniusLiftForms]
  exact frobeniusLiftExterior_closed c.coords c.formallyEtale π hπ p F hF hker hann hp2 hK _

include hann hp2 hK in
/-- **The Cartier isomorphism on the sections over an étale chart**: every closed section of
`Ω^{k+1}_X` is `Φ_F ω + dη`. -/
theorem chart_frobeniusLift_cartier_sections [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)]
    (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0) (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (k : ℕ)
    (z : regularFormsSections K (k + 1) c.U) (hz : regularFormsDiff c₀ hcover (k + 1) c.U z = 0) :
    ∃ ω : regularFormsSections K (k + 1) c.U, ∃ η : regularFormsSections K k c.U,
      z = chartFrobeniusLiftForms c π hπ p F hF hker (k + 1) ω + regularFormsDiff c₀ hcover k c.U η := by
  have hz' : kaehlerDeRhamDiff c.coords c.formallyEtale (chartFormsEquiv c (k + 1) z) = 0 := by
    have h := congrArg (chartFormsEquiv c (k + 1 + 1)) hz
    rw [chartFormsEquiv_regularFormsDiff, (chartFormsEquiv c (k + 1 + 1)).map_zero] at h
    exact congrArg Subtype.val h
  obtain ⟨ω, hω, η, hη, h⟩ := frobeniusLift_cartier_isomorphism_deg c.coords c.formallyEtale p π hπ
    F hF hker hann hp2 hK hy0 (chartFormsEquiv c (k + 1) z) (chartFormsEquiv c (k + 1) z).2 hz'
  set ω' := (chartFormsEquiv c (k + 1)).symm ⟨ω, hω⟩
  set η' := (chartFormsEquiv c k).symm ⟨η, hη⟩
  have he1 : chartFormsEquiv c (k + 1) ω' = ⟨ω, hω⟩ := AddEquiv.apply_symm_apply _ _
  have he2 : chartFormsEquiv c k η' = ⟨η, hη⟩ := AddEquiv.apply_symm_apply _ _
  have h1 : ((chartFormsEquiv c (k + 1) (chartFrobeniusLiftForms c π hπ p F hF hker (k + 1) ω')) :
      ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) =
      frobeniusLiftExterior c.coords c.formallyEtale π hπ p F hF hker ω := by
    rw [chartFormsEquiv_chartFrobeniusLiftForms, he1]
  have h2 : ((chartFormsEquiv c (k + 1) (regularFormsDiff c₀ hcover k c.U η')) :
      ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K]) = kaehlerDeRhamDiff c.coords c.formallyEtale η := by
    rw [chartFormsEquiv_regularFormsDiff]
    change kaehlerDeRhamDiff c.coords c.formallyEtale
      ((chartFormsEquiv c k η' : ExteriorAlgebra Γ(X, c.U) Ω[Γ(X, c.U)⁄K])) = _
    rw [he2]
  refine ⟨ω', η', ?_⟩
  apply (chartFormsEquiv c (k + 1)).injective
  apply Subtype.ext
  rw [(chartFormsEquiv c (k + 1)).map_add, Submodule.coe_add, h1, h2]
  exact sub_eq_iff_eq_add'.mp h

end MixedFujita
