/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DifferentialFormsCharts

/-!
The de Rham differential of `Ω^•_X` (step 10).

The base-change map of `b`-forms along `A → B` (OAI's `exteriorDifferentialMap`) is the restriction
to degree `b` of the map of exterior algebras of check-403 (`exteriorDifferentialMap_coe`).

On a smooth integral scheme `X` over `K` covered by étale charts, the rational forms carry the
intrinsic de Rham differential of `K(X)` (`rationalDeRhamDiff`, defined with the coordinates of a
reference chart and independent of them, check-402), of degree one (`rationalFormsDiff`). It maps
forms regular at a point to forms regular at that point (`rationalFormsDiff_mem_range_stalkFormsMap`):
the local ring has étale coordinates from a chart through the point, and the de Rham differentials
of the local ring and of `K(X)` commute with the map of forms for any choice of coordinates
(check-403). Hence it maps the sections of `Ω^b_X` over a nonempty open subset to those of
`Ω^{b+1}_X` (`regularFormsDiff`), with `d ∘ d = 0` (`regularFormsDiff_comp`). On an étale chart it is
the de Rham differential of `Γ(X, U)` (`chartFormsEquiv_regularFormsDiff`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange

namespace MixedFujita

universe u v w

section BaseChange

variable {K : Type u} [Field K] {A : Type v} [CommRing A] [Algebra K A]
  {B : Type w} [CommRing B] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

/-- **The base change of `b`-forms is the map of exterior algebras in degree `b`.** -/
theorem exteriorDifferentialMap_coe (b : ℕ) (w : ⋀[A]^b Ω[A⁄K]) :
    (exteriorDifferentialMap K K A B b w : ExteriorAlgebra B Ω[B⁄K]) =
      kaehlerExteriorMap K A B w := by
  have key : ((⋀[B]^b Ω[B⁄K]).subtype.restrictScalars A).comp (exteriorDifferentialMap K K A B b) =
      (kaehlerExteriorMap K A B).toLinearMap.comp (⋀[A]^b Ω[A⁄K]).subtype := by
    refine LinearMap.ext_on (exteriorPower.ιMulti_span (R := A) (n := b) (M := Ω[A⁄K])) ?_
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, exteriorDifferentialMap, exteriorScalarMap_wedge]
    simp only [LinearMap.restrictScalars_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    exact (kaehlerExteriorMap_ι (v i)).symm
  exact LinearMap.congr_fun key w

end BaseChange

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

theorem stalkFormsMap_coe (b : ℕ) (x : X) (w : ⋀[X.presheaf.stalk x]^b Ω[X.presheaf.stalk x⁄K]) :
    (stalkFormsMap K b x w : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) =
      kaehlerExteriorMap K (X.presheaf.stalk x) X.functionField w :=
  exteriorDifferentialMap_coe b w

theorem sectionFormsMap_coe (U : X.Opens) [Nonempty U] (b : ℕ) (w : ⋀[Γ(X, U)]^b Ω[Γ(X, U)⁄K]) :
    (sectionFormsMap (K := K) U b w : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) =
      kaehlerExteriorMap K Γ(X, U) X.functionField w :=
  exteriorDifferentialMap_coe b w

/-- **The intrinsic de Rham differential of the rational forms** (with the coordinates of a reference
chart; it does not depend on them, `rationalDeRhamDiff_eq`). -/
noncomputable def rationalDeRhamDiff (c₀ : EtaleChart K X n) :
    ExteriorAlgebra X.functionField Ω[X.functionField⁄K] →ₗ[K]
      ExteriorAlgebra X.functionField Ω[X.functionField⁄K] :=
  kaehlerDeRhamDiff (etaleChartFunctionFieldCoords c₀) (etaleChartFunctionFieldCoords_formallyEtale c₀)

theorem rationalDeRhamDiff_eq (c₀ c₁ : EtaleChart K X n) :
    rationalDeRhamDiff c₀ = rationalDeRhamDiff c₁ :=
  kaehlerDeRhamDiff_eq _ _ _ _

/-- The de Rham differential of rational forms, of degree one. -/
noncomputable def rationalFormsDiff (c₀ : EtaleChart K X n) (b : ℕ) :
    RationalForms K X b →+ RationalForms K X (b + 1) where
  toFun ω := ⟨rationalDeRhamDiff c₀ ω, kaehlerDeRhamDiff_mem_exteriorPower _ _ ω.2⟩
  map_zero' := Subtype.ext (map_zero (rationalDeRhamDiff c₀))
  map_add' ω ω' := Subtype.ext (map_add (rationalDeRhamDiff c₀) (ω : ExteriorAlgebra _ _) ω')

theorem rationalFormsDiff_coe (c₀ : EtaleChart K X n) (b : ℕ) (ω : RationalForms K X b) :
    (rationalFormsDiff c₀ b ω : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) =
      rationalDeRhamDiff c₀ ω := rfl

theorem rationalFormsDiff_comp (c₀ : EtaleChart K X n) (b : ℕ) (ω : RationalForms K X b) :
    rationalFormsDiff c₀ (b + 1) (rationalFormsDiff c₀ b ω) = 0 := by
  apply Subtype.ext
  change rationalDeRhamDiff c₀ (rationalDeRhamDiff c₀ ω) = 0
  exact LinearMap.congr_fun (kaehlerDeRhamDiff_comp_self (etaleChartFunctionFieldCoords c₀)
    (etaleChartFunctionFieldCoords_formallyEtale c₀))
    (ω : ExteriorAlgebra X.functionField Ω[X.functionField⁄K])

/-- **The de Rham differential preserves regularity at a point**: through a chart at the point, the
local ring has étale coordinates, and the differentials commute with the map of forms. -/
theorem rationalFormsDiff_mem_range_stalkFormsMap (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) {b : ℕ} (x : X) (ω : RationalForms K X b)
    (hω : ω ∈ LinearMap.range (stalkFormsMap K b x)) :
    rationalFormsDiff c₀ b ω ∈ LinearMap.range (stalkFormsMap K (b + 1) x) := by
  obtain ⟨c, hxc⟩ : ∃ c : EtaleChart K X n, x ∈ c.U := by
    have hmem : x ∈ iSup (fun c : EtaleChart K X n => c.U) := hcover.symm ▸ Opens.mem_top x
    simpa only [Opens.mem_iSup] using hmem
  obtain ⟨w, hw⟩ := hω
  refine ⟨⟨kaehlerDeRhamDiff (etaleChartStalkCoords c x hxc)
    (etaleChartStalkCoords_formallyEtale c x hxc)
      (w : ExteriorAlgebra (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K]),
    kaehlerDeRhamDiff_mem_exteriorPower _ _ w.2⟩, Subtype.ext ?_⟩
  rw [stalkFormsMap_coe, rationalFormsDiff_coe, ← hw, stalkFormsMap_coe]
  exact (kaehlerDeRhamDiff_comp_exteriorMap _ _ (etaleChartFunctionFieldCoords c₀)
    (etaleChartFunctionFieldCoords_formallyEtale c₀)
    (w : ExteriorAlgebra (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄K])).symm

/-- **The de Rham differential `Γ(U, Ω^b_X) → Γ(U, Ω^{b+1}_X)`** on a nonempty open subset. -/
noncomputable def regularFormsDiff (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) (U : X.Opens) [Nonempty U] :
    regularFormsSections K b U →+ regularFormsSections K (b + 1) U where
  toFun s := ⟨(rationalFormsSectionsEquiv K (b + 1) U).symm
      (rationalFormsDiff c₀ b (regularFormsValue K b U s)), fun x hx => by
    rw [AddEquiv.apply_symm_apply]
    exact rationalFormsDiff_mem_range_stalkFormsMap c₀ hcover x _ (s.2 x hx)⟩
  map_zero' := Subtype.ext (by
    change (rationalFormsSectionsEquiv K (b + 1) U).symm
      (rationalFormsDiff c₀ b (regularFormsValue K b U 0)) = 0
    rw [map_zero, map_zero, map_zero])
  map_add' s t := Subtype.ext (by
    change (rationalFormsSectionsEquiv K (b + 1) U).symm
        (rationalFormsDiff c₀ b (regularFormsValue K b U (s + t))) =
      (rationalFormsSectionsEquiv K (b + 1) U).symm
          (rationalFormsDiff c₀ b (regularFormsValue K b U s)) +
        (rationalFormsSectionsEquiv K (b + 1) U).symm
          (rationalFormsDiff c₀ b (regularFormsValue K b U t))
    rw [map_add, map_add, map_add])

/-- The differential of sections is the differential of their rational values. -/
theorem regularFormsValue_regularFormsDiff (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) (U : X.Opens) [Nonempty U]
    (s : regularFormsSections K b U) :
    regularFormsValue K (b + 1) U (regularFormsDiff c₀ hcover b U s) =
      rationalFormsDiff c₀ b (regularFormsValue K b U s) := by
  exact AddEquiv.apply_symm_apply (rationalFormsSectionsEquiv K (b + 1) U) _

/-- `d ∘ d = 0` on the sections of `Ω^•_X`. -/
theorem regularFormsDiff_comp (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ) (U : X.Opens) [Nonempty U]
    (s : regularFormsSections K b U) :
    regularFormsDiff c₀ hcover (b + 1) U (regularFormsDiff c₀ hcover b U s) = 0 := by
  apply regularFormsValue_injective K (b + 2) U
  rw [regularFormsValue_regularFormsDiff, regularFormsValue_regularFormsDiff, rationalFormsDiff_comp,
    map_zero]

/-- **On an étale chart, the de Rham differential of `Ω^•_X` is the de Rham differential of
`Γ(X, U)`.** -/
theorem chartFormsEquiv_regularFormsDiff (c₀ c : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b : ℕ)
    (s : regularFormsSections K b c.U) :
    chartFormsEquiv c (b + 1) (regularFormsDiff c₀ hcover b c.U s) =
      ⟨kaehlerDeRhamDiff c.coords c.formallyEtale (chartFormsEquiv c b s),
        kaehlerDeRhamDiff_mem_exteriorPower _ _ (chartFormsEquiv c b s).2⟩ := by
  apply sectionFormsMap_injective c (b + 1)
  rw [sectionFormsMap_chartFormsEquiv, regularFormsValue_regularFormsDiff,
    ← sectionFormsMap_chartFormsEquiv]
  apply Subtype.ext
  rw [rationalFormsDiff_coe, sectionFormsMap_coe, sectionFormsMap_coe]
  exact kaehlerDeRhamDiff_comp_exteriorMap _ _ _ _ _

end MixedFujita
