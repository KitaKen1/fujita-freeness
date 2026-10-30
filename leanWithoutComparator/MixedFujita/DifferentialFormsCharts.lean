/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DifferentialFormsSheaf
public import MixedFujita.CanonicalCartierTopForms

/-!
Sections of `Ω^b_X` on étale charts (step 10).

A linear map sending a basis to a basis maps coefficients by the algebra map
(`basis_repr_apply_of_map_basis`), so its range consists of the vectors whose coefficients come from
the smaller ring (`mem_range_iff_of_map_basis`), and it is injective when the algebra map is
(`injective_of_map_basis`). This applies to exterior powers (`exteriorScalarMap_basis`).

On an étale chart `c` of an integral scheme `X` over `K`, the coordinates give bases of the
`b`-forms of `Γ(X, U)`, of the local rings at the points of `U` and of `K(X)`, indexed by the
`b`-element subsets of the coordinates, and the maps of forms send basis to basis. Hence a rational
form is regular at a point of `U` iff its coefficients lie in the local ring
(`mem_range_stalkFormsMap_iff`). As `Γ(X, U)` is the intersection of the local rings in `K(X)`, a
rational form is regular at every point of `U` iff it is a form on `U`
(`forall_mem_range_stalkFormsMap_iff`). So the sections of `Ω^b_X` over `U` are the `b`-forms of
`Γ(X, U)` (`chartFormsLinearEquiv`, `Γ(X, U)`-linearly), a free module with the wedge basis of the
coordinates (`chartSectionsBasis`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange

namespace MixedFujita

universe u

section BasisMap

variable {A L M N : Type*} [CommRing A] [CommRing L] [Algebra A L]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module L N] [IsScalarTower A L N]
  {ι : Type*} (B : Module.Basis ι A M) (C : Module.Basis ι L N) (f : M →ₗ[A] N)
  (hf : ∀ i, f (B i) = C i)
include hf

/-- A linear map sending a basis to a basis maps coefficients by the algebra map. -/
theorem basis_repr_apply_of_map_basis (m : M) (i : ι) :
    C.repr (f m) i = algebraMap A L (B.repr m i) := by
  have h : ((C.coord i).restrictScalars A).comp f = (Algebra.linearMap A L).comp (B.coord i) := by
    refine B.ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, hf,
      Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Module.Basis.repr_self, Algebra.linearMap_apply]
    by_cases hji : j = i
    · subst hji
      simp
    · simp [hji]
  exact LinearMap.congr_fun h m

theorem mem_range_of_map_basis [Fintype ι] {y : N}
    (hy : ∀ i, C.repr y i ∈ (algebraMap A L).range) : y ∈ LinearMap.range f := by
  have hy' : ∀ i, ∃ a, algebraMap A L a = C.repr y i := fun i => RingHom.mem_range.mp (hy i)
  choose a ha using hy'
  refine ⟨∑ i, a i • B i, ?_⟩
  rw [map_sum]
  conv_rhs => rw [← C.sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hf, ← ha i, algebraMap_smul]

/-- **The range of a map sending a basis to a basis**: the vectors with coefficients from the
smaller ring. -/
theorem mem_range_iff_of_map_basis [Fintype ι] (y : N) :
    y ∈ LinearMap.range f ↔ ∀ i, C.repr y i ∈ (algebraMap A L).range := by
  refine ⟨?_, mem_range_of_map_basis B C f hf⟩
  rintro ⟨m, rfl⟩ i
  exact ⟨B.repr m i, (basis_repr_apply_of_map_basis B C f hf m i).symm⟩

theorem injective_of_map_basis (hA : Function.Injective (algebraMap A L)) :
    Function.Injective f := by
  intro m m' h
  refine B.repr.injective (Finsupp.ext fun i => hA ?_)
  rw [← basis_repr_apply_of_map_basis B C f hf, ← basis_repr_apply_of_map_basis B C f hf, h]

end BasisMap

section ExteriorBasisMap

variable {A L M N : Type*} [CommRing A] [CommRing L] [Algebra A L]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module L N] [IsScalarTower A L N]
  {ι : Type*} [LinearOrder ι] (B : Module.Basis ι A M) (C : Module.Basis ι L N) (f : M →ₗ[A] N)
  (hf : ∀ i, f (B i) = C i)
include hf

/-- The map of exterior powers sends the wedge basis to the wedge basis. -/
theorem exteriorScalarMap_basis (b : ℕ) (s : Set.powersetCard ι b) :
    exteriorScalarMap A L M N f b (B.exteriorPower b s) = C.exteriorPower b s := by
  simp only [exteriorPower.coe_basis, exteriorPower.ιMulti_family, exteriorScalarMap_wedge]
  congr 1
  funext j
  exact hf _

end ExteriorBasisMap

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The wedge basis of the rational `b`-forms given by an étale chart. -/
noncomputable abbrev chartFormsBasis (c : EtaleChart K X n) (b : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) b) X.functionField (RationalForms K X b) :=
  (etaleChartBasis c).exteriorPower b

/-- **Regularity at a point of a chart is regularity of the coefficients.** -/
theorem mem_range_stalkFormsMap_iff (c : EtaleChart K X n) (b : ℕ) (x : X) (hx : x ∈ c.U)
    (ω : RationalForms K X b) :
    ω ∈ LinearMap.range (stalkFormsMap K b x) ↔
      ∀ s, (chartFormsBasis c b).repr ω s ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  have hf : ∀ s, stalkFormsMap K b x ((etaleCoordinateBasis (etaleChartStalkCoords c x hx)
      (etaleChartStalkCoords_formallyEtale c x hx)).exteriorPower b s) = chartFormsBasis c b s :=
    exteriorScalarMap_basis _ _ _ (etaleChart_differential_map_basis c x hx) b
  exact mem_range_iff_of_map_basis _ (chartFormsBasis c b) _ hf ω

/-- The map from the `b`-forms on a nonempty open subset to the rational `b`-forms. -/
noncomputable abbrev sectionFormsMap (U : X.Opens) [Nonempty U] (b : ℕ) :
    ⋀[Γ(X, U)]^b Ω[Γ(X, U)⁄K] →ₗ[Γ(X, U)] RationalForms K X b :=
  exteriorDifferentialMap K K Γ(X, U) X.functionField b

theorem sectionFormsMap_basis (c : EtaleChart K X n) (b : ℕ) (s : Set.powersetCard (Fin n) b) :
    sectionFormsMap (K := K) c.U b
        ((etaleCoordinateBasis c.coords c.formallyEtale).exteriorPower b s) =
      chartFormsBasis c b s :=
  exteriorScalarMap_basis _ _ _ (etaleChart_open_differential_map_basis c) b s

theorem sectionFormsMap_injective (c : EtaleChart K X n) (b : ℕ) :
    Function.Injective (sectionFormsMap (K := K) c.U b) :=
  injective_of_map_basis _ (chartFormsBasis c b) _ (sectionFormsMap_basis c b)
    (Scheme.germToFunctionField_injective X c.U)

theorem mem_range_sectionFormsMap_iff (c : EtaleChart K X n) (b : ℕ) (ω : RationalForms K X b) :
    ω ∈ LinearMap.range (sectionFormsMap (K := K) c.U b) ↔
      ∀ s, (chartFormsBasis c b).repr ω s ∈ (algebraMap Γ(X, c.U) X.functionField).range :=
  mem_range_iff_of_map_basis _ (chartFormsBasis c b) _ (sectionFormsMap_basis c b) ω

/-- **On an étale chart, a rational form is regular at every point iff it is a form of the
chart**: `Γ(X, U)` is the intersection of the local rings at the points of `U`. -/
theorem forall_mem_range_stalkFormsMap_iff (c : EtaleChart K X n) (b : ℕ)
    (ω : RationalForms K X b) :
    (∀ (x : X) (_ : x ∈ c.U), ω ∈ LinearMap.range (stalkFormsMap K b x)) ↔
      ω ∈ LinearMap.range (sectionFormsMap (K := K) c.U b) := by
  rw [mem_range_sectionFormsMap_iff]
  constructor
  · intro h s
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range (U := c.U)
      (f := (chartFormsBasis c b).repr ω s)
      fun y hy => (mem_range_stalkFormsMap_iff c b y hy ω).mp (h y hy) s
    exact ⟨a, ha⟩
  · intro h x hx
    rw [mem_range_stalkFormsMap_iff c b x hx]
    intro s
    obtain ⟨a, ha⟩ := h s
    refine ⟨X.presheaf.germ c.U x hx a, ?_⟩
    rw [← ha]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := c.U) hx a

/-- On an étale chart, the values of the sections of `Ω^b_X` are the forms of the chart. -/
theorem exists_regularFormsValue_eq_iff_chart (c : EtaleChart K X n) (b : ℕ)
    (ω : RationalForms K X b) :
    (∃ s, regularFormsValue K b c.U s = ω) ↔
      ω ∈ LinearMap.range (sectionFormsMap (K := K) c.U b) := by
  rw [exists_regularFormsValue_eq_iff, forall_mem_range_stalkFormsMap_iff]

theorem range_regularFormsValue_chart (c : EtaleChart K X n) (b : ℕ) :
    (regularFormsValue K b c.U).range =
      (LinearMap.range (sectionFormsMap (K := K) c.U b)).toAddSubgroup := by
  ext ω
  rw [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup]
  exact exists_regularFormsValue_eq_iff_chart c b ω

/-- The sections of `Ω^b_X` over an étale chart are the `b`-forms of the chart (additively). -/
noncomputable def chartFormsEquiv (c : EtaleChart K X n) (b : ℕ) :
    regularFormsSections K b c.U ≃+ ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K] :=
  ((AddMonoidHom.ofInjective (regularFormsValue_injective K b c.U)).trans
    (AddEquiv.addSubgroupCongr (range_regularFormsValue_chart c b))).trans
    (LinearEquiv.ofInjective _ (sectionFormsMap_injective c b)).symm.toAddEquiv

/-- The equivalence is normalized by the rational form. -/
theorem sectionFormsMap_chartFormsEquiv (c : EtaleChart K X n) (b : ℕ)
    (s : regularFormsSections K b c.U) :
    sectionFormsMap (K := K) c.U b (chartFormsEquiv c b s) = regularFormsValue K b c.U s := by
  change sectionFormsMap c.U b ((LinearEquiv.ofInjective _ (sectionFormsMap_injective c b)).symm
    ⟨regularFormsValue K b c.U s, _⟩) = _
  rw [LinearEquiv.ofInjective_symm_apply]

/-- **The sections of `Ω^b_X` over an étale chart are the `b`-forms of the chart**,
`Γ(X, U)`-linearly. -/
noncomputable def chartFormsLinearEquiv (c : EtaleChart K X n) (b : ℕ) :
    regularFormsSections K b c.U ≃ₗ[Γ(X, c.U)] ⋀[Γ(X, c.U)]^b Ω[Γ(X, c.U)⁄K] :=
  { chartFormsEquiv c b with
    map_smul' := fun r s => by
      apply sectionFormsMap_injective c b
      change sectionFormsMap c.U b (chartFormsEquiv c b (r • s)) =
        sectionFormsMap c.U b (r • chartFormsEquiv c b s)
      rw [sectionFormsMap_chartFormsEquiv, map_smul (sectionFormsMap c.U b) r (chartFormsEquiv c b s),
        sectionFormsMap_chartFormsEquiv, regularFormsValue_apply, regularFormsValue_apply,
        Submodule.coe_smul, rationalFormsSectionsEquiv_smul, ← algebraMap_smul X.functionField r]
      rfl }

theorem chartFormsLinearEquiv_apply (c : EtaleChart K X n) (b : ℕ)
    (s : regularFormsSections K b c.U) :
    chartFormsLinearEquiv c b s = chartFormsEquiv c b s := rfl

/-- **The sections of `Ω^b_X` over an étale chart form a free module**, with the wedge basis of the
coordinates. -/
noncomputable def chartSectionsBasis (c : EtaleChart K X n) (b : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) b) Γ(X, c.U) (regularFormsSections K b c.U) :=
  ((etaleCoordinateBasis c.coords c.formallyEtale).exteriorPower b).map
    (chartFormsLinearEquiv c b).symm

theorem regularFormsValue_chartSectionsBasis (c : EtaleChart K X n) (b : ℕ)
    (s : Set.powersetCard (Fin n) b) :
    regularFormsValue K b c.U (chartSectionsBasis c b s) = chartFormsBasis c b s := by
  rw [← sectionFormsMap_chartFormsEquiv, chartSectionsBasis, Module.Basis.map_apply,
    ← chartFormsLinearEquiv_apply, LinearEquiv.apply_symm_apply, sectionFormsMap_basis]

end MixedFujita
