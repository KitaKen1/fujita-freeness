/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedDifferentialForms
public import MixedFujita.DifferentialFormsCharts
public import MixedFujita.SNCBoundaryLocalProduct
public import MixedFujita.CartierSectionBertini

/-!
Logarithmic differential forms along a family of Cartier divisors (step 10, R2).

For Cartier divisors `E_1, …, E_r` on an integral scheme `X` over `K`, the logarithmic `1`-forms
at a point `x` are the `𝒪_{X,x}`-span of the regular `1`-forms and of the logarithmic derivatives
`df / f` of local equations `f` of the `E_k` at `x` (`logOneFormsLattice`). Two local equations
differ by a unit of the local ring, whose logarithmic derivative is regular
(`rationalDlog_stalkUnit_mem`). The logarithmic `b`-forms at `x` are the image of the `b`-th
exterior power of this lattice in the rational `b`-forms (`logFormsLattice`). Both are defined
without coordinates, and regular forms are logarithmic (`range_stalkFormsMap_le_logFormsLattice`).

For a further Cartier divisor `M`, the rational forms `ω` on `U` with `f • ω` logarithmic at every
`x ∈ U` for a local equation `f` of `M` at `x` form a subsheaf of modules of the rational forms,
the sheaf `Ω^b_X(log E)(M)` (`logFormsSheaf`); it contains `Ω^b_X(M)`
(`twistedFormsSections_le_logFormsSections`).

On a simple normal crossing chart `c` at `x` (the `E_k` given by their coefficients along a simple
normal crossing family), a local equation of `E_k` is a unit times the coordinate of `E_k`
(`normal_isSNCChart_boundary_local_product`). So the logarithmic `1`-forms at `x` are the
`𝒪_{X,x}`-span of the logarithmic basis, `dy_j / y_j` in the directions of the family and `dy_j`
otherwise (`logOneFormsLattice_eq_span`). This lattice is free (`logOneFormsLatticeBasis`), and a
rational `b`-form is logarithmic at `x` iff its coefficients in the wedge basis of the
logarithmic basis lie in the local ring (`mem_logFormsLattice_iff`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

variable (K) in
/-- The logarithmic derivative `dg / g` of a nonzero rational function. -/
noncomputable def rationalDlog (g : X.functionFieldˣ) : Ω[X.functionField⁄K] :=
  ((g⁻¹ : X.functionFieldˣ) : X.functionField) •
    KaehlerDifferential.D K X.functionField (g : X.functionField)

theorem rationalDlog_mul (g h : X.functionFieldˣ) :
    rationalDlog K (g * h) = rationalDlog K g + rationalDlog K h := by
  unfold rationalDlog
  have hg := g.ne_zero
  have hh := h.ne_zero
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.val_mul,
    Derivation.leibniz, smul_add, smul_smul, smul_smul,
    show ((g : X.functionField) * h)⁻¹ * g = (h : X.functionField)⁻¹ by field_simp,
    show ((g : X.functionField) * h)⁻¹ * h = (g : X.functionField)⁻¹ by field_simp, add_comm]

theorem rationalDlog_one : rationalDlog K (1 : X.functionFieldˣ) = 0 := by
  unfold rationalDlog
  rw [Units.val_one, Derivation.map_one_eq_zero, smul_zero]

variable (K) in
/-- The regular `1`-forms at `x`, as an `𝒪_{X,x}`-submodule of the rational `1`-forms. -/
noncomputable abbrev regularOneFormsAt (x : X) :
    Submodule (X.presheaf.stalk x) Ω[X.functionField⁄K] :=
  LinearMap.range (KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField)

/-- The image in `K(X)ˣ` of a unit of the local ring. -/
noncomputable abbrev stalkUnitToFunctionField (x : X) (u : (X.presheaf.stalk x)ˣ) :
    X.functionFieldˣ :=
  Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom u

/-- The logarithmic derivative of a unit of the local ring is regular. -/
theorem rationalDlog_stalkUnit_mem (x : X) (u : (X.presheaf.stalk x)ˣ) :
    rationalDlog K (stalkUnitToFunctionField x u) ∈ regularOneFormsAt K x := by
  refine ⟨((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) •
    KaehlerDifferential.D K (X.presheaf.stalk x) (u : X.presheaf.stalk x), ?_⟩
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, rationalDlog,
    ← algebraMap_smul X.functionField]
  rfl

theorem rationalDlog_eq_of_val_eq_mul (x : X) (f g : X.functionFieldˣ) (u : (X.presheaf.stalk x)ˣ)
    (h : (f : X.functionField) = algebraMap _ _ (u : X.presheaf.stalk x) * g) :
    rationalDlog K f = rationalDlog K (stalkUnitToFunctionField x u) + rationalDlog K g := by
  rw [← rationalDlog_mul]
  congr 1
  ext
  rw [h, Units.val_mul]
  rfl

variable (K) in
/-- **The logarithmic `1`-forms at `x` along the divisors `E_k`**: the regular `1`-forms and the
logarithmic derivatives of local equations of the `E_k`. -/
noncomputable def logOneFormsLattice {r : ℕ} (E : Fin r → CartierDivisor X) (x : X) :
    Submodule (X.presheaf.stalk x) Ω[X.functionField⁄K] :=
  regularOneFormsAt K x ⊔ Submodule.span (X.presheaf.stalk x)
    {ω | ∃ (k : Fin r) (f : X.functionFieldˣ), (E k).IsLocalEquationAt x f ∧ ω = rationalDlog K f}

variable (K) in
/-- **The logarithmic `b`-forms at `x`**: the image of the `b`-th exterior power of the
logarithmic `1`-forms. -/
noncomputable def logFormsLattice {r : ℕ} (E : Fin r → CartierDivisor X) (x : X) (b : ℕ) :
    Submodule (X.presheaf.stalk x) (RationalForms K X b) :=
  LinearMap.range (exteriorScalarMap (X.presheaf.stalk x) X.functionField
    (logOneFormsLattice K E x) Ω[X.functionField⁄K] (logOneFormsLattice K E x).subtype b)

/-- **Regular forms are logarithmic.** -/
theorem range_stalkFormsMap_le_logFormsLattice {r : ℕ} (E : Fin r → CartierDivisor X) (x : X)
    (b : ℕ) : LinearMap.range (stalkFormsMap K b x) ≤ logFormsLattice K E x b := by
  rw [LinearMap.range_eq_map, ← exteriorPower.ιMulti_span, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  refine ⟨exteriorPower.ιMulti (X.presheaf.stalk x) b (fun i =>
    ⟨KaehlerDifferential.map K K _ _ (v i), Submodule.mem_sup_left ⟨v i, rfl⟩⟩), ?_⟩
  rw [exteriorScalarMap_wedge]
  change _ = exteriorScalarMap _ _ _ _ _ b (exteriorPower.ιMulti _ b v)
  rw [exteriorScalarMap_wedge]
  rfl

/-- **Logarithmic regularity of `f • ω` does not depend on the local equation `f`.** -/
theorem smul_mem_logFormsLattice_iff_of_isLocalEquationAt {r : ℕ} (E : Fin r → CartierDivisor X)
    {M : CartierDivisor X} {x : X} {f g : X.functionFieldˣ} (hf : M.IsLocalEquationAt x f)
    (hg : M.IsLocalEquationAt x g) {b : ℕ} (ω : RationalForms K X b) :
    (f : X.functionField) • ω ∈ logFormsLattice K E x b ↔
      (g : X.functionField) • ω ∈ logFormsLattice K E x b := by
  obtain ⟨u, hu⟩ := hf.exists_unit_mul_eq hg
  have hu' : algebraMap (X.presheaf.stalk x) X.functionField ↑u⁻¹ * f = g := by
    rw [← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  constructor
  · intro h
    rw [← hu', mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ h
  · intro h
    rw [← hu, mul_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ h

variable (K) in
/-- The rational `b`-forms on `U` that are logarithmic along the `E_k` with poles bounded by `M`. -/
noncomputable def logFormsSections {r : ℕ} (E : Fin r → CartierDivisor X) (M : CartierDivisor X)
    (b : ℕ) (U : X.Opens) : Submodule Γ(X, U) Γ(rationalFormsSheaf K X b, U) where
  carrier := {s | ∀ (x : X) (hx : x ∈ U) (f : X.functionFieldˣ), M.IsLocalEquationAt x f →
    haveI : Nonempty U := ⟨⟨x, hx⟩⟩
    (f : X.functionField) • rationalFormsSectionsEquiv K b U s ∈ logFormsLattice K E x b}
  zero_mem' := by
    intro x hx f _
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  add_mem' := by
    intro s t hs ht x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [map_add, smul_add]
    exact Submodule.add_mem _ (hs x hx f hf) (ht x hx f hf)
  smul_mem' := by
    intro a s hs x hx f hf
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    rw [rationalFormsSectionsEquiv_smul, smul_comm,
      ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := U) hx a, algebraMap_smul]
    exact Submodule.smul_mem _ _ (hs x hx f hf)

/-- One local equation at each point suffices. -/
theorem mem_logFormsSections_iff_exists {r : ℕ} {E : Fin r → CartierDivisor X}
    {M : CartierDivisor X} {b : ℕ} {U : X.Opens} (s : Γ(rationalFormsSheaf K X b, U)) :
    s ∈ logFormsSections K E M b U ↔ ∀ (x : X) (hx : x ∈ U), ∃ f : X.functionFieldˣ,
      M.IsLocalEquationAt x f ∧ haveI : Nonempty U := ⟨⟨x, hx⟩⟩
        (f : X.functionField) • rationalFormsSectionsEquiv K b U s ∈ logFormsLattice K E x b := by
  constructor
  · intro hs x hx
    obtain ⟨f, hf⟩ := M.exists_isLocalEquationAt x
    exact ⟨f, hf, hs x hx f hf⟩
  · intro hs x hx g hg
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf, hmem⟩ := hs x hx
    exact (smul_mem_logFormsLattice_iff_of_isLocalEquationAt E hf hg _).mp hmem

/-- **Forms with poles bounded by `M` are logarithmic with poles bounded by `M`.** -/
theorem twistedFormsSections_le_logFormsSections {r : ℕ} (E : Fin r → CartierDivisor X)
    (M : CartierDivisor X) (b : ℕ) (U : X.Opens) :
    twistedFormsSections K M b U ≤ logFormsSections K E M b U := fun _ hs x hx f hf =>
  range_stalkFormsMap_le_logFormsLattice E x b (hs x hx f hf)

variable (K) in
/-- **The sheaf `Ω^b_X(log E)(M)`** as a subsheaf of modules of the rational `b`-forms. -/
noncomputable def logFormsSubmodule {r : ℕ} (E : Fin r → CartierDivisor X) (M : CartierDivisor X)
    (b : ℕ) : (rationalFormsSheaf K X b).Submodule where
  obj U := logFormsSections K E M b U.unop
  map {U V} i := fun s hs x hx f hf => by
    have : Nonempty V.unop := ⟨⟨x, hx⟩⟩
    have : Nonempty U.unop := ⟨⟨x, i.unop.le hx⟩⟩
    have h := rationalFormsSectionsEquiv_map K b i.unop s
    change (f : X.functionField) • rationalFormsSectionsEquiv K b V.unop
      ((rationalFormsSheaf K X b).presheaf.map i.unop.op s) ∈ _
    rw [h]
    exact hs x (i.unop.le hx) f hf
  isSheaf {U} s hs := by
    intro x hx f hf
    obtain ⟨V, i, hi, hxV⟩ := hs x hx
    have : Nonempty V := ⟨⟨x, hxV⟩⟩
    have : Nonempty U.unop := ⟨⟨x, hx⟩⟩
    have hi' : (rationalFormsSheaf K X b).presheaf.map i.op s ∈ logFormsSections K E M b V := hi
    rw [← rationalFormsSectionsEquiv_map K b i s]
    exact hi' x hxV f hf

variable (K) in
/-- **The sheaf `Ω^b_X(log E)(M)` of `b`-forms logarithmic along the `E_k` with poles bounded by
`M`.** -/
noncomputable def logFormsSheaf {r : ℕ} (E : Fin r → CartierDivisor X) (M : CartierDivisor X)
    (b : ℕ) : X.Modules :=
  (logFormsSubmodule K E M b).toSheafOfModules

section Chart

/-- The weights of the logarithmic basis of a chart: the inverse coordinate in the directions of
the family, one otherwise. -/
noncomputable def logChartWeight (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))
    (j : Fin n) : X.functionFieldˣ :=
  if ∃ k, σ k = some j then (etaleChartCoordinateRationalUnit c j)⁻¹ else 1

/-- **The logarithmic basis of a chart**: `dy_j / y_j` in the directions of the family, `dy_j`
otherwise. -/
noncomputable def logChartBasis (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) :
    Module.Basis (Fin n) X.functionField Ω[X.functionField⁄K] :=
  (etaleChartBasis c).unitsSMul (logChartWeight c σ)

theorem etaleChartBasis_apply_eq (c : EtaleChart K X n) (j : Fin n) :
    etaleChartBasis c j = KaehlerDifferential.D K X.functionField
      (etaleChartCoordinateRationalUnit c j : X.functionField) := by
  rw [etaleChartBasis, etaleCoordinateBasis_apply]
  rfl

theorem logChartBasis_apply_of_mem (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))
    {j : Fin n} (hj : ∃ k, σ k = some j) :
    logChartBasis c σ j = rationalDlog K (etaleChartCoordinateRationalUnit c j) := by
  rw [logChartBasis, Module.Basis.unitsSMul_apply, logChartWeight, ite_eq_left hj,
    etaleChartBasis_apply_eq]
  rfl

theorem logChartBasis_apply_of_not_mem (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) {j : Fin n} (hj : ¬ ∃ k, σ k = some j) :
    logChartBasis c σ j = etaleChartBasis c j := by
  rw [logChartBasis, Module.Basis.unitsSMul_apply, logChartWeight, ite_eq_right hj, one_smul]

theorem etaleChartBasis_mem_regularOneFormsAt (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (j : Fin n) : etaleChartBasis c j ∈ regularOneFormsAt K x :=
  ⟨_, etaleChart_differential_map_basis c x hx j⟩

theorem etaleChartBasis_mem_span_logChartBasis (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (x : X) (hx : x ∈ c.U) (j : Fin n) :
    etaleChartBasis c j ∈
      Submodule.span (X.presheaf.stalk x) (Set.range (logChartBasis c σ)) := by
  by_cases hj : ∃ k, σ k = some j
  · have hne := (etaleChartCoordinateRationalUnit c j).ne_zero
    have h : etaleChartBasis c j =
        (X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X j))) • logChartBasis c σ j := by
      rw [logChartBasis, Module.Basis.unitsSMul_apply, logChartWeight, ite_eq_left hj, Units.smul_def,
        ← algebraMap_smul X.functionField, smul_smul,
        Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := c.U) hx,
        Units.val_inv_eq_inv_val]
      change _ = ((etaleChartCoordinateRationalUnit c j : X.functionField) *
        (etaleChartCoordinateRationalUnit c j : X.functionField)⁻¹) • _
      rw [mul_inv_cancel₀ hne, one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  · rw [← logChartBasis_apply_of_not_mem c σ hj]
    exact Submodule.subset_span ⟨j, rfl⟩

theorem regularOneFormsAt_le_span_logChartBasis (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (x : X) (hx : x ∈ c.U) :
    regularOneFormsAt K x ≤
      Submodule.span (X.presheaf.stalk x) (Set.range (logChartBasis c σ)) := by
  rintro _ ⟨ω, rfl⟩
  rw [← (etaleCoordinateBasis (etaleChartStalkCoords c x hx)
    (etaleChartStalkCoords_formallyEtale c x hx)).sum_repr ω, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [LinearMap.map_smul, etaleChart_differential_map_basis c x hx j]
  exact Submodule.smul_mem _ _ (etaleChartBasis_mem_span_logChartBasis c σ x hx j)

/-- The wedge basis of the logarithmic basis of a chart. -/
noncomputable abbrev logChartFormsBasis (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (b : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) b) X.functionField (RationalForms K X b) :=
  (logChartBasis c σ).exteriorPower b

theorem logChartBasis_linearIndependent (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (x : X) :
    LinearIndependent (X.presheaf.stalk x) (logChartBasis c σ) :=
  (logChartBasis c σ).linearIndependent.restrict_scalars (by
    intro a b h
    simp only [Algebra.smul_def, mul_one] at h
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField h)

section SNC

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)

include hnorm hinj hξ hEc hc in
/-- On a simple normal crossing chart, a local equation of `E_k` is a unit times the coordinate
of `E_k`. -/
theorem exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation (x : X) (hx : x ∈ c.U)
    (k : Fin r) :
    ∃ (f : X.functionFieldˣ) (_ : (E k).IsLocalEquationAt x f) (u : (X.presheaf.stalk x)ˣ),
      (f : X.functionField) = algebraMap _ _ (u : X.presheaf.stalk x) *
        (sncChartComponentEquation c σ k : X.functionField) := by
  have hsupp : ∀ z : CodimensionOnePoint X, (z : X) ∉ Set.range ξ →
      cartierCoefficient (E k) (z : X) = 0 := fun z hz => by
    rw [hEc k z, ite_eq_right (fun h => hz ⟨k, h.symm⟩)]
  obtain ⟨f, hf, u, hu⟩ := normal_isSNCChart_boundary_local_product hnorm (E k) c ξ hinj hξ σ hc
    hsupp x hx
  have hprod : (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient (E k) (ξ i)) =
      sncChartComponentEquation c σ k := by
    rw [Finset.prod_eq_single k]
    · rw [hEc k ⟨ξ k, hξ k⟩, ite_eq_left rfl, zpow_one]
    · intro i _ hik
      rw [hEc k ⟨ξ i, hξ i⟩, ite_eq_right (fun h => hik (hinj h)), zpow_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  refine ⟨f, hf, u, ?_⟩
  rw [hu, hprod]

include hnorm hinj hξ hEc hc in
/-- **On a simple normal crossing chart the logarithmic `1`-forms are spanned by the logarithmic
basis.** -/
theorem logOneFormsLattice_eq_span (x : X) (hx : x ∈ c.U) :
    logOneFormsLattice K E x =
      Submodule.span (X.presheaf.stalk x) (Set.range (logChartBasis c σ)) := by
  apply le_antisymm
  · refine sup_le (regularOneFormsAt_le_span_logChartBasis c σ x hx) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, f, hf, rfl⟩
    obtain ⟨f', hf', u, hu⟩ := exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation
      hnorm ξ hinj hξ E hEc c σ hc x hx k
    obtain ⟨v, hv⟩ := hf.exists_unit_mul_eq hf'
    rw [SetLike.mem_coe, rationalDlog_eq_of_val_eq_mul (K := K) x f f' v hv.symm,
      rationalDlog_eq_of_val_eq_mul (K := K) x f' (sncChartComponentEquation c σ k) u hu]
    refine Submodule.add_mem _ (regularOneFormsAt_le_span_logChartBasis c σ x hx
      (rationalDlog_stalkUnit_mem x v)) (Submodule.add_mem _
        (regularOneFormsAt_le_span_logChartBasis c σ x hx (rationalDlog_stalkUnit_mem x u)) ?_)
    cases hσ : σ k with
    | none =>
      rw [sncChartComponentEquation, hσ, Option.elim_none, rationalDlog_one]
      exact Submodule.zero_mem _
    | some a =>
      rw [sncChartComponentEquation, hσ, Option.elim_some,
        ← logChartBasis_apply_of_mem c σ ⟨k, hσ⟩]
      exact Submodule.subset_span ⟨a, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe]
    unfold logOneFormsLattice
    by_cases hj : ∃ k, σ k = some j
    · obtain ⟨k, hk⟩ := hj
      obtain ⟨f, hf, u, hu⟩ := exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation
        hnorm ξ hinj hξ E hEc c σ hc x hx k
      have hsnc : sncChartComponentEquation c σ k = etaleChartCoordinateRationalUnit c j := by
        rw [sncChartComponentEquation, hk, Option.elim_some]
      have h := rationalDlog_eq_of_val_eq_mul (K := K) x f _ u hu
      rw [hsnc] at h
      rw [logChartBasis_apply_of_mem c σ ⟨k, hk⟩,
        show rationalDlog K (etaleChartCoordinateRationalUnit c j) =
          rationalDlog K f - rationalDlog K (stalkUnitToFunctionField x u) by rw [h]; abel]
      exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span ⟨k, f, hf, rfl⟩))
        (Submodule.mem_sup_left (rationalDlog_stalkUnit_mem x u))
    · rw [logChartBasis_apply_of_not_mem c σ hj]
      exact Submodule.mem_sup_left (etaleChartBasis_mem_regularOneFormsAt c x hx j)

include hnorm hinj hξ hEc hc in
/-- **The logarithmic basis of a simple normal crossing chart is an `𝒪_{X,x}`-basis of the
logarithmic `1`-forms.** -/
noncomputable def logOneFormsLatticeBasis (x : X) (hx : x ∈ c.U) :
    Module.Basis (Fin n) (X.presheaf.stalk x) (logOneFormsLattice K E x) :=
  (Module.Basis.span (logChartBasis_linearIndependent c σ x)).map
    (LinearEquiv.ofEq _ _ (logOneFormsLattice_eq_span hnorm ξ hinj hξ E hEc c σ hc x hx).symm)

theorem logOneFormsLatticeBasis_apply (x : X) (hx : x ∈ c.U) (j : Fin n) :
    ((logOneFormsLatticeBasis (K := K) hnorm ξ hinj hξ E hEc c σ hc x hx j :
      logOneFormsLattice K E x) : Ω[X.functionField⁄K]) = logChartBasis c σ j := by
  rw [logOneFormsLatticeBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.span_apply]

include hnorm hinj hξ hEc hc in
/-- **A rational `b`-form is logarithmic at a point of a simple normal crossing chart iff its
coefficients in the logarithmic wedge basis lie in the local ring.** -/
theorem mem_logFormsLattice_iff (x : X) (hx : x ∈ c.U) (b : ℕ) (ω : RationalForms K X b) :
    ω ∈ logFormsLattice K E x b ↔
      ∀ s, (logChartFormsBasis c σ b).repr ω s ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range :=
  mem_range_iff_of_map_basis
    ((logOneFormsLatticeBasis hnorm ξ hinj hξ E hEc c σ hc x hx).exteriorPower b)
    (logChartFormsBasis c σ b) _
    (exteriorScalarMap_basis _ _ _
      (logOneFormsLatticeBasis_apply hnorm ξ hinj hξ E hEc c σ hc x hx) b) ω

end SNC

end Chart

end MixedFujita
