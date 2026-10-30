/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleCoordinateDifferentials
public import MixedFujita.RegularEquationCartier
public import MixedFujita.SmoothSchemeCoordinates
public import TauCeti.AlgebraicGeometry.Modules.RationalFunctions
public import MixedFujita.SmoothRelativeCoordinates

/-!
The canonical divisor K_X of a smooth integral scheme over a field, from étale charts (step 1).
An étale chart is a nonempty affine open U with formally étale coordinates x : K[X_1, …, X_n] → Γ(U).
Through the germ to the function field these give a basis d x_1, …, d x_n of Ω[K(X)/K]. Fix a
reference chart c₀ and let ω₀ = d x^(c₀)_1 ∧ ⋯ ∧ d x^(c₀)_n. On a chart c, ω₀ = g_c · d x^(c)_1 ∧ ⋯ ∧
d x^(c)_n with g_c the determinant of the basis of c₀ in the basis of c. For two charts the ratio
g_c / g_c' is the Jacobian determinant of c' with respect to c; at every point p of the overlap both
coordinate systems are formally étale on the stalk, so this determinant is the image of a unit of
the stalk, and therefore of a unit of the sections over the overlap. Hence the g_c glue to a
Cartier divisor, K_X = div(ω₀), whose local equation on every chart c is g_c. A different
reference chart changes K_X by the principal divisor of a determinant.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra cartierBaseLocalAlgebra
  cartierBaseOpenAlgebra

/-- The K-algebra structure on the function field, through the global sections. -/
@[instance_reducible]
noncomputable def functionFieldBaseAlgebra (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] : Algebra K X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp (Scheme.Modules.baseRingToGlobalSections K X)).toAlgebra

attribute [local instance] functionFieldBaseAlgebra

/-- The germ of a section over a nonempty open, as a K-algebra map to the function field. -/
noncomputable def sectionGermAlgHom (U : X.Opens) [Nonempty U] : Γ(X, U) →ₐ[K] X.functionField where
  toRingHom := (X.germToFunctionField U).hom
  commutes' k := by
    dsimp [Algebra.algebraMap, cartierBaseOpenAlgebra, functionFieldBaseAlgebra,
      RingHom.toAlgebra]
    rw [Scheme.baseRingToStructurePresheaf_app]
    change (X.germToFunctionField U) ((X.presheaf.map U.leTop.op)
      (Scheme.Modules.baseRingToGlobalSections K X k)) =
        (X.germToFunctionField ⊤) (Scheme.Modules.baseRingToGlobalSections K X k)
    exact TopCat.Presheaf.germ_res_apply X.presheaf U.leTop _ _ _

theorem sectionGermAlgHom_formallyEtale (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (sectionGermAlgHom (K := K) U).toRingHom.FormallyEtale := by
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have : Algebra.FormallyEtale Γ(X, U) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(X, U))
  exact RingHom.formallyEtale_algebraMap.mpr this

/-- The map from a stalk to the function field, as a K-algebra map. -/
noncomputable def stalkFunctionFieldAlgHom (x : X) : X.presheaf.stalk x →ₐ[K] X.functionField where
  toRingHom := algebraMap (X.presheaf.stalk x) X.functionField
  commutes' k := by
    dsimp [Algebra.algebraMap, cartierBaseLocalAlgebra, cartierGlobalStalkAlgebra,
      functionFieldBaseAlgebra, RingHom.toAlgebra]
    change algebraMap (X.presheaf.stalk x) X.functionField
        (X.presheaf.germ ⊤ x (Opens.mem_top x) (Scheme.Modules.baseRingToGlobalSections K X k)) =
      (X.germToFunctionField ⊤) (Scheme.Modules.baseRingToGlobalSections K X k)
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := (⊤ : X.Opens))
      (Opens.mem_top x) _

theorem stalkFunctionFieldAlgHom_formallyEtale (x : X) :
    (stalkFunctionFieldAlgHom (K := K) x).toRingHom.FormallyEtale := by
  have : Algebra.FormallyEtale (X.presheaf.stalk x) X.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (X.presheaf.stalk x))
  exact RingHom.formallyEtale_algebraMap.mpr this

/-- The germ from sections over an open to the stalk at one of its points, as a K-algebra map. -/
noncomputable def sectionStalkAlgHom (U : X.Opens) (x : X) (hx : x ∈ U) :
    Γ(X, U) →ₐ[K] X.presheaf.stalk x := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  letI := cartierBaseOpenLocalScalarTower (K := K) x hx
  exact IsScalarTower.toAlgHom K Γ(X, U) (X.presheaf.stalk x)

omit [IsIntegral X] in
theorem sectionStalkAlgHom_apply (U : X.Opens) (x : X) (hx : x ∈ U) (s : Γ(X, U)) :
    sectionStalkAlgHom (K := K) U x hx s = X.presheaf.germ U x hx s :=
  rfl

omit [IsIntegral X] in
theorem sectionStalkAlgHom_formallyEtale (U : X.Opens) (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) : (sectionStalkAlgHom (K := K) U x hx).toRingHom.FormallyEtale := by
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : U)
  have := hU.isLocalization_stalk (⟨x, hx⟩ : U)
  have : Algebra.FormallyEtale Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact RingHom.formallyEtale_algebraMap.mpr this

/-- An étale chart: a nonempty affine open with formally étale coordinates. -/
structure EtaleChart (K : Type u) [Field K] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))]
    (n : ℕ) where
  /-- The open subset. -/
  U : X.Opens
  isAffine : IsAffineOpen U
  nonempty : Nonempty U
  /-- The coordinates. -/
  coords : MvPolynomial (Fin n) K →ₐ[K] Γ(X, U)
  formallyEtale : coords.toRingHom.FormallyEtale

variable {n : ℕ}

instance etaleChartNonempty (c : EtaleChart K X n) : Nonempty c.U := c.nonempty

/-- The coordinates of the chart in the function field. -/
noncomputable def etaleChartFunctionFieldCoords (c : EtaleChart K X n) :
    MvPolynomial (Fin n) K →ₐ[K] X.functionField :=
  (sectionGermAlgHom c.U).comp c.coords

theorem etaleChartFunctionFieldCoords_formallyEtale (c : EtaleChart K X n) :
    (etaleChartFunctionFieldCoords c).toRingHom.FormallyEtale :=
  formallyEtale_comp _ (sectionGermAlgHom_formallyEtale c.U c.isAffine) _ c.formallyEtale

/-- The basis d x_1, …, d x_n of Ω[K(X)/K] given by the chart. -/
noncomputable def etaleChartBasis (c : EtaleChart K X n) :
    Module.Basis (Fin n) X.functionField Ω[X.functionField⁄K] :=
  etaleCoordinateBasis (etaleChartFunctionFieldCoords c) (etaleChartFunctionFieldCoords_formallyEtale c)

/-- The coordinates of the chart in the stalk at a point of the chart. -/
noncomputable def etaleChartStalkCoords (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) :
    MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x :=
  (sectionStalkAlgHom c.U x hx).comp c.coords

omit [IsIntegral X] in
theorem etaleChartStalkCoords_formallyEtale (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) :
    (etaleChartStalkCoords c x hx).toRingHom.FormallyEtale :=
  formallyEtale_comp _ (sectionStalkAlgHom_formallyEtale c.U c.isAffine x hx) _ c.formallyEtale

theorem etaleChart_stalkFunctionField_comp_stalkCoords (c : EtaleChart K X n) (x : X)
    (hx : x ∈ c.U) :
    (stalkFunctionFieldAlgHom (K := K) x).comp (etaleChartStalkCoords c x hx) =
      etaleChartFunctionFieldCoords c := by
  apply AlgHom.ext
  intro p
  change algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ c.U x hx (c.coords p)) =
    X.germToFunctionField c.U (c.coords p)
  exact Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := c.U) hx _


/-- The Jacobian determinant of c' with respect to c, at a point of the overlap, is the image of a
unit of the stalk. -/
theorem etaleChart_basis_det_eq_stalk (c c' : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (hx' : x ∈ c'.U) :
    (etaleChartBasis c).det (etaleChartBasis c') = stalkFunctionFieldAlgHom (K := K) x
      ((etaleCoordinateBasis (etaleChartStalkCoords c x hx) (etaleChartStalkCoords_formallyEtale c x hx)).det
        (etaleCoordinateBasis (etaleChartStalkCoords c' x hx') (etaleChartStalkCoords_formallyEtale c' x hx'))) := by
  rw [← etaleCoordinateBasis_det_comp (stalkFunctionFieldAlgHom (K := K) x)
    (stalkFunctionFieldAlgHom_formallyEtale (K := K) x)]
  have h1 : (etaleChartBasis c) = etaleCoordinateBasis ((stalkFunctionFieldAlgHom (K := K) x).comp (etaleChartStalkCoords c x hx))
      (formallyEtale_comp _ (stalkFunctionFieldAlgHom_formallyEtale (K := K) x) _
        (etaleChartStalkCoords_formallyEtale c x hx)) := by
    unfold etaleChartBasis
    congr 1
    exact (etaleChart_stalkFunctionField_comp_stalkCoords c x hx).symm
  have h2 : (etaleChartBasis c') = etaleCoordinateBasis ((stalkFunctionFieldAlgHom (K := K) x).comp
      (etaleChartStalkCoords c' x hx')) (formallyEtale_comp _ (stalkFunctionFieldAlgHom_formallyEtale (K := K) x) _
        (etaleChartStalkCoords_formallyEtale c' x hx')) := by
    unfold etaleChartBasis
    congr 1
    exact (etaleChart_stalkFunctionField_comp_stalkCoords c' x hx').symm
  rw [h1, h2]

/-- The Jacobian determinant of c' with respect to c is the germ of a unit over the overlap. -/
theorem etaleChart_exists_unit_basis_det (c c' : EtaleChart K X n) :
    letI := integral_opens_inter_nonempty X c.U c'.U
    ∃ w : Γ(X, c.U ⊓ c'.U)ˣ,
      (Units.map (X.germToFunctionField (c.U ⊓ c'.U)).hom.toMonoidHom w : X.functionFieldˣ) =
        (Module.Basis.isUnit_det (etaleChartBasis c) (etaleChartBasis c')).unit := by
  let _ := integral_opens_inter_nonempty X c.U c'.U
  set d := (etaleChartBasis c).det (etaleChartBasis c') with hd
  have hdu : IsUnit d := Module.Basis.isUnit_det _ _
  -- d and its inverse are regular at every point of the overlap
  have hreg : ∀ f : X.functionField, (∀ x (hx : x ∈ c.U) (hx' : x ∈ c'.U),
      ∃ u : (X.presheaf.stalk x)ˣ, f = stalkFunctionFieldAlgHom (K := K) x u ∨
        f = stalkFunctionFieldAlgHom (K := K) x ↑u⁻¹) → ∀ y ∈ c.U ⊓ c'.U,
      f ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
    intro f hf y hy
    obtain ⟨u, hu⟩ := hf y hy.1 hy.2
    rcases hu with hu | hu
    · exact ⟨u, hu.symm⟩
    · exact ⟨↑u⁻¹, hu.symm⟩
  have hstalk : ∀ x (hx : x ∈ c.U) (hx' : x ∈ c'.U), ∃ u : (X.presheaf.stalk x)ˣ,
      d = stalkFunctionFieldAlgHom (K := K) x u := by
    intro x hx hx'
    refine ⟨(Module.Basis.isUnit_det
      (etaleCoordinateBasis (etaleChartStalkCoords c x hx) (etaleChartStalkCoords_formallyEtale c x hx))
      (etaleCoordinateBasis (etaleChartStalkCoords c' x hx') (etaleChartStalkCoords_formallyEtale c' x hx'))).unit, ?_⟩
    rw [IsUnit.unit_spec]
    exact etaleChart_basis_det_eq_stalk c c' x hx hx'
  obtain ⟨s, hs⟩ := TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range
    (U := c.U ⊓ c'.U) (f := d) (hreg d fun x hx hx' => by
      obtain ⟨u, hu⟩ := hstalk x hx hx'
      exact ⟨u, Or.inl hu⟩)
  obtain ⟨s', hs'⟩ := TauCeti.AlgebraicGeometry.Scheme.exists_germToFunctionField_eq_of_forall_mem_range
    (U := c.U ⊓ c'.U) (f := d⁻¹) (hreg d⁻¹ fun x hx hx' => by
      obtain ⟨u, hu⟩ := hstalk x hx hx'
      refine ⟨u, Or.inr ?_⟩
      rw [hu, map_units_inv])
  have hd0 : d ≠ 0 := hdu.ne_zero
  have hss' : s * s' = 1 := by
    apply Scheme.germToFunctionField_injective X (c.U ⊓ c'.U)
    rw [map_mul, map_one, hs, hs', mul_inv_cancel₀ hd0]
  refine ⟨⟨s, s', hss', by rw [mul_comm]; exact hss'⟩, ?_⟩
  apply Units.ext
  rw [Units.coe_map, IsUnit.unit_spec]
  exact hs

/-- The local equation of K_X on the chart c: the determinant of the reference basis in the basis
of c, so that ω₀ = g_c · d x^(c)_1 ∧ ⋯ ∧ d x^(c)_n. -/
noncomputable def etaleChartCanonicalEquation (c₀ c : EtaleChart K X n) : X.functionFieldˣ :=
  (Module.Basis.isUnit_det (etaleChartBasis c) (etaleChartBasis c₀)).unit

theorem etaleChartCanonicalEquation_val (c₀ c : EtaleChart K X n) :
    (etaleChartCanonicalEquation c₀ c : X.functionField) = (etaleChartBasis c).det (etaleChartBasis c₀) :=
  IsUnit.unit_spec _

/-- The chart equations differ by units of the sections over the overlaps. -/
theorem etaleChartCanonicalEquation_transition (c₀ c c' : EtaleChart K X n) :
    letI := integral_opens_inter_nonempty X c.U c'.U
    ∃ w : Γ(X, c.U ⊓ c'.U)ˣ,
      etaleChartCanonicalEquation c₀ c = Units.map (X.germToFunctionField (c.U ⊓ c'.U)).hom w *
        etaleChartCanonicalEquation c₀ c' := by
  let _ := integral_opens_inter_nonempty X c.U c'.U
  obtain ⟨w, hw⟩ := etaleChart_exists_unit_basis_det c c'
  refine ⟨w, ?_⟩
  apply Units.ext
  have hw' := congrArg Units.val hw
  rw [IsUnit.unit_spec] at hw'
  rw [Units.val_mul, etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val,
    ← Module.Basis.det_mul_det (etaleChartBasis c) (etaleChartBasis c') (etaleChartBasis c₀)]
  congr 1
  rw [← hw']
  rfl

variable (n) in
/-- The canonical divisor K_X = div(ω₀), glued from the chart equations, when étale charts cover X.
-/
noncomputable def canonicalDivisor (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) : CartierDivisor X :=
  (cartierDivisor_existsUnique_of_rationalUnits X (fun c : EtaleChart K X n => c.U) hcover
    (fun c => etaleChartCanonicalEquation c₀ c) (fun c c' => etaleChartCanonicalEquation_transition c₀ c c')).exists.choose

/-- On every chart c, K_X is the class of the chart equation g_c. -/
theorem canonicalDivisor_restrict (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c : EtaleChart K X n) :
    (cartierDivisorSheaf X).1.map (homOfLE (show c.U ≤ ⊤ from le_top)).op
        (canonicalDivisor n c₀ hcover) =
      rationalUnitClass X c.U (Additive.ofMul (etaleChartCanonicalEquation c₀ c)) :=
  (cartierDivisor_existsUnique_of_rationalUnits X (fun c : EtaleChart K X n => c.U) hcover
    (fun c => etaleChartCanonicalEquation c₀ c)
      (fun c c' => etaleChartCanonicalEquation_transition c₀ c c')).exists.choose_spec c

/-- The chart equation is a local equation of K_X at every point of the chart. -/
theorem canonicalDivisor_isLocalEquationAt (c₀ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (c : EtaleChart K X n) {x : X}
    (hx : x ∈ c.U) :
    (canonicalDivisor n c₀ hcover).IsLocalEquationAt x (etaleChartCanonicalEquation c₀ c) :=
  CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
    (canonicalDivisor_restrict c₀ hcover c).symm hx

/-- Changing the reference chart changes K_X by the principal divisor of the determinant of the
two reference bases: K_X is well defined up to linear equivalence. -/
theorem canonicalDivisor_change_reference (c₀ c₁ : EtaleChart K X n)
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) :
    canonicalDivisor n c₁ hcover = canonicalDivisor n c₀ hcover +
      principalCartierDivisor X (etaleChartCanonicalEquation c₁ c₀) := by
  have huniq := (cartierDivisor_existsUnique_of_rationalUnits X (fun c : EtaleChart K X n => c.U)
    hcover (fun c => etaleChartCanonicalEquation c₁ c) (fun c c' => etaleChartCanonicalEquation_transition c₁ c c'))
  apply huniq.unique (canonicalDivisor_restrict c₁ hcover)
  intro c
  have hmul : etaleChartCanonicalEquation c₁ c = etaleChartCanonicalEquation c₀ c * etaleChartCanonicalEquation c₁ c₀ := by
    apply Units.ext
    rw [Units.val_mul, etaleChartCanonicalEquation_val, etaleChartCanonicalEquation_val,
      etaleChartCanonicalEquation_val, Module.Basis.det_mul_det]
  rw [map_add, canonicalDivisor_restrict c₀ hcover c, hmul, ofMul_mul, map_add]
  congr 1
  exact principalCartierDivisor_restrict X (etaleChartCanonicalEquation c₁ c₀) c.U

section Cover

variable [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]

omit [IsIntegral X] in
/-- On a smooth scheme of relative dimension n every point lies in an étale chart. -/
theorem etaleCharts_cover : iSup (fun c : EtaleChart K X n => c.U) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hU, hx, hs⟩ := smoothRelativeScheme_exists_affineStandardSmooth (K := K) n x
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K
    Γ(X, U)
  have hfe : g.toRingHom.FormallyEtale := by
    let _ := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin n) K) Γ(X, U) := hg
    exact Algebra.Etale.formallyEtale
  let c : EtaleChart K X n := ⟨U, hU, ⟨⟨x, hx⟩⟩, g, hfe⟩
  exact Opens.mem_iSup.mpr ⟨c, hx⟩

/-- The canonical divisor of a smooth scheme of relative dimension n, for a reference chart. -/
noncomputable def smoothCanonicalDivisor (c₀ : EtaleChart K X n) : CartierDivisor X :=
  canonicalDivisor n c₀ etaleCharts_cover

end Cover

end MixedFujita
