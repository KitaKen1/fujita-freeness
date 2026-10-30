/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalDivisor
public import MixedFujita.ProperBirationalSections

/-!
The actual differential map from an etale-chart stalk to the function field
carries its Kaehler coordinate basis to the original generic basis. On a
curve, membership in this image is exactly regularity of the single basis
coefficient. The original canonical Cartier equation converts the reference
differential into each local coordinate differential, so its actual sections
on every nonempty open are precisely the rational coefficients making that
reference form regular at every point. No comparison with Weil differentials
or Serre duality is assumed or asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open KaehlerDifferential

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower functionFieldBaseAlgebra functionFieldBaseScalarTower

theorem basis_fin_one_repr_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 1) R M) (w : M) : (b.repr w 0) • b 0 = w := by
  simpa only [Fin.sum_univ_one] using b.sum_repr w

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]

theorem canonicalStalkFunctionFieldScalarTower (x : X) :
    IsScalarTower K (X.presheaf.stalk x) X.functionField :=
  IsScalarTower.of_algebraMap_eq fun k => (stalkFunctionFieldAlgHom (K := K) x).commutes k |>.symm

attribute [local instance] canonicalStalkFunctionFieldScalarTower

theorem etaleChart_differential_map_basis {n : ℕ} (c : EtaleChart K X n)
    (x : X) (hx : x ∈ c.U) (i : Fin n) :
    KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField
      (etaleCoordinateBasis (etaleChartStalkCoords c x hx)
        (etaleChartStalkCoords_formallyEtale c x hx) i) = etaleChartBasis c i := by
  rw [etaleCoordinateBasis_apply, KaehlerDifferential.map_D]
  unfold etaleChartBasis
  rw [etaleCoordinateBasis_apply]
  congr 1
  exact congrArg (fun f : MvPolynomial (Fin n) K →ₐ[K] X.functionField =>
    f (MvPolynomial.X i)) (etaleChart_stalkFunctionField_comp_stalkCoords c x hx)

theorem curveEtaleChartCanonicalEquation_smul (c₀ c : EtaleChart K X 1) :
    (etaleChartCanonicalEquation c₀ c : X.functionField) • etaleChartBasis c 0 =
      etaleChartBasis c₀ 0 := by
  rw [etaleChartCanonicalEquation_val, Module.Basis.det_apply, Matrix.det_fin_one,
    Module.Basis.toMatrix_apply]
  exact basis_fin_one_repr_smul _ _

noncomputable def stalkRationalDifferentialMap (x : X) :
    Ω[X.presheaf.stalk x⁄K] →ₗ[K] Ω[X.functionField⁄K] :=
  (KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField).restrictScalars K

theorem curve_differential_mem_stalk_range_iff (c : EtaleChart K X 1)
    (x : X) (hx : x ∈ c.U) (w : Ω[X.functionField⁄K]) :
    w ∈ (stalkRationalDifferentialMap (K := K) x).range ↔
      (etaleChartBasis c).repr w 0 ∈
        (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  let b := etaleCoordinateBasis (etaleChartStalkCoords c x hx)
    (etaleChartStalkCoords_formallyEtale c x hx)
  have hb := etaleChart_differential_map_basis c x hx 0
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨b.repr v 0, ?_⟩
    change algebraMap (X.presheaf.stalk x) X.functionField (b.repr v 0) =
      (etaleChartBasis c).repr
        (KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField v) 0
    have hmap : KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField v =
        algebraMap (X.presheaf.stalk x) X.functionField (b.repr v 0) • etaleChartBasis c 0 := by
      calc
        _ = KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField
            ((b.repr v 0) • b 0) := congrArg _ (basis_fin_one_repr_smul b v).symm
        _ = _ := by rw [map_smul, hb, algebraMap_smul]
    rw [hmap, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · rintro ⟨a, ha⟩
    refine ⟨a • b 0, ?_⟩
    change KaehlerDifferential.map K K (X.presheaf.stalk x) X.functionField (a • b 0) = w
    rw [map_smul, hb, ← algebraMap_smul X.functionField, ha]
    exact basis_fin_one_repr_smul _ _

theorem canonicalDivisor_sections_iff_regular_curve_differential
    (c₀ : EtaleChart K X 1)
    (hcover : iSup (fun c : EtaleChart K X 1 => c.U) = ⊤)
    (U : X.Opens) [Nonempty U] (s : Γ(TauCeti.AlgebraicGeometry.Scheme.rationalFunctions X, U)) :
    s ∈ (canonicalDivisor 1 c₀ hcover).sections U ↔
      ∀ x ∈ U, (rationalFunctionsEquiv U s) • etaleChartBasis c₀ 0 ∈
        (stalkRationalDifferentialMap (K := K) x).range := by
  constructor
  · intro hs x hx
    obtain ⟨c, hxc⟩ : ∃ c : EtaleChart K X 1, x ∈ c.U := by
      have : x ∈ iSup (fun c : EtaleChart K X 1 => c.U) := hcover.symm ▸ Opens.mem_top x
      simpa only [Opens.mem_iSup] using this
    rw [curve_differential_mem_stalk_range_iff c x hxc,
      ← curveEtaleChartCanonicalEquation_smul c₀ c, smul_smul, map_smul,
      Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      mul_comm]
    exact (CartierDivisor.mem_sections.mp hs) x hx _
      (canonicalDivisor_isLocalEquationAt c₀ hcover c hxc)
  · intro hs
    apply CartierDivisor.mem_sections_iff_exists.mpr
    intro x hx
    obtain ⟨c, hxc⟩ : ∃ c : EtaleChart K X 1, x ∈ c.U := by
      have : x ∈ iSup (fun c : EtaleChart K X 1 => c.U) := hcover.symm ▸ Opens.mem_top x
      simpa only [Opens.mem_iSup] using this
    refine ⟨etaleChartCanonicalEquation c₀ c,
      canonicalDivisor_isLocalEquationAt c₀ hcover c hxc, ?_⟩
    have h := (curve_differential_mem_stalk_range_iff c x hxc _).mp (hs x hx)
    rwa [← curveEtaleChartCanonicalEquation_smul c₀ c, smul_smul, map_smul,
      Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one,
      mul_comm] at h

end MixedFujita
