/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogChartSections

/-!
Rational forms with regular logarithmic coefficients on a chart (step 10, R2).

On an étale chart `c` with a logarithmic basis `θ_i` (check 476), call a rational form
*log-regular* on the chart if its coefficients in the exterior algebra basis `θ_s` of the
logarithmic basis are regular functions on the chart (`logChartRegular`). These forms are closed
under sums, multiplication by regular functions, products (products of basis elements are `0` or
`± θ_{s ∪ t}`), and the grade involution (`logChartRegular_mul`, `logChartRegular_involute`); they
contain `θ_i` and the differentials of regular functions (`logChartRegular_ι_kaehlerD`). A
log-regular `b`-form has regular coefficients in the logarithmic wedge basis of degree `b`
(`logChartFormsBasis_repr_mem_of_logChartRegular`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

theorem list_prod_map_neg {A : Type*} [Ring A] {β : Type*} (f : β → A) (l : List β) :
    (l.map fun v => -f v).prod = (-1) ^ l.length * (l.map f).prod := by
  induction l with
  | nil => simp
  | cons v l ih =>
    have hc : (-1 : A) ^ l.length * f v = f v * (-1) ^ l.length :=
      ((Commute.neg_one_left (f v)).pow_left l.length).eq
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.length_cons]
    calc -f v * ((-1) ^ l.length * (l.map f).prod)
        = -((f v * (-1) ^ l.length) * (l.map f).prod) := by rw [neg_mul, mul_assoc]
      _ = -(((-1) ^ l.length * f v) * (l.map f).prod) := by rw [hc]
      _ = (-1) ^ (l.length + 1) * (f v * (l.map f).prod) := by
        rw [pow_succ]
        noncomm_ring

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))

/-- The regular functions on the chart, in `K(X)`. -/
noncomputable abbrev chartRegularFunctions : Subalgebra K X.functionField :=
  (sectionGermAlgHom (K := K) c.U).range

/-- **The rational forms with regular logarithmic coefficients on the chart.** -/
def logChartRegular (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) : Prop :=
  ∀ s, (logChartBasis c σ).ExteriorAlgebra.repr z s ∈ chartRegularFunctions c

theorem logChartRegular_zero : logChartRegular c σ 0 := fun s => by
  rw [map_zero, Finsupp.zero_apply]
  exact Subalgebra.zero_mem _

variable {c σ}

theorem logChartRegular_add {z z' : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : logChartRegular c σ z) (hz' : logChartRegular c σ z') : logChartRegular c σ (z + z') :=
  fun s => by
    rw [map_add, Finsupp.add_apply]
    exact Subalgebra.add_mem _ (hz s) (hz' s)

theorem logChartRegular_neg {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : logChartRegular c σ z) : logChartRegular c σ (-z) := fun s => by
  rw [map_neg, Finsupp.neg_apply]
  exact Subalgebra.neg_mem _ (hz s)

theorem logChartRegular_sub {z z' : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : logChartRegular c σ z) (hz' : logChartRegular c σ z') : logChartRegular c σ (z - z') := by
  rw [sub_eq_add_neg]
  exact logChartRegular_add hz (logChartRegular_neg hz')

theorem logChartRegular_smul {a : X.functionField} (ha : a ∈ chartRegularFunctions c)
    {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]} (hz : logChartRegular c σ z) :
    logChartRegular c σ (a • z) := fun s => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact Subalgebra.mul_mem _ ha (hz s)

theorem logChartRegular_zsmul (k : ℤ) {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : logChartRegular c σ z) : logChartRegular c σ (k • z) := by
  rw [← Int.cast_smul_eq_zsmul X.functionField]
  exact logChartRegular_smul (Subalgebra.intCast_mem _ k) hz

theorem logChartRegular_sum {ι : Type*} (T : Finset ι)
    {f : ι → ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hf : ∀ i ∈ T, logChartRegular c σ (f i)) : logChartRegular c σ (∑ i ∈ T, f i) := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact logChartRegular_zero c σ
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact logChartRegular_add (hf a (Finset.mem_insert_self a T))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

variable (c σ)

theorem logChartRegular_basis (s : Finset (Fin n)) :
    logChartRegular c σ ((logChartBasis c σ).ExteriorAlgebra s) := fun t => by
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

theorem logChartRegular_basis_mul (s t : Finset (Fin n)) :
    logChartRegular c σ ((logChartBasis c σ).ExteriorAlgebra s *
      (logChartBasis c σ).ExteriorAlgebra t) := by
  have hs : (logChartBasis c σ).ExteriorAlgebra s =
      (logChartBasis c σ).ExteriorAlgebra (Set.powersetCard.ofCard (rfl : s.card = s.card) :
        Set.powersetCard (Fin n) s.card) := rfl
  have ht : (logChartBasis c σ).ExteriorAlgebra t =
      (logChartBasis c σ).ExteriorAlgebra (Set.powersetCard.ofCard (rfl : t.card = t.card) :
        Set.powersetCard (Fin n) t.card) := rfl
  rw [hs, ht]
  by_cases hd : Disjoint (Set.powersetCard.ofCard (rfl : s.card = s.card) :
      Set.powersetCard (Fin n) s.card).val (Set.powersetCard.ofCard (rfl : t.card = t.card) :
        Set.powersetCard (Fin n) t.card).val
  · rw [ExteriorAlgebra.basis_mul_of_disjoint _ _ _ hd, Units.smul_def]
    exact logChartRegular_zsmul _ (logChartRegular_basis c σ _)
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint _ _ _ hd]
    exact logChartRegular_zero c σ

variable {c σ}

/-- **Log-regular forms are closed under products.** -/
theorem logChartRegular_mul {z z' : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : logChartRegular c σ z) (hz' : logChartRegular c σ z') : logChartRegular c σ (z * z') := by
  rw [← (logChartBasis c σ).ExteriorAlgebra.sum_repr z,
    ← (logChartBasis c σ).ExteriorAlgebra.sum_repr z', Finset.sum_mul_sum]
  refine logChartRegular_sum _ fun s _ => logChartRegular_sum _ fun t _ => ?_
  rw [smul_mul_smul_comm]
  exact logChartRegular_smul (Subalgebra.mul_mem _ (hz s) (hz' t))
    (logChartRegular_basis_mul c σ s t)

variable (c σ)

theorem logChartRegular_one : logChartRegular c σ 1 := by
  have h : (logChartBasis c σ).ExteriorAlgebra ∅ = 1 := by
    rw [basisExteriorAlgebra_eq_listProd]
    rfl
  rw [← h]
  exact logChartRegular_basis c σ ∅

variable {c σ}

theorem logChartRegular_algebraMap {a : X.functionField} (ha : a ∈ chartRegularFunctions c) :
    logChartRegular c σ (algebraMap X.functionField
      (ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) a) := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact logChartRegular_smul ha (logChartRegular_one c σ)

theorem exteriorInvolute_basisExteriorAlgebra (s : Finset (Fin n)) :
    exteriorInvolute K X.functionField ((logChartBasis c σ).ExteriorAlgebra s) =
      ((-1 : ℤ) ^ s.card) • (logChartBasis c σ).ExteriorAlgebra s := by
  rw [basisExteriorAlgebra_eq_listProd, map_list_prod, List.map_map]
  have h : (exteriorInvolute K X.functionField ∘ fun j => ExteriorAlgebra.ι X.functionField
      (logChartBasis c σ j)) = fun j => -ExteriorAlgebra.ι X.functionField (logChartBasis c σ j) := by
    funext j
    exact exteriorInvolute_ι _
  rw [h, list_prod_map_neg, List.length_ofFn, zsmul_eq_mul]
  push_cast
  rfl

/-- **Log-regular forms are closed under the grade involution.** -/
theorem logChartRegular_involute {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : logChartRegular c σ z) : logChartRegular c σ (exteriorInvolute K X.functionField z) := by
  rw [← (logChartBasis c σ).ExteriorAlgebra.sum_repr z, map_sum]
  refine logChartRegular_sum _ fun s _ => ?_
  rw [exteriorInvolute_smul, exteriorInvolute_basisExteriorAlgebra]
  exact logChartRegular_smul (hz s) (logChartRegular_zsmul _ (logChartRegular_basis c σ s))

theorem ι_logChartBasis_eq (i : Fin n) :
    ExteriorAlgebra.ι X.functionField (logChartBasis c σ i) =
      (logChartBasis c σ).ExteriorAlgebra {i} := by
  rw [basisExteriorAlgebra_eq_listProd]
  simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  congr 2
  exact (Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ _ _)).symm

/-- A `1`-form with regular logarithmic coefficients is log-regular. -/
theorem logChartRegular_ι {v : Ω[X.functionField⁄K]}
    (hv : ∀ i, (logChartBasis c σ).repr v i ∈ chartRegularFunctions c) :
    logChartRegular c σ (ExteriorAlgebra.ι X.functionField v) := by
  rw [← (logChartBasis c σ).sum_repr v, map_sum]
  refine logChartRegular_sum _ fun i _ => ?_
  rw [map_smul, ι_logChartBasis_eq]
  exact logChartRegular_smul (hv i) (logChartRegular_basis c σ _)

variable (c σ)

theorem germ_mem_chartRegularFunctions (a : Γ(X, c.U)) :
    sectionGermAlgHom (K := K) c.U a ∈ chartRegularFunctions c := ⟨a, rfl⟩

theorem coordinate_mem_chartRegularFunctions (j : Fin n) :
    (etaleChartCoordinateRationalUnit c j : X.functionField) ∈ chartRegularFunctions c :=
  ⟨c.coords (MvPolynomial.X j), rfl⟩

/-- The differential of a regular function has regular logarithmic coefficients. -/
theorem logChartBasis_repr_kaehlerD_mem (a : Γ(X, c.U)) (i : Fin n) :
    (logChartBasis c σ).repr (KaehlerDifferential.D K X.functionField
      (sectionGermAlgHom (K := K) c.U a)) i ∈
      chartRegularFunctions c := by
  rw [kaehlerD_eq_sum_logGenerator c (logSetOf σ)]
  simp only [logGenerator_logSetOf]
  rw [Module.Basis.repr_sum_self, etaleCoordPartial_functionField_germ]
  refine Subalgebra.mul_mem _ (germ_mem_chartRegularFunctions c _) ?_
  split_ifs
  · exact coordinate_mem_chartRegularFunctions c i
  · exact Subalgebra.one_mem _

theorem logChartRegular_ι_kaehlerD (a : Γ(X, c.U)) :
    logChartRegular c σ (ExteriorAlgebra.ι X.functionField
      (KaehlerDifferential.D K X.functionField (sectionGermAlgHom (K := K) c.U a))) :=
  logChartRegular_ι fun i => logChartBasis_repr_kaehlerD_mem c σ a i

/-- The coefficients of a `b`-form in the logarithmic wedge basis of degree `b` are its coefficients
in the exterior algebra basis. -/
theorem logChartFormsBasis_repr_eq {b : ℕ} (z : RationalForms K X b)
    (t : Set.powersetCard (Fin n) b) :
    (logChartFormsBasis c σ b).repr z t =
      (logChartBasis c σ).ExteriorAlgebra.repr (z : ExteriorAlgebra X.functionField
        Ω[X.functionField⁄K]) t.1 := by
  conv_rhs => rw [← (logChartFormsBasis c σ b).sum_repr z]
  rw [Submodule.coe_sum, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single t]
  · rw [Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis, map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro t' _ ht'
    rw [Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis, map_smul, Finsupp.smul_apply,
      Module.Basis.repr_self, Finsupp.single_apply,
      ite_eq_right_iff.mpr (fun h => absurd (Subtype.ext h) ht'), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem logChartFormsBasis_repr_mem_of_logChartRegular {b : ℕ} {z : RationalForms K X b}
    (hz : logChartRegular c σ (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]))
    (t : Set.powersetCard (Fin n) b) :
    (logChartFormsBasis c σ b).repr z t ∈ chartRegularFunctions c := by
  rw [logChartFormsBasis_repr_eq]
  exact hz t.1

end MixedFujita
