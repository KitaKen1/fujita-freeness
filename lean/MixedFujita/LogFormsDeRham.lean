/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogDIComponents
public import MixedFujita.LinearCechDeRham

/-!
The de Rham differential of logarithmic forms (step 10, R2).

For a subring `A` of `K(X)` and an étale chart `c` with logarithmic basis `θ_i` (check 476), the
rational forms whose coefficients in the exterior algebra basis `θ_s` lie in `A` (`LogCoeffsIn`)
are closed under sums, `A`-multiples and products, as for the regular functions on the chart in
check 483. The `θ_s` are closed, so these forms are also closed under the de Rham differential when
the differentials of the elements of `A` have coefficients in `A`
(`logCoeffsIn_rationalDeRhamDiff`). For the local ring at a point of a simple normal crossing
chart this holds. Hence the de Rham differential and the products with logarithmic `1`-forms
preserve the logarithmic forms at every point (`rationalFormsDiff_mem_logFormsLattice`,
`mem_logFormsLattice_of_eq_ι_mul`).

In characteristic `p`, for `N = p • M + Σ_k r_k • E_k` the local equation `f = g^p Π_k h_k^{r_k}`
has `df / f = Σ_k r_k dh_k / h_k` logarithmic. So the de Rham differential preserves
`Ω^•_X(log E)(N)` (`logFormsDiff`, with `d ∘ d = 0`). As for check 420, it gives a morphism of
presheaves of abelian groups (`logFormsDiffPresheaf`) and the de Rham differential between the
Čech complexes (`logFormsCechDiff`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Coefficients

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) (A : Subring X.functionField)

/-- **The rational forms whose coefficients in the logarithmic exterior basis of a chart lie in
`A`.** -/
def LogCoeffsIn (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) : Prop :=
  ∀ s, (logChartBasis c σ).ExteriorAlgebra.repr z s ∈ A

theorem logCoeffsIn_zero : LogCoeffsIn c σ A 0 := fun s => by
  rw [map_zero, Finsupp.zero_apply]
  exact A.zero_mem

variable {c σ A}

theorem logCoeffsIn_add {z z' : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : LogCoeffsIn c σ A z) (hz' : LogCoeffsIn c σ A z') : LogCoeffsIn c σ A (z + z') :=
  fun s => by
    rw [map_add, Finsupp.add_apply]
    exact A.add_mem (hz s) (hz' s)

theorem logCoeffsIn_neg {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : LogCoeffsIn c σ A z) : LogCoeffsIn c σ A (-z) := fun s => by
  rw [map_neg, Finsupp.neg_apply]
  exact A.neg_mem (hz s)

theorem logCoeffsIn_sub {z z' : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : LogCoeffsIn c σ A z) (hz' : LogCoeffsIn c σ A z') : LogCoeffsIn c σ A (z - z') := by
  rw [sub_eq_add_neg]
  exact logCoeffsIn_add hz (logCoeffsIn_neg hz')

theorem logCoeffsIn_smul {a : X.functionField} (ha : a ∈ A)
    {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]} (hz : LogCoeffsIn c σ A z) :
    LogCoeffsIn c σ A (a • z) := fun s => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact A.mul_mem ha (hz s)

theorem logCoeffsIn_zsmul (k : ℤ) {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : LogCoeffsIn c σ A z) : LogCoeffsIn c σ A (k • z) := by
  rw [← Int.cast_smul_eq_zsmul X.functionField]
  exact logCoeffsIn_smul (intCast_mem A k) hz

theorem logCoeffsIn_sum {ι : Type*} (T : Finset ι)
    {f : ι → ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hf : ∀ i ∈ T, LogCoeffsIn c σ A (f i)) : LogCoeffsIn c σ A (∑ i ∈ T, f i) := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact logCoeffsIn_zero c σ A
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    exact logCoeffsIn_add (hf a (Finset.mem_insert_self a T))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

variable (c σ A)

theorem logCoeffsIn_basis (s : Finset (Fin n)) :
    LogCoeffsIn c σ A ((logChartBasis c σ).ExteriorAlgebra s) := fun t => by
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact A.one_mem
  · exact A.zero_mem

theorem logCoeffsIn_basis_mul (s t : Finset (Fin n)) :
    LogCoeffsIn c σ A ((logChartBasis c σ).ExteriorAlgebra s *
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
    exact logCoeffsIn_zsmul _ (logCoeffsIn_basis c σ A _)
  · rw [ExteriorAlgebra.basis_mul_of_not_disjoint _ _ _ hd]
    exact logCoeffsIn_zero c σ A

variable {c σ A}

/-- **Forms with coefficients in `A` are closed under products.** -/
theorem logCoeffsIn_mul {z z' : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]}
    (hz : LogCoeffsIn c σ A z) (hz' : LogCoeffsIn c σ A z') : LogCoeffsIn c σ A (z * z') := by
  rw [← (logChartBasis c σ).ExteriorAlgebra.sum_repr z,
    ← (logChartBasis c σ).ExteriorAlgebra.sum_repr z', Finset.sum_mul_sum]
  refine logCoeffsIn_sum _ fun s _ => logCoeffsIn_sum _ fun t _ => ?_
  rw [smul_mul_smul_comm]
  exact logCoeffsIn_smul (A.mul_mem (hz s) (hz' t)) (logCoeffsIn_basis_mul c σ A s t)

/-- A `1`-form with logarithmic coefficients in `A`. -/
theorem logCoeffsIn_ι {v : Ω[X.functionField⁄K]} (hv : ∀ i, (logChartBasis c σ).repr v i ∈ A) :
    LogCoeffsIn c σ A (ExteriorAlgebra.ι X.functionField v) := by
  rw [← (logChartBasis c σ).sum_repr v, map_sum]
  refine logCoeffsIn_sum _ fun i _ => ?_
  rw [map_smul, ι_logChartBasis_eq]
  exact logCoeffsIn_smul (hv i) (logCoeffsIn_basis c σ A _)

variable (c σ)

/-- **The logarithmic exterior basis is closed.** -/
theorem rationalDeRhamDiff_logChartBasis_exteriorAlgebra (c₀ : EtaleChart K X n)
    (s : Finset (Fin n)) : rationalDeRhamDiff c₀ ((logChartBasis c σ).ExteriorAlgebra s) = 0 := by
  rw [rationalDeRhamDiff_eq c₀ c, basisExteriorAlgebra_eq_listProd]
  generalize List.ofFn (s.orderEmbOfFin rfl) = l
  induction l with
  | nil => rw [List.map_nil, List.prod_nil]; exact rationalDeRhamDiff_one c
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, rationalDeRhamDiff_mul, ih, mul_zero, add_zero,
      ← logGenerator_logSetOf c σ j, rationalDeRhamDiff_ι_logGenerator, zero_mul]

variable {c σ}

/-- **The de Rham differential preserves the forms with coefficients in `A`** when the
differentials of the elements of `A` have coefficients in `A`. -/
theorem logCoeffsIn_rationalDeRhamDiff (c₀ : EtaleChart K X n)
    (hD : ∀ a ∈ A, ∀ i, (logChartBasis c σ).repr (KaehlerDifferential.D K X.functionField a) i ∈ A)
    {z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]} (hz : LogCoeffsIn c σ A z) :
    LogCoeffsIn c σ A (rationalDeRhamDiff c₀ z) := by
  rw [← (logChartBasis c σ).ExteriorAlgebra.sum_repr z, map_sum]
  refine logCoeffsIn_sum _ fun s _ => ?_
  rw [rationalDeRhamDiff_smul, rationalDeRhamDiff_logChartBasis_exteriorAlgebra, smul_zero,
    add_zero]
  exact logCoeffsIn_mul (logCoeffsIn_ι (hD _ (hz s))) (logCoeffsIn_basis c σ A s)

variable (c σ A) in
theorem logCoeffsIn_of_forall_repr_mem {b : ℕ} (z : RationalForms K X b)
    (h : ∀ t, (logChartFormsBasis c σ b).repr z t ∈ A) :
    LogCoeffsIn c σ A (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) := by
  intro s
  by_cases hs : s.card = b
  · have h' := logChartFormsBasis_repr_eq c σ z ⟨s, Set.powersetCard.mem_iff.mpr hs⟩
    rw [← h']
    exact h _
  · have hexp := (logChartFormsBasis c σ b).sum_repr z
    have hcoe := congrArg (fun w : RationalForms K X b =>
      (logChartBasis c σ).ExteriorAlgebra.repr (w : ExteriorAlgebra X.functionField
        Ω[X.functionField⁄K]) s) hexp
    rw [← hcoe, Submodule.coe_sum, map_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero]
    · exact A.zero_mem
    · intro t _
      rw [Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis, map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply,
        ite_eq_right_iff.mpr (fun h => absurd (by subst h; exact Set.powersetCard.mem_iff.mp t.2) hs),
        smul_zero]

theorem logChartFormsBasis_repr_mem_of_logCoeffsIn {b : ℕ} {z : RationalForms K X b}
    (hz : LogCoeffsIn c σ A (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]))
    (t : Set.powersetCard (Fin n) b) : (logChartFormsBasis c σ b).repr z t ∈ A := by
  rw [logChartFormsBasis_repr_eq]
  exact hz t.1

end Coefficients

section Stalk

/-- The local ring at `x`, as a subring of `K(X)`. -/
noncomputable abbrev stalkFunctions (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))

theorem logChartBasis_repr_mem_stalk_of_mem_span (x : X) {v : Ω[X.functionField⁄K]}
    (hv : v ∈ Submodule.span (X.presheaf.stalk x) (Set.range (logChartBasis c σ))) (i : Fin n) :
    (logChartBasis c σ).repr v i ∈ stalkFunctions x := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  | zero => rw [map_zero, Finsupp.zero_apply]; exact Subring.zero_mem _
  | add v w _ _ hv hw => rw [map_add, Finsupp.add_apply]; exact Subring.add_mem _ hv hw
  | smul a v _ hv =>
    rw [← algebraMap_smul X.functionField a v, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ ⟨a, rfl⟩ hv

/-- The differential of a function regular at `x` has logarithmic coefficients regular at `x`. -/
theorem logChartBasis_repr_kaehlerD_mem_stalk (x : X) (hx : x ∈ c.U) {a : X.functionField}
    (ha : a ∈ stalkFunctions x) (i : Fin n) :
    (logChartBasis c σ).repr (KaehlerDifferential.D K X.functionField a) i ∈ stalkFunctions x := by
  obtain ⟨s, rfl⟩ := ha
  exact logChartBasis_repr_mem_stalk_of_mem_span c σ x
    (regularOneFormsAt_le_span_logChartBasis c σ x hx
      ⟨KaehlerDifferential.D K _ s, KaehlerDifferential.map_D K K _ _ s⟩) i

theorem rationalDlog_pow (g : X.functionFieldˣ) (m : ℕ) :
    rationalDlog K (g ^ m) = m • rationalDlog K g := by
  induction m with
  | zero => rw [pow_zero, rationalDlog_one, zero_smul]
  | succ m ih => rw [pow_succ, rationalDlog_mul, ih, succ_nsmul]

theorem rationalDlog_pow_char (p : ℕ) [CharP K p] (g : X.functionFieldˣ) :
    rationalDlog K (g ^ p) = 0 := by
  rw [rationalDlog_pow, ← Nat.cast_smul_eq_nsmul X.functionField,
    natCast_char_eq_zero_of_algebra (K := K) (S := X.functionField) p, zero_smul]

theorem kaehlerD_eq_smul_rationalDlog (f : X.functionFieldˣ) :
    KaehlerDifferential.D K X.functionField (f : X.functionField) =
      (f : X.functionField) • rationalDlog K f := by
  rw [rationalDlog, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ f.ne_zero, one_smul]

end Stalk

section Twist

variable {r : ℕ} (E : Fin r → CartierDivisor X)

/-- The local equation `g^p Π_k h_k^{r_k}` of `p • M + Σ_k r_k • E_k`. -/
theorem isLocalEquationAt_logTwist (p : ℕ) (M : CartierDivisor X) (rr : Fin r → ℕ) {x : X}
    {g : X.functionFieldˣ} (hg : M.IsLocalEquationAt x g) {h : Fin r → X.functionFieldˣ}
    (hh : ∀ k, (E k).IsLocalEquationAt x (h k)) :
    (p • M + ∑ k, rr k • E k).IsLocalEquationAt x (g ^ p * ∏ k, h k ^ rr k) := by
  refine (isLocalEquationAt_nsmul_pow hg p).mul ?_
  have : ∀ T : Finset (Fin r),
      (∑ k ∈ T, rr k • E k).IsLocalEquationAt x (∏ k ∈ T, h k ^ rr k) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.prod_empty]
      exact CartierDivisor.isLocalEquationAt_zero x
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (isLocalEquationAt_nsmul_pow (hh a) (rr a)).mul ih
  exact this Finset.univ

theorem rationalDlog_logTwist (p : ℕ) [CharP K p] (g : X.functionFieldˣ)
    (h : Fin r → X.functionFieldˣ) (rr : Fin r → ℕ) :
    rationalDlog K (g ^ p * ∏ k, h k ^ rr k) = ∑ k, rr k • rationalDlog K (h k) := by
  rw [rationalDlog_mul, rationalDlog_pow_char p, zero_add]
  have : ∀ T : Finset (Fin r),
      rationalDlog K (∏ k ∈ T, h k ^ rr k) = ∑ k ∈ T, rr k • rationalDlog K (h k) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, rationalDlog_one]
    | insert a T ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, rationalDlog_mul, ih, rationalDlog_pow]
  exact this Finset.univ

theorem sum_rationalDlog_mem_logOneFormsLattice (x : X) (h : Fin r → X.functionFieldˣ)
    (hh : ∀ k, (E k).IsLocalEquationAt x (h k)) (rr : Fin r → ℕ) :
    ∑ k, rr k • rationalDlog K (h k) ∈ logOneFormsLattice K E x :=
  Submodule.sum_mem _ fun k _ => by
    have hk : rationalDlog K (h k) ∈ logOneFormsLattice K E x :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨k, h k, hh k, rfl⟩)
    exact nsmul_mem hk (rr k)

end Twist

theorem logFormsSheaf_sections_subsingleton {r : ℕ} (E : Fin r → CartierDivisor X)
    (M : CartierDivisor X) (b : ℕ) {U : X.Opens} (hU : IsEmpty U) :
    Subsingleton Γ(logFormsSheaf K E M b, U) :=
  modules_sections_subsingleton_of_eq_bot _ (Opens.coe_eq_empty.mp (Set.isEmpty_coe_sort.mp hU))

section SNC

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)

include hnorm hinj hξ hEc in
/-- **Logarithmic forms at a point of a simple normal crossing chart are the forms with
logarithmic coefficients in the local ring.** -/
theorem mem_logFormsLattice_iff_logCoeffsIn (c : EtaleChart K X n) (σ : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σ) (x : X) (hx : x ∈ c.U) {b : ℕ} (z : RationalForms K X b) :
    z ∈ logFormsLattice K E x b ↔
      LogCoeffsIn c σ (stalkFunctions x) (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) :=
  ⟨fun h => logCoeffsIn_of_forall_repr_mem c σ _ z
      ((mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b z).mp h),
    fun h => (mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b z).mpr
      (logChartFormsBasis_repr_mem_of_logCoeffsIn h)⟩

include hnorm hinj hξ hEc in
/-- **The de Rham differential preserves the logarithmic forms at every point.** -/
theorem rationalFormsDiff_mem_logFormsLattice (hsnc : IsSNCFamily K n ξ) (c₀ : EtaleChart K X n)
    {b : ℕ} (x : X) {z : RationalForms K X b} (hz : z ∈ logFormsLattice K E x b) :
    rationalFormsDiff c₀ b z ∈ logFormsLattice K E x (b + 1) := by
  obtain ⟨c, σ, hxc, hc⟩ := hsnc x
  rw [mem_logFormsLattice_iff_logCoeffsIn hnorm ξ hinj hξ E hEc c σ hc x hxc] at hz ⊢
  rw [rationalFormsDiff_coe]
  exact logCoeffsIn_rationalDeRhamDiff c₀
    (fun a ha i => logChartBasis_repr_kaehlerD_mem_stalk c σ x hxc ha i) hz

include hnorm hinj hξ hEc in
/-- **Products with logarithmic `1`-forms preserve the logarithmic forms at every point.** -/
theorem mem_logFormsLattice_of_eq_ι_mul (hsnc : IsSNCFamily K n ξ) {b : ℕ} (x : X)
    {v : Ω[X.functionField⁄K]} (hv : v ∈ logOneFormsLattice K E x) {z : RationalForms K X b}
    (hz : z ∈ logFormsLattice K E x b) (w : RationalForms K X (b + 1))
    (hw : (w : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) =
      ExteriorAlgebra.ι X.functionField v * z) : w ∈ logFormsLattice K E x (b + 1) := by
  obtain ⟨c, σ, hxc, hc⟩ := hsnc x
  rw [mem_logFormsLattice_iff_logCoeffsIn hnorm ξ hinj hξ E hEc c σ hc x hxc] at hz ⊢
  rw [logOneFormsLattice_eq_span hnorm ξ hinj hξ E hEc c σ hc x hxc] at hv
  rw [hw]
  exact logCoeffsIn_mul (logCoeffsIn_ι (logChartBasis_repr_mem_stalk_of_mem_span c σ x hv)) hz

include hnorm hinj hξ hEc in
/-- **In characteristic `p` the de Rham differential preserves the logarithmic forms with poles
bounded by `p • M + Σ_k r_k • E_k` at every point.** -/
theorem smul_rationalFormsDiff_mem_logFormsLattice (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) {b : ℕ} (x : X) (g : X.functionFieldˣ) (h : Fin r → X.functionFieldˣ)
    (hh : ∀ k, (E k).IsLocalEquationAt x (h k)) (rr : Fin r → ℕ) (ω : RationalForms K X b)
    (hω : ((g ^ p * ∏ k, h k ^ rr k : X.functionFieldˣ) : X.functionField) • ω ∈
      logFormsLattice K E x b) :
    ((g ^ p * ∏ k, h k ^ rr k : X.functionFieldˣ) : X.functionField) • rationalFormsDiff c₀ b ω ∈
      logFormsLattice K E x (b + 1) := by
  obtain ⟨f, hf⟩ : ∃ f : X.functionFieldˣ, f = g ^ p * ∏ k, h k ^ rr k := ⟨_, rfl⟩
  rw [← hf] at hω ⊢
  have hd := rationalFormsDiff_mem_logFormsLattice hnorm ξ hinj hξ E hEc hsnc c₀ x hω
  have hm := mem_logFormsLattice_of_eq_ι_mul hnorm ξ hinj hξ E hEc hsnc x
    (sum_rationalDlog_mem_logOneFormsLattice (K := K) E x h hh rr) hω
    (rationalFormsDiff c₀ b ((f : X.functionField) • ω) -
      (f : X.functionField) • rationalFormsDiff c₀ b ω) (by
      rw [Submodule.coe_sub, rationalFormsDiff_coe, Submodule.coe_smul, rationalDeRhamDiff_smul,
        Submodule.coe_smul, rationalFormsDiff_coe, add_sub_cancel_right,
        kaehlerD_eq_smul_rationalDlog, hf, rationalDlog_logTwist p, ← hf, map_smul, smul_mul_assoc,
        mul_smul_comm])
  have := Submodule.sub_mem _ hd hm
  rwa [sub_sub_cancel] at this

variable (K) in
include hnorm hinj hξ hEc in
theorem rationalFormsDiff_mem_logFormsSections (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) {b : ℕ} (U : X.Opens)
    [Nonempty U] (s : Γ(rationalFormsSheaf K X b, U))
    (hs : s ∈ logFormsSections K E (p • M + ∑ k, rr k • E k) b U) :
    (rationalFormsSectionsEquiv K (b + 1) U).symm
        (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s)) ∈
      logFormsSections K E (p • M + ∑ k, rr k • E k) (b + 1) U := by
  rw [mem_logFormsSections_iff_exists]
  intro x hx
  obtain ⟨g, hg⟩ := M.exists_isLocalEquationAt x
  choose h hh using fun k => (E k).exists_isLocalEquationAt x
  refine ⟨_, isLocalEquationAt_logTwist E p M rr hg hh, ?_⟩
  rw [AddEquiv.apply_symm_apply]
  exact smul_rationalFormsDiff_mem_logFormsLattice hnorm ξ hinj hξ E hEc hsnc p c₀ x g h hh rr _
    (hs x hx _ (isLocalEquationAt_logTwist E p M rr hg hh))

/-- **The de Rham differential of `Ω^•_X(log E)(p • M + Σ_k r_k • E_k)`** on a nonempty open
subset. -/
noncomputable def logFormsDiff (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) (U : X.Opens)
    [Nonempty U] :
    logFormsSections K E (p • M + ∑ k, rr k • E k) b U →+
      logFormsSections K E (p • M + ∑ k, rr k • E k) (b + 1) U where
  toFun s := ⟨(rationalFormsSectionsEquiv K (b + 1) U).symm
      (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s)),
    rationalFormsDiff_mem_logFormsSections K hnorm ξ hinj hξ E hEc hsnc p c₀ M rr U s.1 s.2⟩
  map_zero' := Subtype.ext (by
    change (rationalFormsSectionsEquiv K (b + 1) U).symm
      (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U 0)) = 0
    rw [map_zero, map_zero, map_zero])
  map_add' s t := Subtype.ext (by
    change (rationalFormsSectionsEquiv K (b + 1) U).symm
        (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U (s + t))) =
      (rationalFormsSectionsEquiv K (b + 1) U).symm
          (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s)) +
        (rationalFormsSectionsEquiv K (b + 1) U).symm
          (rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U t))
    rw [map_add, map_add, map_add])

theorem rationalFormsSectionsEquiv_logFormsDiff (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) (U : X.Opens)
    [Nonempty U] (s : logFormsSections K E (p • M + ∑ k, rr k • E k) b U) :
    rationalFormsSectionsEquiv K (b + 1) U
        (logFormsDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s) =
      rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s) :=
  AddEquiv.apply_symm_apply (rationalFormsSectionsEquiv K (b + 1) U) _

/-- `d ∘ d = 0` on `Ω^•_X(log E)(p • M + Σ_k r_k • E_k)`. -/
theorem logFormsDiff_comp (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) (U : X.Opens)
    [Nonempty U] (s : logFormsSections K E (p • M + ∑ k, rr k • E k) b U) :
    logFormsDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (b + 1) U
      (logFormsDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s) = 0 := by
  apply Subtype.ext
  apply (rationalFormsSectionsEquiv K (b + 2) U).injective
  rw [rationalFormsSectionsEquiv_logFormsDiff, rationalFormsSectionsEquiv_logFormsDiff,
    rationalFormsDiff_comp]
  exact ((rationalFormsSectionsEquiv K (b + 2) U).map_zero).symm

open Classical in
/-- The de Rham differential of `Ω^•_X(log E)(p • M + Σ_k r_k • E_k)` on every open subset (zero on the empty one). -/
noncomputable def logFormsDiffApp (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ)
    (U : X.Opens) :
    Γ(logFormsSheaf K E (p • M + ∑ k, rr k • E k) b, U) →+ Γ(logFormsSheaf K E (p • M + ∑ k, rr k • E k) (b + 1), U) :=
  if _h : Nonempty U then logFormsDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U else 0

theorem rationalFormsSectionsEquiv_logFormsDiffApp (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) (U : X.Opens) [h : Nonempty U]
    (s : Γ(logFormsSheaf K E (p • M + ∑ k, rr k • E k) b, U)) :
    rationalFormsSectionsEquiv K (b + 1) U (logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s).1 =
      rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U s.1) := by
  unfold logFormsDiffApp
  split
  · exact rationalFormsSectionsEquiv_logFormsDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s
  · exact absurd h ‹_›

/-- **The de Rham differential of `Ω^•_X(log E)(p • M + Σ_k r_k • E_k)` as a morphism of presheaves of abelian groups.** -/
noncomputable def logFormsDiffPresheaf (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) :
    (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b).presheaf ⟶ (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (b + 1)).presheaf where
  app U := AddCommGrpCat.ofHom (logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U.unop)
  naturality {U V} i := by
    ext s
    change logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b V.unop
        ((logFormsSheaf K E (p • M + ∑ k, rr k • E k) b).presheaf.map i s) =
      (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (b + 1)).presheaf.map i
        (logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U.unop s)
    rcases isEmpty_or_nonempty V.unop with hV | hV
    · exact @Subsingleton.elim _ (logFormsSheaf_sections_subsingleton E (p • M + ∑ k, rr k • E k) (b + 1) hV) _ _
    · have : Nonempty U.unop := ⟨⟨hV.some.1, i.unop.le hV.some.2⟩⟩
      apply Subtype.ext
      apply (rationalFormsSectionsEquiv K (b + 1) V.unop).injective
      rw [rationalFormsSectionsEquiv_logFormsDiffApp]
      change rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b V.unop
          ((rationalFormsSheaf K X b).presheaf.map i.unop.op s.1)) =
        rationalFormsSectionsEquiv K (b + 1) V.unop
          ((rationalFormsSheaf K X (b + 1)).presheaf.map i.unop.op
            (logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U.unop s).1)
      rw [rationalFormsSectionsEquiv_map K b i.unop, rationalFormsSectionsEquiv_map K (b + 1) i.unop,
        rationalFormsSectionsEquiv_logFormsDiffApp]

theorem logFormsDiffPresheaf_app_apply (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ)
    (U : X.Opens) (s : Γ(logFormsSheaf K E (p • M + ∑ k, rr k • E k) b, U)) :
    (logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b).app (op U) s =
      logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s :=
  rfl

/-- `d ∘ d = 0` as morphisms of presheaves. -/
theorem logFormsDiffPresheaf_comp (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) :
    logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b ≫ logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (b + 1) =
      0 := by
  ext U s
  change logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (b + 1) U (logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s) = 0
  rcases isEmpty_or_nonempty U with hU | hU
  · exact @Subsingleton.elim _ (logFormsSheaf_sections_subsingleton E (p • M + ∑ k, rr k • E k) (b + 1 + 1) hU) _ _
  · apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (b + 2) U).injective
    rw [rationalFormsSectionsEquiv_logFormsDiffApp, rationalFormsSectionsEquiv_logFormsDiffApp,
      rationalFormsDiff_comp]
    exact ((rationalFormsSectionsEquiv K (b + 2) U).map_zero).symm

/-- **The de Rham differential between the Čech complexes** of `Ω^b_X(log E)(p • M + Σ_k r_k • E_k)`
and `Ω^{b+1}_X(log E)(p • M + Σ_k r_k • E_k)` for a finite family of open subsets. -/
noncomputable def logFormsCechDiff (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    TopCat.Presheaf.cechComplex 𝒰 (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b).presheaf ⟶
      TopCat.Presheaf.cechComplex 𝒰 (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (b + 1)).presheaf :=
  TopCat.Presheaf.cechComplexMap 𝒰 (logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b)

/-- `d ∘ d = 0` between the Čech complexes. -/
theorem logFormsCechDiff_comp (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    logFormsCechDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰 ≫ logFormsCechDiff hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (b + 1) 𝒰 = 0 := by
  rw [logFormsCechDiff, logFormsCechDiff, TopCat.Presheaf.cechComplexMap,
    TopCat.Presheaf.cechComplexMap, ← Functor.map_comp, logFormsDiffPresheaf_comp]
  exact Scheme.Modules.cechComplexMap_zero 𝒰

end SNC

section Linear

attribute [local instance] sectionsBaseModule

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)

/-- **The logarithmic de Rham differential is `K`-linear on sections.** -/
theorem logFormsDiffApp_algebraMap_smul (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) (U : X.Opens) (c : K)
    (s : Γ(logFormsSheaf K E (p • M + ∑ k, rr k • E k) b, U)) :
    logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U (algebraMap K Γ(X, U) c • s) =
      algebraMap K Γ(X, U) c • logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s := by
  rcases isEmpty_or_nonempty U with hU | hU
  · exact @Subsingleton.elim _ (logFormsSheaf_sections_subsingleton E (p • M + ∑ k, rr k • E k) (b + 1) hU) _ _
  · apply Subtype.ext
    apply (rationalFormsSectionsEquiv K (b + 1) U).injective
    rw [rationalFormsSectionsEquiv_logFormsDiffApp]
    change rationalFormsDiff c₀ b (rationalFormsSectionsEquiv K b U
        (algebraMap K Γ(X, U) c • s.1)) =
      rationalFormsSectionsEquiv K (b + 1) U
        (algebraMap K Γ(X, U) c • (logFormsDiffApp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b U s).1)
    have hc : X.germToFunctionField U (algebraMap K Γ(X, U) c) = algebraMap K X.functionField c :=
      (sectionGermAlgHom (K := K) U).commutes c
    rw [rationalFormsSectionsEquiv_smul, rationalFormsSectionsEquiv_smul, hc,
      rationalFormsDiff_algebraMap_smul, rationalFormsSectionsEquiv_logFormsDiffApp]

/-- The logarithmic de Rham differential on Čech cochains, `K`-linearly. -/
noncomputable def logFormsCechDiffLinear (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) (m : ℕ) :
    TopCat.Presheaf.CechCochain 𝒰 (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b).presheaf m →ₗ[K]
      TopCat.Presheaf.CechCochain 𝒰 (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (b + 1)).presheaf m where
  toFun := TopCat.Presheaf.cechCochainMap 𝒰 (logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b) m
  map_add' := map_add _
  map_smul' c f := by
    funext x
    rw [TopCat.Presheaf.cechCochainMap_apply, Pi.smul_apply, Pi.smul_apply,
      TopCat.Presheaf.cechCochainMap_apply]
    exact logFormsDiffApp_algebraMap_smul hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b _ c (f x)

/-- **The logarithmic de Rham differential as a `K`-linear map of Čech complexes.** -/
noncomputable def logFormsCechDiffLinearMap (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) b) 𝒰 ⟶
      cechComplexLinear K (logFormsSheaf K E (p • M + ∑ k, rr k • E k) (b + 1)) 𝒰 :=
  CochainComplex.ofHom
    (fun m => ModuleCat.ofHom (logFormsCechDiffLinear hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰 m))
    (fun m => by
      rw [cechComplexLinear_d, cechComplexLinear_d]
      exact ModuleCat.hom_ext (LinearMap.ext fun f =>
        TopCat.Presheaf.cechD_cechCochainMap 𝒰 (logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b) f))

theorem logFormsCechDiffLinearMap_comp (hsnc : IsSNCFamily K n ξ) (p : ℕ) [CharP K p]
    (c₀ : EtaleChart K X n) (M : CartierDivisor X) (rr : Fin r → ℕ) (b : ℕ) {N : ℕ}
    (𝒰 : Fin N → X.Opens) :
    logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b 𝒰 ≫ logFormsCechDiffLinearMap hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (b + 1) 𝒰 = 0 := by
  ext m : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
  refine ModuleCat.hom_ext (LinearMap.ext fun f => funext fun x => ?_)
  change (logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr (b + 1)).app _ ((logFormsDiffPresheaf hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b).app _ (f x)) = 0
  have h := congrArg (fun φ => φ.app (op (TopCat.Presheaf.cechOpen 𝒰 x)) (f x))
    (logFormsDiffPresheaf_comp hnorm ξ hinj hξ E hEc hsnc p c₀ M rr b)
  simpa using h

end Linear

end MixedFujita
