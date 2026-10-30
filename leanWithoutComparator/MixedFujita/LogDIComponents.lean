/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogRegularForms
public import MixedFujita.TwistedChartDIComponent
public import MixedFujita.KaehlerDeRhamFunctoriality

/-!
The Deligne–Illusie components preserve logarithmic forms (step 10, R2).

Let `c` be an étale chart with logarithmic directions `A = σ(Fin r)`, and `c'` a chart whose
coordinates have the same germs as those of `c` and are units in the logarithmic directions (the
complement of the boundary in `c`). The local logarithmic generators `θ'_j` of `c'`
(`localLogGenerator`) map to the logarithmic basis `θ_j` of `c` (`map_localLogGenerator`), and form
a basis of the `1`-forms of `c'` (`localLogBasis`).

Assume lift data modulo `p²` on `c'` such that the Frobenius lift forms `Φ_{F_j}(θ'_i)` have
regular logarithmic coefficients on `c` and the homotopies `h_{j j'}(θ'_i)` are regular on `c`.
Then the components of the degree-`1` Deligne–Illusie cocycles of the `θ'_i`
(`logRegular_diSeqCocycle`), of their products (`logRegular_diSeqProd`, the products of check 451
being sums of products and grade involutions) and of the Deligne–Illusie map on `b`-forms
(`logRegular_diSeqAlt`) are log-regular on `c` for every `b`-form of `c'` that is log-regular on
`c`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u w

attribute [local instance] Classical.propDecidable

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

section Generators

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) (c' : EtaleChart K X n)
  (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))

theorem algebraMap_section_eq_sectionGermAlgHom (U : X.Opens) [Nonempty U] (a : Γ(X, U)) :
    algebraMap Γ(X, U) X.functionField a = sectionGermAlgHom (K := K) U a := rfl

/-- The weights of the local logarithmic basis: the inverse coordinate in the logarithmic
directions. -/
noncomputable def localLogWeight (j : Fin n) : Γ(X, c'.U)ˣ :=
  if h : j ∈ logSetOf σ then (hunit j h).unit⁻¹ else 1

/-- **The local logarithmic basis** `dy_j / y_j` (`j ∈ A`), `dy_j` (`j ∉ A`) of the `1`-forms of
`c'`. -/
noncomputable def localLogBasis : Module.Basis (Fin n) Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K] :=
  (etaleCoordinateBasis c'.coords c'.formallyEtale).unitsSMul (localLogWeight σ c' hunit)

variable (hcoords : ∀ j, sectionGermAlgHom (K := K) c'.U (c'.coords (MvPolynomial.X j)) =
  (etaleChartCoordinateRationalUnit c j : X.functionField))

include hcoords in
/-- **The local logarithmic generators map to the logarithmic basis.** -/
theorem map_localLogBasis (j : Fin n) :
    KaehlerDifferential.map K K Γ(X, c'.U) X.functionField (localLogBasis σ c' hunit j) =
      logChartBasis c σ j := by
  rw [localLogBasis, Module.Basis.unitsSMul_apply, etaleCoordinateBasis_apply, localLogWeight]
  have hD : KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
      (KaehlerDifferential.D K Γ(X, c'.U) (c'.coords (MvPolynomial.X j))) =
        KaehlerDifferential.D K X.functionField
          (etaleChartCoordinateRationalUnit c j : X.functionField) := by
    rw [KaehlerDifferential.map_D, algebraMap_section_eq_sectionGermAlgHom (K := K), hcoords]
  by_cases hj : j ∈ logSetOf σ
  · simp only [hj, ↓reduceDIte]
    rw [Units.smul_def, LinearMap.map_smul_of_tower, hD,
      logChartBasis_apply_of_mem c σ ((mem_logSetOf σ j).mp hj), rationalDlog,
      ← algebraMap_smul X.functionField]
    congr 1
    have h1 : algebraMap Γ(X, c'.U) X.functionField
        (((hunit j hj).unit⁻¹ : Γ(X, c'.U)ˣ) : Γ(X, c'.U)) *
          (etaleChartCoordinateRationalUnit c j : X.functionField) = 1 := by
      rw [← hcoords j, ← algebraMap_section_eq_sectionGermAlgHom (K := K), ← map_mul,
        IsUnit.val_inv_mul, map_one]
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left h1
  · simp only [hj, ↓reduceDIte]
    rw [one_smul, hD,
      logChartBasis_apply_of_not_mem c σ (fun h => hj ((mem_logSetOf σ j).mpr h)),
      etaleChartBasis_apply_eq]

include hcoords in
/-- The wedges of the local logarithmic basis map to the exterior basis of the logarithmic basis. -/
theorem kaehlerExteriorMap_localLogBasis_exteriorPower (b : ℕ) (t : Set.powersetCard (Fin n) b) :
    kaehlerExteriorMap K Γ(X, c'.U) X.functionField
        (((localLogBasis σ c' hunit).exteriorPower b t : ⋀[Γ(X, c'.U)]^b Ω[Γ(X, c'.U)⁄K]) :
          ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]) =
      (logChartBasis c σ).ExteriorAlgebra t.1 := by
  have h := ExteriorAlgebra.basis_eq_coe_basis (logChartBasis c σ) t
  rw [h, exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
    exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, kaehlerExteriorMap_ι, map_localLogBasis c σ c' hunit hcoords]

end Generators

section Components

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) (c' : EtaleChart K X n)

/-- A form of `c'` whose rational form is log-regular on `c`. -/
def LogRegularOn (z : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]) : Prop :=
  logChartRegular c σ (kaehlerExteriorMap K Γ(X, c'.U) X.functionField z)

variable {c σ c'}

theorem logRegularOn_add {z z' : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]}
    (hz : LogRegularOn c σ c' z) (hz' : LogRegularOn c σ c' z') : LogRegularOn c σ c' (z + z') := by
  unfold LogRegularOn
  rw [map_add]
  exact logChartRegular_add hz hz'

theorem logRegularOn_zsmul (k : ℤ) {z : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]}
    (hz : LogRegularOn c σ c' z) : LogRegularOn c σ c' (k • z) := by
  unfold LogRegularOn
  rw [map_zsmul]
  exact logChartRegular_zsmul k hz

theorem logRegularOn_mul {z z' : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]}
    (hz : LogRegularOn c σ c' z) (hz' : LogRegularOn c σ c' z') : LogRegularOn c σ c' (z * z') := by
  unfold LogRegularOn
  rw [map_mul]
  exact logChartRegular_mul hz hz'

theorem logRegularOn_sum {ι : Type*} (T : Finset ι)
    {f : ι → ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]}
    (hf : ∀ i ∈ T, LogRegularOn c σ c' (f i)) : LogRegularOn c σ c' (∑ i ∈ T, f i) := by
  unfold LogRegularOn
  rw [map_sum]
  exact logChartRegular_sum T hf

theorem kaehlerExteriorMap_exteriorInvolute (z : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]) :
    kaehlerExteriorMap K Γ(X, c'.U) X.functionField (exteriorInvolute K Γ(X, c'.U) z) =
      exteriorInvolute K X.functionField (kaehlerExteriorMap K Γ(X, c'.U) X.functionField z) := by
  induction z using ExteriorAlgebra.induction with
  | algebraMap a =>
    simp only [exteriorInvolute_apply, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply Γ(X, c'.U) X.functionField
      (ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) a, AlgHom.commutes]
  | ι v => rw [exteriorInvolute_ι, map_neg, kaehlerExteriorMap_ι, exteriorInvolute_ι]
  | mul x z hx hz => rw [map_mul, map_mul, hx, hz, map_mul, map_mul]
  | add x z hx hz => rw [map_add, map_add, hx, hz, map_add, map_add]

theorem logRegularOn_involute_pow (k : ℕ) {z : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]}
    (hz : LogRegularOn c σ c' z) :
    LogRegularOn c σ c' ((exteriorInvolute K Γ(X, c'.U) ^ k) z) := by
  induction k generalizing z with
  | zero => exact hz
  | succ k ih =>
    rw [pow_succ]
    change LogRegularOn c σ c' ((exteriorInvolute K Γ(X, c'.U) ^ k)
      (exteriorInvolute K Γ(X, c'.U) z))
    refine ih ?_
    unfold LogRegularOn
    rw [kaehlerExteriorMap_exteriorInvolute]
    exact logChartRegular_involute hz

variable (c σ c') (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c'.U)) (hπ : Function.Surjective π) (p : ℕ)
  [Fact p.Prime] [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hΦ : ∀ (j : J) (i : Fin n) (t : Fin n), (logChartBasis c σ).repr
      (KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
        (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p (F j) (hF j) hker
          (localLogBasis σ c' hunit i))) t ∈ chartRegularFunctions c)
  (hH : ∀ (j j' : J) (i : Fin n), algebraMap Γ(X, c'.U) X.functionField
      (frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π hπ p (F j) (F j') (hF j) (hF j') hker
        (localLogBasis σ c' hunit i)) ∈ chartRegularFunctions c)

omit [Fact p.Prime] [CharP K p] in
include hΦ hH in
/-- **The degree-`1` Deligne–Illusie cocycles of the local logarithmic generators are
log-regular.** -/
theorem logRegularOn_diSeqCocycle (i : Fin n) (a : ℕ) (s : ℕ → J) :
    LogRegularOn c σ c' (diSeqCocycle c'.coords c'.formallyEtale π hπ p F hF hker
      (localLogBasis σ c' hunit i) a s) := by
  rcases a with _ | _ | a
  · change logChartRegular c σ (kaehlerExteriorMap K Γ(X, c'.U) X.functionField
      (ExteriorAlgebra.ι _ (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p (F (s 0))
        (hF (s 0)) hker (localLogBasis σ c' hunit i))))
    rw [kaehlerExteriorMap_ι]
    exact logChartRegular_ι (hΦ (s 0) i)
  · change logChartRegular c σ (kaehlerExteriorMap K Γ(X, c'.U) X.functionField
      (algebraMap Γ(X, c'.U) _ (frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π hπ p (F (s 0))
        (F (s 1)) (hF (s 0)) (hF (s 1)) hker (localLogBasis σ c' hunit i))))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply Γ(X, c'.U) X.functionField
      (ExteriorAlgebra X.functionField Ω[X.functionField⁄K])]
    exact logChartRegular_algebraMap (hH (s 0) (s 1) i)
  · change logChartRegular c σ (kaehlerExteriorMap K Γ(X, c'.U) X.functionField 0)
    rw [map_zero]
    exact logChartRegular_zero c σ

omit [Fact p.Prime] [CharP K p] in
include hΦ hH in
/-- **The products of the cocycles of local logarithmic generators are log-regular.** -/
theorem logRegularOn_diSeqProd (l : List (Fin n)) (a : ℕ) (s : ℕ → J) :
    LogRegularOn c σ c' (diSeqProd c'.coords c'.formallyEtale π hπ p F hF hker
      (l.map (localLogBasis σ c' hunit)) a s) := by
  induction l generalizing a s with
  | nil =>
    rcases a with _ | a
    · change logChartRegular c σ (kaehlerExteriorMap K Γ(X, c'.U) X.functionField 1)
      rw [map_one]
      exact logChartRegular_one c σ
    · change logChartRegular c σ (kaehlerExteriorMap K Γ(X, c'.U) X.functionField 0)
      rw [map_zero]
      exact logChartRegular_zero c σ
  | cons i l ih =>
    change LogRegularOn c σ c' (seqTotalMul (exteriorInvolute K Γ(X, c'.U))
      (diSeqCocycle c'.coords c'.formallyEtale π hπ p F hF hker (localLogBasis σ c' hunit i))
      (diSeqProd c'.coords c'.formallyEtale π hπ p F hF hker (l.map (localLogBasis σ c' hunit)))
      a s)
    unfold seqTotalMul
    exact logRegularOn_sum _ fun x _ => logRegularOn_mul (logRegularOn_involute_pow _
      (logRegularOn_diSeqCocycle c σ c' hunit π hπ p F hF hker hΦ hH i _ _)) (ih _ _)

include hΦ hH in
/-- **The Deligne–Illusie map of a wedge of local logarithmic generators is log-regular.** -/
theorem logRegularOn_diSeqAlt_basis (b : ℕ) (t : Set.powersetCard (Fin n) b) (a : ℕ) (s : ℕ → J) :
    LogRegularOn c σ c' (twistedPiHom K Γ(X, c'.U) p J (diSeqAlt c'.coords c'.formallyEtale π hπ p F
      hF hker b ((localLogBasis σ c' hunit).exteriorPower b t)) a s) := by
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, diSeqAlt_ιMulti, map_sum,
    Finset.sum_apply, Finset.sum_apply]
  refine logRegularOn_sum _ fun τ _ => ?_
  rw [Units.smul_def, map_zsmul, Pi.smul_apply, Pi.smul_apply]
  refine logRegularOn_zsmul _ ?_
  change LogRegularOn c σ c' (diSeqProd c'.coords c'.formallyEtale π hπ p F hF hker
    (List.ofFn fun i => ((localLogBasis σ c' hunit) ∘ (Set.powersetCard.ofFinEmbEquiv.symm t)) (τ i))
      a s)
  have hl : (List.ofFn fun i => ((localLogBasis σ c' hunit) ∘
      (Set.powersetCard.ofFinEmbEquiv.symm t)) (τ i)) =
      (List.ofFn fun i => (Set.powersetCard.ofFinEmbEquiv.symm t) (τ i)).map
        (localLogBasis σ c' hunit) := by
    rw [List.map_ofFn]
    rfl
  rw [hl]
  exact logRegularOn_diSeqProd c σ c' hunit π hπ p F hF hker hΦ hH _ a s

variable (hcoords : ∀ j, sectionGermAlgHom (K := K) c'.U (c'.coords (MvPolynomial.X j)) =
  (etaleChartCoordinateRationalUnit c j : X.functionField))

include hΦ hH hcoords in
/-- **The Deligne–Illusie map preserves log-regularity.** -/
theorem logRegularOn_diSeqAlt (b : ℕ) (x : ⋀[Γ(X, c'.U)]^b Ω[Γ(X, c'.U)⁄K])
    (hx : LogRegularOn c σ c' (x : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K])) (a : ℕ)
    (s : ℕ → J) :
    LogRegularOn c σ c' (twistedPiHom K Γ(X, c'.U) p J (diSeqAlt c'.coords c'.formallyEtale π hπ p F
      hF hker b x) a s) := by
  have hφ : kaehlerExteriorMap K Γ(X, c'.U) X.functionField
      (x : ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]) =
        ∑ t, algebraMap Γ(X, c'.U) X.functionField
          (((localLogBasis σ c' hunit).exteriorPower b).repr x t) •
            (logChartBasis c σ).ExteriorAlgebra t.1 := by
    conv_lhs => rw [← ((localLogBasis σ c' hunit).exteriorPower b).sum_repr x]
    rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Submodule.coe_smul, kaehlerExteriorMap_smul,
      kaehlerExteriorMap_localLogBasis_exteriorPower c σ c' hunit hcoords]
  have hcoef : ∀ t, algebraMap Γ(X, c'.U) X.functionField
      (((localLogBasis σ c' hunit).exteriorPower b).repr x t) ∈ chartRegularFunctions c := by
    intro t
    have h := hx t.1
    rw [hφ, map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single t] at h
    · rwa [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
        smul_eq_mul, mul_one] at h
    · intro t' _ ht'
      rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
        ite_eq_right_iff.mpr (fun h => absurd (Subtype.ext h) ht'), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ t) h
  conv => enter [4]; rw [← ((localLogBasis σ c' hunit).exteriorPower b).sum_repr x]
  rw [map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  refine logRegularOn_sum _ fun t _ => ?_
  rw [LinearMap.map_smul, twistedPiHom_smul]
  unfold LogRegularOn
  rw [kaehlerExteriorMap_smul, map_pow]
  exact logChartRegular_smul (Subalgebra.pow_mem _ (hcoef t) p)
    (logRegularOn_diSeqAlt_basis c σ c' hunit π hπ p F hF hker hΦ hH b t a s)

end Components

section Sections

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)

include hnorm hinj hξ hEc hc in
/-- A form which is logarithmic at every point of an SNC chart is log-regular on the chart. -/
theorem logChartRegular_of_forall_mem_logFormsLattice {b : ℕ} (z : RationalForms K X b)
    (hz : ∀ x ∈ c.U, z ∈ logFormsLattice K E x b) :
    logChartRegular c σ (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) := by
  intro s
  by_cases hs : s.card = b
  · have h := logChartFormsBasis_repr_eq c σ z ⟨s, Set.powersetCard.mem_iff.mpr hs⟩
    rw [← h]
    obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range (U := c.U) fun x hx =>
      (mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b z).mp (hz x hx)
        ⟨s, Set.powersetCard.mem_iff.mpr hs⟩
    exact ⟨a, ha⟩
  · have hexp := (logChartFormsBasis c σ b).sum_repr z
    have hcoe := congrArg (fun w : RationalForms K X b =>
      (logChartBasis c σ).ExteriorAlgebra.repr (w : ExteriorAlgebra X.functionField
        Ω[X.functionField⁄K]) s) hexp
    rw [← hcoe, Submodule.coe_sum, map_sum, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero]
    · exact Subalgebra.zero_mem _
    · intro t _
      rw [Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis, map_smul, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply,
        ite_eq_right_iff.mpr (fun h => absurd (by subst h; exact Set.powersetCard.mem_iff.mp t.2) hs),
        smul_zero]

include hnorm hinj hξ hEc hc in
/-- A log-regular `b`-form is logarithmic at every point of the chart. -/
theorem mem_logFormsLattice_of_logChartRegular {b : ℕ} (z : RationalForms K X b)
    (hz : logChartRegular c σ (z : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]))
    (x : X) (hx : x ∈ c.U) : z ∈ logFormsLattice K E x b := by
  refine (mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b z).mpr fun t => ?_
  obtain ⟨a, ha⟩ := logChartFormsBasis_repr_mem_of_logChartRegular c σ hz t
  exact ⟨X.presheaf.germ c.U x hx a,
    (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := c.U) hx a).trans ha⟩

variable (c' : EtaleChart K X n) (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  (hcoords : ∀ j, sectionGermAlgHom (K := K) c'.U (c'.coords (MvPolynomial.X j)) =
    (etaleChartCoordinateRationalUnit c j : X.functionField))
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c'.U)) (hπ : Function.Surjective π) (p : ℕ)
  [Fact p.Prime] [CharP K p] {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)
  (hΦ : ∀ (j : J) (i : Fin n) (t : Fin n), (logChartBasis c σ).repr
      (KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
        (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p (F j) (hF j) hker
          (localLogBasis σ c' hunit i))) t ∈ chartRegularFunctions c)
  (hH : ∀ (j j' : J) (i : Fin n), algebraMap Γ(X, c'.U) X.functionField
      (frobeniusLiftHomotopyAux c'.coords c'.formallyEtale π hπ p (F j) (F j') (hF j) (hF j') hker
        (localLogBasis σ c' hunit i)) ∈ chartRegularFunctions c)
  {M : CartierDivisor X} {g : X.functionFieldˣ} (hg : ∀ x ∈ c'.U, M.IsLocalEquationAt x g)

include hnorm hinj hξ hEc hc hcoords hΦ hH in
/-- **The twisted Deligne–Illusie components of the localized chart preserve logarithmic forms**:
if `g ω` is logarithmic at every point of `c`, then `g^p Θ^{b,a}_s(ω)` is logarithmic at every point
of `c`. -/
theorem twistedChartDIComponent_mem_logFormsLattice (b i a : ℕ) (h : i + a = b) (s : ℕ → J)
    (ω : twistedFormsSections K M b c'.U)
    (hω : ∀ x ∈ c.U, (g : X.functionField) • rationalFormsSectionsEquiv K b c'.U ω.1 ∈
      logFormsLattice K E x b) (x : X) (hx : x ∈ c.U) :
    ((g : X.functionField) ^ p) • rationalFormsSectionsEquiv K i c'.U
        (twistedChartDIComponent c' π hπ p F hF hker hg b i a h s ω).1 ∈
      logFormsLattice K E x i := by
  rw [twistedChartDIComponent_val, smul_smul, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow,
    one_smul, rationalFormsSectionsEquiv_chartFormsEquiv_symm]
  refine mem_logFormsLattice_of_logChartRegular hnorm ξ hinj hξ E hEc c σ hc _ ?_ x hx
  rw [exteriorDifferentialMap_coe, diSeqAltComponent_coe]
  refine logRegularOn_diSeqAlt c σ c' hunit π hπ p F hF hker hΦ hH hcoords b _ ?_ a s
  unfold LogRegularOn
  rw [← exteriorDifferentialMap_coe]
  have hx' : sectionFormsMap (K := K) c'.U b (twistedChartForm c' hg ω) =
      (g : X.functionField) • rationalFormsSectionsEquiv K b c'.U ω.1 := by
    rw [twistedChartForm, sectionFormsMap_chartFormsEquiv, regularFormsValue_apply,
      twistToRegularForms_val]
  rw [hx']
  exact logChartRegular_of_forall_mem_logFormsLattice hnorm ξ hinj hξ E hEc c σ hc _ hω

end Sections

end MixedFujita
