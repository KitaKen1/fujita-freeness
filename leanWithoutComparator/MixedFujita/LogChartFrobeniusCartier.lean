/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogCechDIComponents
public import MixedFujita.PointClosureHyperplaneEquivalence

/-!
The Frobenius lift on logarithmic forms of a chart and the logarithmic inverse Cartier operator
(step 10, R2).

**Twist exponents.** On a simple normal crossing chart, `Σ_k r_k • E_k` has the uniform local
equation `Π_j y_j^{r'_j}`, with the exponents `r'_j = Σ_{σ k = j} r_k` moved from the components
to the coordinates (`isLocalEquationAt_logTwistMonomial`). The exponents stay `< p` when the `r_k`
are (`logTwistExponent_lt`). So `p • M + Σ_k r_k • E_k` has the equation whose inverse is the twist
weight of check 482.

**The Frobenius lift on model forms.** Let `F` be a Frobenius lift on a localized chart `c'` with
`Φ_F(θ'_i) = C₀(θ_i)` exactly, where `C₀(θ_i) = θ_i` in the logarithmic directions and
`y_i^{p-1} θ_i` otherwise (this holds for the coordinate Frobenius `F(ỹ) = ỹ^p`). Then `Φ_F` maps
the wedge of the local logarithmic basis over `t` to `Π_{i ∈ t} C₀(θ_i)` times the logarithmic
wedge (`kaehlerExteriorMap_frobeniusLiftExterior_localLogBasis`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
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

section Exponents

variable {r : ℕ} (σ : Fin r → Option (Fin n)) (rr : Fin r → ℕ)

/-- **The coordinate exponents of `Σ_k r_k • E_k`** on a simple normal crossing chart. -/
def logTwistExponent (j : Fin n) : ℕ :=
  ∑ k, if σ k = some j then rr k else 0

variable {σ rr} in
theorem logTwistExponent_lt (hσ : ∀ i j a, σ i = some a → σ j = some a → i = j) {p : ℕ}
    (hp : 0 < p) (hrr : ∀ k, rr k < p) (j : Fin n) : logTwistExponent σ rr j < p := by
  by_cases h : ∃ k, σ k = some j
  · obtain ⟨k, hk⟩ := h
    rw [logTwistExponent, Finset.sum_eq_single k]
    · simp only [hk, ↓reduceIte]
      exact hrr k
    · intro k' _ hk'
      have hne : ¬ σ k' = some j := fun h' => hk' (hσ k' k j h' hk)
      simp only [hne, ↓reduceIte]
    · intro h'
      exact absurd (Finset.mem_univ k) h'
  · rw [logTwistExponent, Finset.sum_eq_zero]
    · exact hp
    · intro k _
      have hne : ¬ σ k = some j := fun h' => h ⟨k, h'⟩
      simp only [hne, ↓reduceIte]

end Exponents

section Equations

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) (rr : Fin r → ℕ)

/-- **`Π_k (equation of E_k)^{r_k}` is the monomial of the coordinate exponents.** -/
theorem prod_sncChartComponentEquation_pow :
    ∏ k, ((sncChartComponentEquation c σ k : X.functionFieldˣ) : X.functionField) ^ rr k =
      (logTwistMonomial c (logSetOf σ) (logTwistExponent σ rr) : X.functionField) := by
  have h1 : ∀ k, ((sncChartComponentEquation c σ k : X.functionFieldˣ) : X.functionField) ^ rr k =
      ∏ j, (etaleChartCoordinateRationalUnit c j : X.functionField) ^
        (if σ k = some j then rr k else 0) := by
    intro k
    cases hk : σ k with
    | none =>
      simp only [sncChartComponentEquation, hk, Option.elim_none, Units.val_one, one_pow,
        reduceCtorEq, ↓reduceIte, pow_zero, Finset.prod_const_one]
    | some j₀ =>
      rw [sncChartComponentEquation, hk, Option.elim_some, Finset.prod_eq_single j₀]
      · simp only [↓reduceIte]
      · intro j _ hj
        have hne : ¬ (some j₀ = some j) := fun h' => hj (Option.some_injective _ h').symm
        simp only [hne, ↓reduceIte, pow_zero]
      · intro h'
        exact absurd (Finset.mem_univ j₀) h'
  rw [Finset.prod_congr rfl fun k _ => h1 k, Finset.prod_comm]
  have h2 : ∀ j, ∏ k, (etaleChartCoordinateRationalUnit c j : X.functionField) ^
      (if σ k = some j then rr k else 0) =
      (etaleChartCoordinateRationalUnit c j : X.functionField) ^ logTwistExponent σ rr j := by
    intro j
    rw [Finset.prod_pow_eq_pow_sum, logTwistExponent]
  rw [Finset.prod_congr rfl fun j _ => h2 j, logTwistMonomial, Units.coe_prod]
  symm
  refine Finset.prod_subset (Finset.subset_univ _) fun j _ hj => ?_
  have h0 : logTwistExponent σ rr j = 0 := by
    rw [logTwistExponent]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : ¬ σ k = some j := fun h' => hj ((mem_logSetOf σ j).mpr ⟨k, h'⟩)
    simp only [hne, ↓reduceIte]
  rw [h0, pow_zero, Units.val_one]

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (hc : IsSNCChart c ξ σ)

include hnorm hinj hξ hEc hc in
/-- **The monomial of the coordinate exponents is a local equation of `Σ_k r_k • E_k`** at every
point of a simple normal crossing chart. -/
theorem isLocalEquationAt_logTwistMonomial (x : X) (hx : x ∈ c.U) :
    (∑ k, rr k • E k).IsLocalEquationAt x
      (logTwistMonomial c (logSetOf σ) (logTwistExponent σ rr)) := by
  choose h hh u hu using fun k =>
    exists_isLocalEquationAt_eq_unit_mul_sncChartComponentEquation hnorm ξ hinj hξ E hEc c σ hc x
      hx k
  have h1 : ∀ T : Finset (Fin r),
      (∑ k ∈ T, rr k • E k).IsLocalEquationAt x (∏ k ∈ T, h k ^ rr k) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.prod_empty]
      exact CartierDivisor.isLocalEquationAt_zero x
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact (isLocalEquationAt_nsmul_pow (hh a) (rr a)).mul ih
  refine isLocalEquationAt_stalkUnit_mul (h1 Finset.univ) (∏ k, (u k)⁻¹ ^ rr k) ?_
  have h2 : ((∏ k, h k ^ rr k : X.functionFieldˣ) : X.functionField) =
      algebraMap (X.presheaf.stalk x) X.functionField ((∏ k, u k ^ rr k : (X.presheaf.stalk x)ˣ) :
        X.presheaf.stalk x) *
        (logTwistMonomial c (logSetOf σ) (logTwistExponent σ rr) : X.functionField) := by
    rw [← prod_sncChartComponentEquation_pow, Units.coe_prod, Units.coe_prod, map_prod,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_pow_eq_pow_val, hu k, mul_pow, Units.val_pow_eq_pow_val, map_pow]
  rw [h2, ← mul_assoc, ← map_mul, ← Units.val_mul, ← Finset.prod_mul_distrib]
  have h3 : ∏ k, ((u k)⁻¹ ^ rr k * u k ^ rr k) = 1 :=
    Finset.prod_eq_one fun k _ => by rw [← mul_pow, inv_mul_cancel, one_pow]
  rw [h3, Units.val_one, map_one, one_mul]

include hnorm hinj hξ hEc hc in
/-- **The inverse of the twist weight of check 482 is a local equation of
`p • M + Σ_k r_k • E_k`** at every point of the chart, for a uniform equation `g` of `M`. -/
theorem isLocalEquationAt_logTwistWeight (p : ℕ) (M : CartierDivisor X) {g : X.functionFieldˣ}
    (hg : ∀ x ∈ c.U, M.IsLocalEquationAt x g) (x : X) (hx : x ∈ c.U) :
    (p • M + ∑ k, rr k • E k).IsLocalEquationAt x
      (g ^ p * logTwistMonomial c (logSetOf σ) (logTwistExponent σ rr)) :=
  (isLocalEquationAt_nsmul_pow (hg x hx) p).mul
    (isLocalEquationAt_logTwistMonomial c σ rr hnorm ξ hinj hξ E hEc hc x hx)

end Equations

theorem list_ofFn_prod_smul {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {m : ℕ}
    (a : Fin m → R) (v : Fin m → A) :
    (List.ofFn fun i => a i • v i).prod = (∏ i, a i) • (List.ofFn v).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ,
      ih (fun i => a i.succ) (fun i => v i.succ), smul_mul_smul_comm]


theorem prod_ofFinEmbEquiv_symm {M : Type*} [CommMonoid M] {b : ℕ} (t : Set.powersetCard (Fin n) b)
    (f : Fin n → M) : ∏ i, f (Set.powersetCard.ofFinEmbEquiv.symm t i) = ∏ j ∈ t.1, f j := by
  have h : (Set.powersetCard.ofFinEmbEquiv.symm t) = Finset.orderEmbOfFin t.1 t.2 := rfl
  rw [h]
  calc ∏ i, f ((Finset.orderEmbOfFin t.1 t.2) i) =
        ∏ j ∈ Finset.univ.map (Finset.orderEmbOfFin t.1 t.2).toEmbedding, f j :=
      (Finset.prod_map _ _ _).symm
    _ = ∏ j ∈ t.1, f j := by rw [Finset.map_orderEmbOfFin_univ]

/-- The coordinates of a monomial, in `K(X)`. -/
theorem sectionGermAlgHom_coords_monomial (c : EtaleChart K X n) (s : Fin n →₀ ℕ) :
    sectionGermAlgHom (K := K) c.U (c.coords (MvPolynomial.monomial s 1)) =
      ∏ j, (etaleChartCoordinateRationalUnit c j : X.functionField) ^ (s j) := by
  have h := MvPolynomial.aeval_unique c.coords
  rw [h, MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [map_pow]
  rfl

section Frobenius

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n)) (c' : EtaleChart K X n)
  (hunit : ∀ j ∈ logSetOf σ, IsUnit (c'.coords (MvPolynomial.X j)))
  {L : Type w} [CommRing L] (π : L →+* Γ(X, c'.U)) (hπ : Function.Surjective π) (p : ℕ)
  [Fact p.Prime] [CharP K p] (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p)
  (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z)

/-- The coefficient of `C₀(θ_j)`: `1` in the logarithmic directions, `y_j^{p-1}` otherwise. -/
noncomputable def logCartierCoeff (j : Fin n) : X.functionField :=
  if j ∈ logSetOf σ then 1 else (etaleChartCoordinateRationalUnit c j : X.functionField) ^ (p - 1)

omit [IsIntegral X] in
theorem frobeniusLiftExterior_ofFn_prod {m : ℕ} (v : Fin m → Ω[Γ(X, c'.U)⁄K]) :
    frobeniusLiftExterior c'.coords c'.formallyEtale π hπ p F hF hker ((List.ofFn fun i => ExteriorAlgebra.ι Γ(X, c'.U) (v i)).prod) =
      (List.ofFn fun i => ExteriorAlgebra.ι Γ(X, c'.U) (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p F hF hker (v i))).prod := by
  induction m with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil]
    exact frobeniusLiftExterior_one _ _ _ _ _ _ _ _
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, frobeniusLiftExterior_mul, frobeniusLiftExterior_ι,
      ih (fun i => v i.succ), List.ofFn_succ, List.prod_cons]

variable (hcoords : ∀ j, sectionGermAlgHom (K := K) c'.U (c'.coords (MvPolynomial.X j)) =
    (etaleChartCoordinateRationalUnit c j : X.functionField))
  (hΦ0 : ∀ i, KaehlerDifferential.map K K Γ(X, c'.U) X.functionField
    (frobeniusLiftOneFormAux c'.coords c'.formallyEtale π hπ p F hF hker (localLogBasis σ c' hunit i)) = logCartierCoeff c σ p i • logChartBasis c σ i)

include hΦ0 in
/-- **The Frobenius lift on the wedges of the local logarithmic basis**:
`Φ_F(θ'_t) = (Π_{i ∈ t} C₀_i) θ_t`. -/
theorem kaehlerExteriorMap_frobeniusLiftExterior_localLogBasis (b : ℕ)
    (t : Set.powersetCard (Fin n) b) :
    kaehlerExteriorMap K Γ(X, c'.U) X.functionField (frobeniusLiftExterior c'.coords c'.formallyEtale π hπ p F hF hker
        (((localLogBasis σ c' hunit).exteriorPower b t : ⋀[Γ(X, c'.U)]^b Ω[Γ(X, c'.U)⁄K]) :
          ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K])) =
      (∏ i, logCartierCoeff c σ p (Set.powersetCard.ofFinEmbEquiv.symm t i)) •
        (logChartBasis c σ).ExteriorAlgebra t.1 := by
  have h := ExteriorAlgebra.basis_eq_coe_basis (logChartBasis c σ) t
  rw [h, exteriorPower.basis_apply, exteriorPower.basis_apply, exteriorPower.ιMulti_family_apply_coe,
    exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, frobeniusLiftExterior_ofFn_prod,
    map_list_prod, List.map_ofFn, ← list_ofFn_prod_smul]
  congr 2
  funext i
  simp only [Function.comp_apply, kaehlerExteriorMap_ι, hΦ0, map_smul]


include hcoords in
/-- The wedges of the local logarithmic basis give the logarithmic wedge basis. -/
theorem sectionFormsMap_localLogBasis_exteriorPower (b : ℕ) (t : Set.powersetCard (Fin n) b) :
    sectionFormsMap (K := K) c'.U b ((localLogBasis σ c' hunit).exteriorPower b t) =
      logChartFormsBasis c σ b t := by
  apply Subtype.ext
  rw [sectionFormsMap_coe, kaehlerExteriorMap_localLogBasis_exteriorPower c σ c' hunit hcoords b t]
  exact ExteriorAlgebra.basis_eq_coe_basis (logChartBasis c σ) t

include hcoords in
/-- **The coefficients of the regular twist `g ω` in the local logarithmic wedge basis are the
model coefficients.** -/
theorem localLogBasis_repr_twistToRegularForms {M : CartierDivisor X} {g : X.functionFieldˣ}
    (hg : ∀ x ∈ c'.U, M.IsLocalEquationAt x g) {b : ℕ}
    (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) (ω : twistedFormsSections K M b c'.U)
    (hω : rationalFormsSectionsEquiv K b c'.U ω.1 =
      logChartModelForm c σ ((g⁻¹ : X.functionFieldˣ) : X.functionField) a)
    (t : Set.powersetCard (Fin n) b) :
    sectionGermAlgHom (K := K) c'.U (((localLogBasis σ c' hunit).exteriorPower b).repr
        (chartFormsEquiv c' b (twistToRegularForms c' hg ω)) t) =
      sectionGermAlgHom (K := K) c.U (a t) := by
  have h1 : sectionFormsMap (K := K) c'.U b (chartFormsEquiv c' b (twistToRegularForms c' hg ω)) =
      ∑ t, sectionGermAlgHom (K := K) c.U (a t) • logChartFormsBasis c σ b t := by
    rw [sectionFormsMap_chartFormsEquiv, regularFormsValue_apply, twistToRegularForms_val, hω,
      smul_logChartModelForm_inv c σ b a]
  have h2 : sectionFormsMap (K := K) c'.U b (chartFormsEquiv c' b (twistToRegularForms c' hg ω)) =
      ∑ t, sectionGermAlgHom (K := K) c'.U (((localLogBasis σ c' hunit).exteriorPower b).repr
        (chartFormsEquiv c' b (twistToRegularForms c' hg ω)) t) • logChartFormsBasis c σ b t := by
    conv_lhs => rw [← ((localLogBasis σ c' hunit).exteriorPower b).sum_repr
      (chartFormsEquiv c' b (twistToRegularForms c' hg ω))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_smul, sectionFormsMap_localLogBasis_exteriorPower c σ c' hunit hcoords b t,
      ← algebraMap_smul X.functionField]
    rfl
  have h3 := congrArg (fun z => (logChartFormsBasis c σ b).repr z t) (h2.symm.trans h1)
  simp only [Module.Basis.repr_sum_self] at h3
  exact h3

omit [IsIntegral X] in
theorem frobeniusLiftExterior_finset_sum {ι : Type*} (T : Finset ι)
    (f : ι → ExteriorAlgebra Γ(X, c'.U) Ω[Γ(X, c'.U)⁄K]) :
    frobeniusLiftExterior c'.coords c'.formallyEtale π hπ p F hF hker (∑ i ∈ T, f i) = ∑ i ∈ T, frobeniusLiftExterior c'.coords c'.formallyEtale π hπ p F hF hker (f i) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact frobeniusLiftExterior_zero _ _ _ _ _ _ _ _
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, frobeniusLiftExterior_add, ih]

include hcoords hΦ0 in
/-- **The Frobenius lift of the regular twist of a model form**, in the logarithmic wedge basis. -/
theorem rationalFormsSectionsEquiv_chartFrobeniusLiftForms_model {M : CartierDivisor X}
    {g : X.functionFieldˣ} (hg : ∀ x ∈ c'.U, M.IsLocalEquationAt x g) {b : ℕ}
    (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) (ω : twistedFormsSections K M b c'.U)
    (hω : rationalFormsSectionsEquiv K b c'.U ω.1 =
      logChartModelForm c σ ((g⁻¹ : X.functionFieldˣ) : X.functionField) a) :
    rationalFormsSectionsEquiv K b c'.U
        (chartFrobeniusLiftForms c' π hπ p F hF hker b (twistToRegularForms c' hg ω)).1 =
      ∑ t, (sectionGermAlgHom (K := K) c.U (a t) ^ p *
        ∏ i, logCartierCoeff c σ p (Set.powersetCard.ofFinEmbEquiv.symm t i)) •
          logChartFormsBasis c σ b t := by
  rw [← regularFormsValue_apply, ← sectionFormsMap_chartFormsEquiv]
  apply Subtype.ext
  rw [sectionFormsMap_coe, chartFormsEquiv_chartFrobeniusLiftForms]
  conv_lhs => rw [← ((localLogBasis σ c' hunit).exteriorPower b).sum_repr
    (chartFormsEquiv c' b (twistToRegularForms c' hg ω))]
  rw [Submodule.coe_sum, frobeniusLiftExterior_finset_sum, map_sum, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Submodule.coe_smul, frobeniusLiftExterior_smul, map_smul,
    kaehlerExteriorMap_frobeniusLiftExterior_localLogBasis c σ c' hunit π hπ p F hF hker hΦ0 b t,
    Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis, ← algebraMap_smul X.functionField,
    smul_smul, map_pow, ← localLogBasis_repr_twistToRegularForms c σ c' hunit hcoords hg a ω hω t]
  rfl


omit [Fact p.Prime] [CharP K p] in
/-- **The exponents of the logarithmic inverse Cartier operator**:
`y^{β(t)} = y^r Π_{i ∈ t} C₀_i`. -/
theorem prod_logCartierExponent (rr : Fin n → ℕ) {b : ℕ} (t : Set.powersetCard (Fin n) b) :
    ∏ j, (etaleChartCoordinateRationalUnit c j : X.functionField) ^
        (logCartierExponent p (logSetOf σ) rr t.1 j) =
      (logTwistMonomial c (logSetOf σ) rr : X.functionField) *
        ∏ i, logCartierCoeff c σ p (Set.powersetCard.ofFinEmbEquiv.symm t i) := by
  have hsplit : ∀ j, (etaleChartCoordinateRationalUnit c j : X.functionField) ^
      (logCartierExponent p (logSetOf σ) rr t.1 j) =
      (if j ∈ logSetOf σ then (etaleChartCoordinateRationalUnit c j : X.functionField) ^ rr j
        else 1) * (if j ∈ t.1 then logCartierCoeff c σ p j else 1) := by
    intro j
    rw [logCartierExponent_apply, logCartierCoeff]
    by_cases hA : j ∈ logSetOf σ <;> by_cases ht : j ∈ t.1 <;> simp [hA, ht]
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter, prod_ofFinEmbEquiv_symm,
    logTwistMonomial, Units.coe_prod]
  congr 1

include hcoords hΦ0 in
/-- **On model forms the twisted Frobenius lift is the logarithmic inverse Cartier operator**:
for `ω = Σ_t (a_t g⁻¹) θ_t`, `Φ_{p•M}(ω) = C⁻¹(a)` with the twist weight of check 482 (for any
exponents `r`). -/
theorem rationalFormsSectionsEquiv_twistedChartFrobeniusLiftForms_model {M : CartierDivisor X}
    {g : X.functionFieldˣ} (hg : ∀ x ∈ c'.U, M.IsLocalEquationAt x g) (rr : Fin n → ℕ) {b : ℕ}
    (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) (ω : twistedFormsSections K M b c'.U)
    (hω : rationalFormsSectionsEquiv K b c'.U ω.1 =
      logChartModelForm c σ ((g⁻¹ : X.functionFieldˣ) : X.functionField) a) :
    rationalFormsSectionsEquiv K b c'.U
        (twistedChartFrobeniusLiftForms c' π hπ p F hF hker hg b ω).1 =
      logChartInverseCartierForm c σ p rr (logTwistWeight c σ p rr g) a := by
  rw [twistedChartFrobeniusLiftForms_val,
    rationalFormsSectionsEquiv_chartFrobeniusLiftForms_model c σ c' hunit π hπ p F hF hker hcoords
      hΦ0 hg a ω hω, logChartInverseCartierForm, logChartModelForm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul]
  congr 1
  rw [map_mul, map_pow, sectionGermAlgHom_coords_monomial, prod_logCartierExponent c σ p rr t,
    logTwistWeight, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val]
  have hg0 := g.ne_zero
  have hm0 := (logTwistMonomial c (logSetOf σ) rr).ne_zero
  field_simp
  have hgp : ((1 : X.functionField) / g) ^ p * (g : X.functionField) ^ p = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀ _ (pow_ne_zero _ hg0)]
  linear_combination (sectionGermAlgHom (K := K) c.U (a t) ^ p *
    ∏ i, logCartierCoeff c σ p (Set.powersetCard.ofFinEmbEquiv.symm t i)) * hgp

end Frobenius

end MixedFujita
