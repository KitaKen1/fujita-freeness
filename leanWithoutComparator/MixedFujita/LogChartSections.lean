/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LogChartModel
public import MixedFujita.LogFormsCoherent
public import MixedFujita.GradedCartierIsomorphism

/-!
Sections of the twisted logarithmic forms on a simple normal crossing chart (step 10, R2).

The coordinate form of degree `b` with coefficients `a_t` (`t` a `b`-element set) is
`Σ_t a_t e_t` (`coordModelOfCoeffs`); the logarithmic inverse Cartier operator of check 478 acts on
its coefficients (`logInverseCartier_coordModelOfCoeffs`).

On a simple normal crossing chart `c` with logarithmic directions `A = σ(Fin r)` (`logSetOf`), the
logarithmic generators of check 479 are the logarithmic basis of check 476
(`logGenerator_logSetOf`), and `e_s ↦ θ_s` sends the coordinate basis to the exterior algebra basis
of the logarithmic basis (`logExteriorMap_coordExteriorBasis`). So the model map with weight `w`
sends the coordinate form with coefficients `a` to the rational `b`-form
`Σ_t (a_t w) θ_t` (`logChartModelForm`, `logChartModelMap_coordModelOfCoeffs`), and the degree-`b`
projection of the image of any coordinate form is the image of its degree-`b` part
(`formsProj_logChartModelMap`).

If `h` is an equation of `N` on the chart, the forms `Σ_t (a_t h⁻¹) θ_t` are exactly the sections of
`Ω^b_X(log E)(N)` over the chart (`logChartModelForm_mem`, `exists_logChartModelForm_eq`), with
unique coefficients (`logChartModelForm_injective`).

With the twist weight `w = (g^p y^r)⁻¹` (`logTwistWeight`), the model map is injective and
intertwines the differentials (checks 478 and 479), so the Cartier isomorphism of check 478 becomes
a statement on the forms of the chart: a closed form `Σ_t (a_t w) θ_t` of degree `b + 1` is
`C⁻¹ y + d(Σ_t (a'_t w) θ_t)` (`logChart_cartier_exists_succ`; in degree `0`, `C⁻¹ y`,
`logChart_cartier_exists_zero`), where `C⁻¹ y = Σ_t (y_t^p y^{β(t)} w) θ_t`
(`logChartInverseCartierForm`), and `C⁻¹ y` is exact only for `y = 0`
(`logChart_cartier_unique_succ`, `logChart_cartier_unique_zero`). The degrees are separated by the
projections of check 421 (`formsProj_succ_rationalDeRhamDiff`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u v

attribute [local instance] Classical.propDecidable

section ModelDegree

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {n : ℕ}

theorem coordExteriorCoeff_tmul_basis (a : S) (u s : Finset (Fin n)) :
    coordExteriorCoeff (a ⊗ₜ[K] coordExteriorBasis K n u) s = if u = s then a else 0 := by
  have h : a ⊗ₜ[K] coordExteriorBasis K n u =
      a • (Algebra.TensorProduct.basis S (coordExteriorBasis K n)) u := by
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [coordExteriorCoeff, h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem coordExteriorCoeff_finset_sum {ι : Type*} (T : Finset ι) (f : ι → S ⊗[K] CoordExterior K n)
    (s : Finset (Fin n)) :
    coordExteriorCoeff (∑ i ∈ T, f i) s = ∑ i ∈ T, coordExteriorCoeff (f i) s := by
  simp only [coordExteriorCoeff, map_sum, Finsupp.finsetSum_apply]

/-- **The coordinate form of degree `b`** `Σ_{|t| = b} a_t e_t`. -/
noncomputable def coordModelOfCoeffs {b : ℕ} (a : Set.powersetCard (Fin n) b → S) :
    S ⊗[K] CoordExterior K n :=
  ∑ t, a t ⊗ₜ[K] coordExteriorBasis K n t.1

theorem coordExteriorCoeff_coordModelOfCoeffs {b : ℕ} (a : Set.powersetCard (Fin n) b → S)
    (s : Finset (Fin n)) :
    coordExteriorCoeff (coordModelOfCoeffs (K := K) a) s =
      if h : s.card = b then a ⟨s, Set.powersetCard.mem_iff.mpr h⟩ else 0 := by
  rw [coordModelOfCoeffs, coordExteriorCoeff_finset_sum]
  simp only [coordExteriorCoeff_tmul_basis]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨s, Set.powersetCard.mem_iff.mpr h⟩]
    · rw [ite_eq_left rfl]
    · intro t _ ht
      rw [ite_eq_right fun hts => ht (Subtype.ext hts)]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · refine Finset.sum_eq_zero fun t _ => ?_
    exact ite_eq_right fun (hts : (t : Finset (Fin n)) = s) =>
      h (hts ▸ Set.powersetCard.mem_iff.mp t.2)

/-- The degree-`b` coefficients of a coordinate form. -/
noncomputable def coordModelCoeffs (b : ℕ) (ω : S ⊗[K] CoordExterior K n) :
    Set.powersetCard (Fin n) b → S :=
  fun t => coordExteriorCoeff ω t.1

theorem eq_of_coordExteriorCoeff_eq {ω η : S ⊗[K] CoordExterior K n}
    (h : ∀ s, coordExteriorCoeff ω s = coordExteriorCoeff η s) : ω = η := by
  rw [← sub_eq_zero]
  exact eq_zero_of_coordExteriorCoeff _ fun s => by rw [coordExteriorCoeff_sub, h s, sub_self]

variable {n : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (A : Finset (Fin n)) (r : Fin n → ℕ)
  (p : ℕ) [Fact p.Prime] [CharP K p]

omit [CharP K p] in
/-- The logarithmic inverse Cartier operator acts on the coefficients. -/
theorem logInverseCartier_coordModelOfCoeffs {b : ℕ} (a : Set.powersetCard (Fin n) b → S) :
    logInverseCartier y p A r (coordModelOfCoeffs (K := K) a) =
      coordModelOfCoeffs (K := K) fun t =>
        a t ^ p * y (MvPolynomial.monomial (logCartierExponent p A r t.1) 1) := by
  apply eq_of_coordExteriorCoeff_eq
  intro s
  rw [coordExteriorCoeff_logInverseCartier, coordExteriorCoeff_coordModelOfCoeffs,
    coordExteriorCoeff_coordModelOfCoeffs]
  split_ifs with h
  · rfl
  · rw [zero_pow (Fact.out : p.Prime).ne_zero, zero_mul]

omit [Fact p.Prime] [CharP K p] in
theorem coordModelCoeffs_logInverseCartier (b : ℕ) (ω : S ⊗[K] CoordExterior K n)
    (t : Set.powersetCard (Fin n) b) :
    coordModelCoeffs b (logInverseCartier y p A r ω) t =
      coordModelCoeffs b ω t ^ p * y (MvPolynomial.monomial (logCartierExponent p A r t.1) 1) :=
  coordExteriorCoeff_logInverseCartier y A r p ω t.1

end ModelDegree

section Basis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*} [LinearOrder ι]

theorem basisExteriorAlgebra_eq_listProd (b : Module.Basis ι R M) (s : Finset ι) :
    b.ExteriorAlgebra s =
      ((List.ofFn (s.orderEmbOfFin rfl)).map fun j => ExteriorAlgebra.ι R (b j)).prod := by
  rw [ExteriorAlgebra.basis_apply]
  change ExteriorAlgebra.ιMulti R s.card (b ∘ (s.orderEmbOfFin rfl)) = _
  rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
  rfl

theorem sum_ite_card_eq_sum_powersetCard {N : Type*} [AddCommMonoid N] {m : ℕ} (b : ℕ)
    (f : Finset (Fin m) → N) :
    (∑ s, if s.card = b then f s else 0) = ∑ t : Set.powersetCard (Fin m) b, f t.1 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun s => by simp [Set.powersetCard.mem_iff]) f

end Basis

section Chart

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The logarithmic directions `σ(Fin r)` of a chart. -/
noncomputable def logSetOf {r : ℕ} (σ : Fin r → Option (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => ∃ k, σ k = some j

theorem mem_logSetOf {r : ℕ} (σ : Fin r → Option (Fin n)) (j : Fin n) :
    j ∈ logSetOf σ ↔ ∃ k, σ k = some j := by
  simp [logSetOf]

theorem logGenerator_logSetOf (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))
    (j : Fin n) : logGenerator c (logSetOf σ) j = logChartBasis c σ j := by
  by_cases hj : ∃ k, σ k = some j
  · rw [logGenerator, ite_eq_left ((mem_logSetOf σ j).mpr hj), logChartBasis_apply_of_mem c σ hj]
  · rw [logGenerator, ite_eq_right (fun h => hj ((mem_logSetOf σ j).mp h)),
      logChartBasis_apply_of_not_mem c σ hj, etaleChartBasis_apply_eq]

/-- `e_s ↦ θ_s` sends the coordinate basis to the exterior algebra basis of the logarithmic
basis. -/
theorem logExteriorMap_coordExteriorBasis (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (s : Finset (Fin n)) :
    logExteriorMap c (logSetOf σ) (coordExteriorBasis K n s) =
      (logChartBasis c σ).ExteriorAlgebra s := by
  rw [coordExteriorBasis_eq_listProd, map_list_prod, List.map_map,
    basisExteriorAlgebra_eq_listProd]
  congr 2
  funext j
  simp only [Function.comp_apply, logExteriorMap_coordVector, logGenerator_logSetOf]

/-- **The rational `b`-form `Σ_t (a_t w) θ_t`** of coefficients on a chart. -/
noncomputable def logChartModelForm (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))
    (w : X.functionField) {b : ℕ} (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) :
    RationalForms K X b :=
  ∑ t, (sectionGermAlgHom (K := K) c.U (a t) * w) • logChartFormsBasis c σ b t

theorem logChartModelMap_coordModelOfCoeffs (c : EtaleChart K X n) {r : ℕ}
    (σ : Fin r → Option (Fin n)) (w : X.functionField) {b : ℕ}
    (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) :
    logChartModelMap c (logSetOf σ) w (coordModelOfCoeffs (K := K) a) =
      (logChartModelForm c σ w a : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) := by
  rw [coordModelOfCoeffs, map_sum, logChartModelForm, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [logChartModelMap_tmul, logExteriorMap_coordExteriorBasis, Submodule.coe_smul,
    ExteriorAlgebra.basis_eq_coe_basis]

/-- **The degree-`b` projection of the image of a coordinate form is the image of its degree-`b`
part.** -/
theorem formsProj_logChartModelMap (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))
    (w : X.functionField) (b : ℕ) (ω : Γ(X, c.U) ⊗[K] CoordExterior K n) :
    formsProj (K := K) (S := X.functionField) b (logChartModelMap c (logSetOf σ) w ω) =
      (logChartModelForm c σ w (coordModelCoeffs b ω) :
        ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) := by
  conv_lhs => rw [eq_sum_tmul_coordExteriorBasis ω]
  rw [map_sum, map_sum]
  have hterm : ∀ s : Finset (Fin n),
      formsProj (K := K) (S := X.functionField) b (logChartModelMap c (logSetOf σ) w
        ((Algebra.TensorProduct.basis Γ(X, c.U) (coordExteriorBasis K n)).repr ω s ⊗ₜ[K]
          coordExteriorBasis K n s)) =
        if s.card = b then (sectionGermAlgHom (K := K) c.U (coordExteriorCoeff ω s) * w) •
          (logChartBasis c σ).ExteriorAlgebra s else 0 := by
    intro s
    rw [logChartModelMap_tmul, logExteriorMap_coordExteriorBasis]
    have hmem : (logChartBasis c σ).ExteriorAlgebra s ∈
        ⋀[X.functionField]^s.card Ω[X.functionField⁄K] := by
      have h : (logChartBasis c σ).ExteriorAlgebra s =
          ((logChartBasis c σ).exteriorPower s.card (Set.powersetCard.ofCard rfl) :
            ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) :=
        ExteriorAlgebra.basis_eq_coe_basis _ (Set.powersetCard.ofCard rfl)
      rw [h]
      exact SetLike.coe_mem _
    split_ifs with hs
    · subst hs
      exact formsProj_of_mem_same (Submodule.smul_mem _ _ hmem)
    · exact formsProj_of_mem_ne (Submodule.smul_mem _ _ hmem) hs
  rw [Finset.sum_congr rfl fun s _ => hterm s, sum_ite_card_eq_sum_powersetCard b
    (fun s => (sectionGermAlgHom (K := K) c.U (coordExteriorCoeff ω s) * w) •
      (logChartBasis c σ).ExteriorAlgebra s), logChartModelForm, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Submodule.coe_smul, ← ExteriorAlgebra.basis_eq_coe_basis]
  rfl

section SNC

variable [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))]
  (hnorm : ∀ z : X, IsIntegrallyClosed (X.presheaf.stalk z))
  {r : ℕ} (ξ : Fin r → X) (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
  (E : Fin r → CartierDivisor X)
  (hEc : ∀ (k : Fin r) (z : CodimensionOnePoint X),
    cartierCoefficient (E k) (z : X) = if (z : X) = ξ k then 1 else 0)
  (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
  {N : CartierDivisor X} {h : X.functionFieldˣ} (hh : ∀ x ∈ c.U, N.IsLocalEquationAt x h)

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
theorem smul_logChartModelForm_inv (b : ℕ) (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) :
    (h : X.functionField) • logChartModelForm c σ ((h⁻¹ : X.functionFieldˣ) : X.functionField) a =
      ∑ t, sectionGermAlgHom (K := K) c.U (a t) • logChartFormsBasis c σ b t := by
  rw [logChartModelForm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_smul, Units.val_inv_eq_inv_val, mul_left_comm, mul_inv_cancel₀ h.ne_zero, mul_one]

include hnorm hinj hξ hEc hc hh in
/-- **The forms `Σ_t (a_t h⁻¹) θ_t` are logarithmic with poles bounded by `N`.** -/
theorem logChartModelForm_mem {b : ℕ} (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) (x : X)
    (hx : x ∈ c.U) (f : X.functionFieldˣ) (hf : N.IsLocalEquationAt x f) :
    (f : X.functionField) • logChartModelForm c σ ((h⁻¹ : X.functionFieldˣ) : X.functionField) a ∈
      logFormsLattice K E x b := by
  rw [smul_mem_logFormsLattice_iff_of_isLocalEquationAt E hf (hh x hx),
    smul_logChartModelForm_inv c σ b a,
    mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b]
  intro t
  rw [Module.Basis.repr_sum_self]
  exact ⟨X.presheaf.germ c.U x hx (a t),
    Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (U := c.U) hx (a t)⟩

include hnorm hinj hξ hEc hc in
/-- **Every section of `Ω^b_X(log E)(N)` over the chart is `Σ_t (a_t h⁻¹) θ_t`.** -/
theorem exists_logChartModelForm_eq {b : ℕ} (ρ : RationalForms K X b)
    (hρ : ∀ x ∈ c.U, (h : X.functionField) • ρ ∈ logFormsLattice K E x b) :
    ∃ a : Set.powersetCard (Fin n) b → Γ(X, c.U),
      ρ = logChartModelForm c σ ((h⁻¹ : X.functionFieldˣ) : X.functionField) a := by
  have hcoef : ∀ t, ∃ a : Γ(X, c.U), X.germToFunctionField c.U a =
      (logChartFormsBasis c σ b).repr ((h : X.functionField) • ρ) t := fun t =>
    exists_germToFunctionField_eq_of_forall_mem_range fun x hx =>
      (mem_logFormsLattice_iff hnorm ξ hinj hξ E hEc c σ hc x hx b _).mp (hρ x hx) t
  choose a ha using hcoef
  refine ⟨a, ?_⟩
  have h1 : (h : X.functionField) • ρ = (h : X.functionField) •
      logChartModelForm c σ ((h⁻¹ : X.functionFieldˣ) : X.functionField) a := by
    rw [smul_logChartModelForm_inv c σ b a]
    conv_lhs => rw [← (logChartFormsBasis c σ b).sum_repr ((h : X.functionField) • ρ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← ha t]
    rfl
  exact smul_right_injective _ h.ne_zero h1

omit [IsLocallyNoetherian X] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (z : X))] in
/-- **The coefficients are unique.** -/
theorem logChartModelForm_injective {w : X.functionField} (hw : w ≠ 0) {b : ℕ}
    {a a' : Set.powersetCard (Fin n) b → Γ(X, c.U)}
    (h : logChartModelForm c σ w a = logChartModelForm c σ w a') : a = a' := by
  funext t
  have := congrArg (fun ρ => (logChartFormsBasis c σ b).repr ρ t) h
  simp only [logChartModelForm, Module.Basis.repr_sum_self] at this
  exact Scheme.germToFunctionField_injective X c.U (mul_right_cancel₀ hw this)

end SNC

section Cartier

variable (c : EtaleChart K X n) {r : ℕ} (σ : Fin r → Option (Fin n))

/-- **The model map is injective** for a nonzero weight. -/
theorem logChartModelMap_injective {w : X.functionField} (hw : w ≠ 0) :
    Function.Injective (logChartModelMap c (logSetOf σ) w) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro ω hω
  have hexp : logChartModelMap c (logSetOf σ) w ω = ∑ s,
      (sectionGermAlgHom (K := K) c.U (coordExteriorCoeff ω s) * w) •
        (logChartBasis c σ).ExteriorAlgebra s := by
    conv_lhs => rw [eq_sum_tmul_coordExteriorBasis ω]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [logChartModelMap_tmul, logExteriorMap_coordExteriorBasis]
  rw [hexp] at hω
  have hli := (logChartBasis c σ).ExteriorAlgebra.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have h0 := hli _ hω
  apply eq_zero_of_coordExteriorCoeff
  intro s
  have hs := h0 s
  rw [mul_eq_zero, or_iff_left hw] at hs
  exact Scheme.germToFunctionField_injective X c.U (hs.trans (map_zero _).symm)

variable (p : ℕ) [hp : Fact p.Prime] [CharP K p] (rr : Fin n → ℕ) (g : X.functionFieldˣ)

/-- The twist weight `(g^p y^r)⁻¹` of a chart. -/
noncomputable abbrev logTwistWeight : X.functionField :=
  (((g ^ p * logTwistMonomial c (logSetOf σ) rr)⁻¹ : X.functionFieldˣ) : X.functionField)

/-- **The logarithmic inverse Cartier operator on the forms of a chart**:
`Σ_t (a_t w) θ_t ↦ Σ_t (a_t^p y^{β(t)} w) θ_t`. -/
noncomputable def logChartInverseCartierForm (w : X.functionField) {b : ℕ}
    (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) : RationalForms K X b :=
  logChartModelForm c σ w fun t =>
    a t ^ p * c.coords (MvPolynomial.monomial (logCartierExponent p (logSetOf σ) rr t.1) 1)

omit [CharP K p] in
theorem logChartModelMap_logInverseCartier (w : X.functionField) {b : ℕ}
    (a : Set.powersetCard (Fin n) b → Γ(X, c.U)) :
    logChartModelMap c (logSetOf σ) w
        (logInverseCartier c.coords p (logSetOf σ) rr (coordModelOfCoeffs (K := K) a)) =
      (logChartInverseCartierForm c σ p rr w a :
        ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) := by
  rw [logInverseCartier_coordModelOfCoeffs, logChartModelMap_coordModelOfCoeffs]
  rfl

omit hp in
theorem rationalDeRhamDiff_logChartModelMap_twist (ω : Γ(X, c.U) ⊗[K] CoordExterior K n) :
    rationalDeRhamDiff c (logChartModelMap c (logSetOf σ) (logTwistWeight c σ p rr g) ω) =
      logChartModelMap c (logSetOf σ) (logTwistWeight c σ p rr g)
        (koszulDeRhamDiff (logTwistedPartial c.coords c.formallyEtale (logSetOf σ) rr) ω) :=
  rationalDeRhamDiff_logChartModelMap c (logSetOf σ) rr _
    (etaleCoordPartial_logTwistWeight c (logSetOf σ) rr g p) ω

omit hp [CharP K p] in
theorem formsProj_succ_rationalDeRhamDiff (b : ℕ)
    (x : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) :
    formsProj (K := K) (S := X.functionField) (b + 1) (rationalDeRhamDiff c x) =
      rationalDeRhamDiff c (formsProj (K := K) (S := X.functionField) b x) :=
  formsProj_succ_kaehlerDeRhamDiff _ _ b x

omit hp [CharP K p] in
theorem formsProj_zero_rationalDeRhamDiff (x : ExteriorAlgebra X.functionField Ω[X.functionField⁄K]) :
    formsProj (K := K) (S := X.functionField) 0 (rationalDeRhamDiff c x) = 0 :=
  formsProj_zero_kaehlerDeRhamDiff _ _ x

omit hp [CharP K p] in
theorem logChartModelForm_logInverseCartier (w : X.functionField) (b : ℕ)
    (Y : Γ(X, c.U) ⊗[K] CoordExterior K n) :
    logChartModelForm c σ w (coordModelCoeffs b (logInverseCartier c.coords p (logSetOf σ) rr Y)) =
      logChartInverseCartierForm c σ p rr w (coordModelCoeffs b Y) := by
  rw [logChartInverseCartierForm]
  congr 1
  funext t
  exact coordModelCoeffs_logInverseCartier c.coords (logSetOf σ) rr p b Y t

variable [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)]
  (hy0 : ∀ j : Fin n, etaleCoordFun c.coords j ≠ 0) (hr : ∀ j ∈ logSetOf σ, rr j < p)

include hy0 hr in
/-- **The logarithmic Cartier isomorphism on a chart, existence in degree `b + 1`**: a closed form
`Σ_t (a_t w) θ_t` is `C⁻¹` of a form plus the differential of a form of degree `b`. -/
theorem logChart_cartier_exists_succ {b : ℕ} (a : Set.powersetCard (Fin n) (b + 1) → Γ(X, c.U))
    (hz : rationalFormsDiff c (b + 1) (logChartModelForm c σ (logTwistWeight c σ p rr g) a) = 0) :
    ∃ (y : Set.powersetCard (Fin n) (b + 1) → Γ(X, c.U))
      (a' : Set.powersetCard (Fin n) b → Γ(X, c.U)),
      logChartModelForm c σ (logTwistWeight c σ p rr g) a =
        logChartInverseCartierForm c σ p rr (logTwistWeight c σ p rr g) y +
          rationalFormsDiff c b (logChartModelForm c σ (logTwistWeight c σ p rr g) a') := by
  have hw0 : logTwistWeight c σ p rr g ≠ 0 := Units.ne_zero _
  have hΨZ := logChartModelMap_coordModelOfCoeffs c σ (logTwistWeight c σ p rr g) a
  have hdZ : koszulDeRhamDiff (logTwistedPartial c.coords c.formallyEtale (logSetOf σ) rr)
      (coordModelOfCoeffs (K := K) a) = 0 := by
    apply logChartModelMap_injective c σ hw0
    rw [map_zero, ← rationalDeRhamDiff_logChartModelMap_twist c σ p rr g, hΨZ,
      ← rationalFormsDiff_coe, hz]
    rfl
  obtain ⟨Y, hY, -⟩ := log_etale_cartier_isomorphism c.coords c.formallyEtale (logSetOf σ) rr p hy0
    hr _ hdZ
  obtain ⟨H, hH⟩ := hY
  refine ⟨coordModelCoeffs (b + 1) Y, coordModelCoeffs b H, ?_⟩
  apply Subtype.ext
  have h1 := congrArg (logChartModelMap c (logSetOf σ) (logTwistWeight c σ p rr g)) hH
  rw [← rationalDeRhamDiff_logChartModelMap_twist c σ p rr g, map_sub, hΨZ] at h1
  have h2 := congrArg (formsProj (K := K) (S := X.functionField) (b + 1)) h1
  rw [map_sub, formsProj_of_mem_same (logChartModelForm c σ _ a).2, formsProj_logChartModelMap,
    formsProj_succ_rationalDeRhamDiff, formsProj_logChartModelMap,
    logChartModelForm_logInverseCartier] at h2
  rw [Submodule.coe_add, rationalFormsDiff_coe, h2]
  abel

include hy0 hr in
/-- **The logarithmic Cartier isomorphism on a chart, existence in degree `0`.** -/
theorem logChart_cartier_exists_zero (a : Set.powersetCard (Fin n) 0 → Γ(X, c.U))
    (hz : rationalFormsDiff c 0 (logChartModelForm c σ (logTwistWeight c σ p rr g) a) = 0) :
    ∃ y : Set.powersetCard (Fin n) 0 → Γ(X, c.U),
      logChartModelForm c σ (logTwistWeight c σ p rr g) a =
        logChartInverseCartierForm c σ p rr (logTwistWeight c σ p rr g) y := by
  have hw0 : logTwistWeight c σ p rr g ≠ 0 := Units.ne_zero _
  have hΨZ := logChartModelMap_coordModelOfCoeffs c σ (logTwistWeight c σ p rr g) a
  have hdZ : koszulDeRhamDiff (logTwistedPartial c.coords c.formallyEtale (logSetOf σ) rr)
      (coordModelOfCoeffs (K := K) a) = 0 := by
    apply logChartModelMap_injective c σ hw0
    rw [map_zero, ← rationalDeRhamDiff_logChartModelMap_twist c σ p rr g, hΨZ,
      ← rationalFormsDiff_coe, hz]
    rfl
  obtain ⟨Y, hY, -⟩ := log_etale_cartier_isomorphism c.coords c.formallyEtale (logSetOf σ) rr p hy0
    hr _ hdZ
  obtain ⟨H, hH⟩ := hY
  refine ⟨coordModelCoeffs 0 Y, ?_⟩
  apply Subtype.ext
  have h1 := congrArg (logChartModelMap c (logSetOf σ) (logTwistWeight c σ p rr g)) hH
  rw [← rationalDeRhamDiff_logChartModelMap_twist c σ p rr g, map_sub, hΨZ] at h1
  have h2 := congrArg (formsProj (K := K) (S := X.functionField) 0) h1
  rw [map_sub, formsProj_of_mem_same (logChartModelForm c σ _ a).2, formsProj_logChartModelMap,
    formsProj_zero_rationalDeRhamDiff, logChartModelForm_logInverseCartier] at h2
  exact (sub_eq_zero.mp h2.symm)

omit [IsIntegral X] [CharP K p] [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)] in
theorem logInverseCartier_zero_form :
    logInverseCartier c.coords p (logSetOf σ) rr (0 : Γ(X, c.U) ⊗[K] CoordExterior K n) = 0 := by
  apply eq_zero_of_coordExteriorCoeff
  intro s
  rw [coordExteriorCoeff_logInverseCartier]
  simp only [coordExteriorCoeff, map_zero, Finsupp.zero_apply]
  rw [zero_pow hp.out.ne_zero, zero_mul]

omit [IsIntegral X] [Algebra.FiniteType K Γ(X, c.U)] in
theorem eq_zero_of_coordModelOfCoeffs_eq_zero {b : ℕ} {y : Set.powersetCard (Fin n) b → Γ(X, c.U)}
    (h : coordModelOfCoeffs (K := K) y = 0) : y = 0 := by
  funext t
  have h1 := coordExteriorCoeff_coordModelOfCoeffs (K := K) y t.1
  have hcard : (t : Finset (Fin n)).card = b := Set.powersetCard.mem_iff.mp t.2
  simp only [hcard, ↓reduceDIte] at h1
  rw [h] at h1
  have h0 : coordExteriorCoeff (0 : Γ(X, c.U) ⊗[K] CoordExterior K n) t.1 = 0 := by
    simp [coordExteriorCoeff]
  rw [h0] at h1
  exact h1.symm

include hy0 hr in
/-- **The logarithmic Cartier isomorphism on a chart, uniqueness in degree `b + 1`.** -/
theorem logChart_cartier_unique_succ {b : ℕ} (y : Set.powersetCard (Fin n) (b + 1) → Γ(X, c.U))
    (a' : Set.powersetCard (Fin n) b → Γ(X, c.U))
    (h : logChartInverseCartierForm c σ p rr (logTwistWeight c σ p rr g) y =
      rationalFormsDiff c b (logChartModelForm c σ (logTwistWeight c σ p rr g) a')) : y = 0 := by
  have hw0 : logTwistWeight c σ p rr g ≠ 0 := Units.ne_zero _
  have hdH : logInverseCartier c.coords p (logSetOf σ) rr (coordModelOfCoeffs (K := K) y) =
      koszulDeRhamDiff (logTwistedPartial c.coords c.formallyEtale (logSetOf σ) rr)
        (coordModelOfCoeffs (K := K) a') := by
    apply logChartModelMap_injective c σ hw0
    rw [logChartModelMap_logInverseCartier, ← rationalDeRhamDiff_logChartModelMap_twist c σ p rr g,
      logChartModelMap_coordModelOfCoeffs, ← rationalFormsDiff_coe, ← h]
  have hz := logInverseCartier_cocycle c.coords c.formallyEtale (logSetOf σ) rr p hy0 hr
    (coordModelOfCoeffs (K := K) y)
  obtain ⟨ω, -, huniq⟩ := log_etale_cartier_isomorphism c.coords c.formallyEtale (logSetOf σ) rr p
    hy0 hr _ hz
  have h1 := huniq (coordModelOfCoeffs (K := K) y) (by
    simp only [sub_self]
    exact Submodule.zero_mem _)
  have h2 := huniq 0 (by
    simp only [logInverseCartier_zero_form, sub_zero, hdH]
    exact LinearMap.mem_range_self _ _)
  exact eq_zero_of_coordModelOfCoeffs_eq_zero c (h1.trans h2.symm)

omit [PerfectRing K p] [Algebra.FiniteType K Γ(X, c.U)] in
include hy0 in
/-- **The logarithmic Cartier isomorphism on a chart, uniqueness in degree `0`.** -/
theorem logChart_cartier_unique_zero (y : Set.powersetCard (Fin n) 0 → Γ(X, c.U))
    (h : logChartInverseCartierForm c σ p rr (logTwistWeight c σ p rr g) y = 0) : y = 0 := by
  have hw0 : logTwistWeight c σ p rr g ≠ 0 := Units.ne_zero _
  have h0 : logInverseCartier c.coords p (logSetOf σ) rr (coordModelOfCoeffs (K := K) y) =
      logInverseCartier c.coords p (logSetOf σ) rr 0 := by
    rw [logInverseCartier_zero_form]
    apply logChartModelMap_injective c σ hw0
    rw [logChartModelMap_logInverseCartier, h, map_zero]
    rfl
  exact eq_zero_of_coordModelOfCoeffs_eq_zero c
    (logInverseCartier_injective c.coords (logSetOf σ) rr p hy0 h0)

end Cartier

end Chart

end MixedFujita
