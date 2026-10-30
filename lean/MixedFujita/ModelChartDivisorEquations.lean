/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformMonomialAssembly

/-!
Actual local equations for the model Jacobian and the pullback of a regular base function.
The monomial assembly uses these equations directly; neither a chosen Jacobian equation nor a
normality/DVR assumption on the smooth model has to be supplied by the caller.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra cartierBaseLocalAlgebra
  functionFieldBaseAlgebra

section Equations

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))] {n : ℕ}

/-- The pullback of the principal divisor of an actual base function has the pulled-back chart
function as its local equation at every point. -/
theorem modelChart_pullback_principal_localEquation
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (g : A) (u : (Spec (CommRingCat.of A)).functionFieldˣ)
    (hu : (u : (Spec (CommRingCat.of A)).functionField) =
      (Spec (CommRingCat.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))
    (c : EtaleChart K T n) (t : T) :
    ∃ v : T.functionFieldˣ,
      (v : T.functionField) = T.germToFunctionField c.U (modelChartAlgHom (K := K) ρ c.U g) ∧
      (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A)) u)).IsLocalEquationAt t v := by
  refine ⟨Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom u, ?_, ?_⟩
  · change (dominantFunctionFieldMap ρ).hom (u : (Spec (CommRingCat.of A)).functionField) = _
    rw [hu, dominantFunctionFieldMap_germ ρ ⊤ c.U le_top]
    rfl
  · rw [cartierPullback_principal]
    exact CartierDivisor.isLocalEquationAt_principalCartierDivisor _ _

variable [SmoothOfRelativeDimension n (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

/-- The actual chart Jacobian is a local equation of the actual birational relative canonical
divisor, regardless of the reference charts used to define that divisor. -/
theorem modelChart_jacobian_localEquation
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
    (cX : EtaleChart K (Spec (CommRingCat.of A)) n) (cT : EtaleChart K T n)
    (φ : MvPolynomial (Fin n) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    (c : EtaleChart K T n) (t : T) (ht : t ∈ c.U) :
    ∃ u : T.functionFieldˣ,
      (u : T.functionField) = T.germToFunctionField c.U
        (etaleRelativeJacobian (modelChartAlgHom (K := K) ρ c.U) φ c.coords c.formallyEtale).det ∧
      (birationalRelativeCanonicalDivisor n ρ hρ cX etaleCharts_cover cT etaleCharts_cover).IsLocalEquationAt t u := by
  let hR := isUnit_chartRelativeJacobianDet_of_bijective ρ hρ cX cT
  refine ⟨(isUnit_chartRelativeJacobianDet ρ cX cT hR (specAlgebraEtaleChart φ hφ) c).unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, chartRelativeJacobianDet_appLE]
  · exact relativeCanonicalDivisor_isLocalEquationAt ρ cX etaleCharts_cover cT etaleCharts_cover
      hR t (specAlgebraEtaleChart φ hφ) trivial c ht

end Equations

section Monomials

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  {N r : ℕ}
  [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
  {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
  (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1)) (cT : EtaleChart K T (N + 1))

local notation "Rρ" => birationalRelativeCanonicalDivisor (N + 1) ρ hρ cX etaleCharts_cover cT etaleCharts_cover

/-- The actual model Jacobian supplies its quotient monomial identity with natural exponents
equal to the actual relative canonical coefficients on all assigned components. -/
theorem exists_modelChart_jacobian_quotient_monomial
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    (c : EtaleChart K T (N + 1)) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Rρ (z : T) = 0)
    (s₀ : Fin r) (hσ₀ : σ s₀ = some 0) (hzero : cartierCoefficient Rρ (ξ s₀) = 0)
    (t : T) (ht : t ∈ c.U)
    (P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}))
    (hmem : ∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ P ↔
      f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) :
    ∃ (κ : Fin N → ℕ) (J₁ J₂ : Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}),
      J₁ ∉ P ∧ J₂ ∉ P ∧
      Ideal.Quotient.mk _ (etaleRelativeJacobian (modelChartAlgHom (K := K) ρ c.U) φ c.coords c.formallyEtale).det * J₁ =
        (∏ l, hyperplaneCoords c.coords (MvPolynomial.X l) ^ κ l) * J₂ ∧
      ∀ (i : Fin r) (l : Fin N), σ i = some l.succ → (κ l : ℤ) = cartierCoefficient Rρ (ξ i) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (N + 1) _
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have hnonneg (i : Fin r) : 0 ≤ cartierCoefficient Rρ (ξ i) :=
    cartierCoefficient_nonneg_of_isEffective _
      (birationalRelativeCanonicalDivisor_isEffective ρ hρ cX etaleCharts_cover cT etaleCharts_cover) _
  obtain ⟨u, hu, hf⟩ := modelChart_jacobian_localEquation ρ hρ cX cT φ hφ c t ht
  obtain ⟨κ, J₁, J₂, hJ₁, hJ₂, heq, hκ⟩ := exists_quotient_function_monomial
    (smooth_stalk_isIntegrallyClosed (K := K)) Rρ c ξ hinj hξ σ hc hsupport
    (fun i => (cartierCoefficient Rρ (ξ i)).toNat) (fun i => (Int.toNat_of_nonneg (hnonneg i)).symm)
    s₀ hσ₀ (by rw [hzero]; rfl) t ht _ u hu hf P hmem
  exact ⟨κ, J₁, J₂, hJ₁, hJ₂, heq, fun i l hi => by rw [hκ i l hi, Int.toNat_of_nonneg (hnonneg i)]⟩

end Monomials

section RegularFunctions

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  {N r : ℕ} {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K))]
  (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [ρ.IsOver (Spec (CommRingCat.of K))]
  (g : A) (u : (Spec (CommRingCat.of A)).functionFieldˣ)
  (hu : (u : (Spec (CommRingCat.of A)).functionField) =
    (Spec (CommRingCat.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g))

local notation "Dg" => cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A)) u)

include hu

/-- A regular base function on the actual model chart is a monomial up to two pointwise units;
its natural exponents are the actual coefficients of its pulled-back principal divisor. -/
theorem exists_modelChart_function_monomial
    (c : EtaleChart K T (N + 1)) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Dg (z : T) = 0)
    (t : T) (ht : t ∈ c.U) :
    ∃ (b : Fin (N + 1) → ℕ) (V W : Γ(T, c.U)),
      V ∉ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal ∧
      W ∉ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal ∧
      modelChartAlgHom (K := K) ρ c.U g * V = (∏ l, c.coords (MvPolynomial.X l) ^ b l) * W ∧
      ∀ (i : Fin r) (l : Fin (N + 1)), σ i = some l → (b l : ℤ) = cartierCoefficient Dg (ξ i) := by
  have : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth (N + 1) _
  have : ∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T)) :=
    fun z => smoothOverField_codimensionOne_stalk_DVR (K := K) z
  have hA : (principalCartierDivisor (Spec (CommRingCat.of A)) u).IsEffective :=
    (CartierDivisor.isEffective_principalCartierDivisor_iff _).mpr
      ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv g, hu.symm⟩
  have hnonneg (i : Fin r) : 0 ≤ cartierCoefficient Dg (ξ i) :=
    cartierCoefficient_nonneg_of_isEffective _ (cartierPullback_isEffective ρ _ hA) _
  obtain ⟨v, hv, hf⟩ := modelChart_pullback_principal_localEquation ρ g u hu c t
  obtain ⟨b, V, W, hV, hW, heq, hb⟩ := exists_chart_function_monomial
    (smooth_stalk_isIntegrallyClosed (K := K)) Dg c ξ hinj hξ σ hc hsupport
    (fun i => (cartierCoefficient Dg (ξ i)).toNat) (fun i => (Int.toNat_of_nonneg (hnonneg i)).symm)
    t ht _ v hv hf
  exact ⟨b, V, W, hV, hW, heq, fun i l hi => by rw [hb i l hi, Int.toNat_of_nonneg (hnonneg i)]⟩

/-- For a pulled-back function with strict-transform coefficient one, the remaining factor w
has a quotient monomial identity with the other actual coefficients. -/
theorem exists_modelChart_factor_quotient_monomial
    (c : EtaleChart K T (N + 1)) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Dg (z : T) = 0)
    (s₀ : Fin r) (hσ₀ : σ s₀ = some 0) (hone : cartierCoefficient Dg (ξ s₀) = 1)
    (t : T) (ht : t ∈ c.U) (w : Γ(T, c.U))
    (hw : modelChartAlgHom (K := K) ρ c.U g = c.coords (MvPolynomial.X 0) * w)
    (P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}))
    (hmem : ∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ P ↔
      f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) :
    ∃ (η : Fin N → ℕ) (W₁ W₂ : Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}),
      W₁ ∉ P ∧ W₂ ∉ P ∧ Ideal.Quotient.mk _ w * W₁ =
        (∏ l, hyperplaneCoords c.coords (MvPolynomial.X l) ^ η l) * W₂ ∧
      ∀ (i : Fin r) (l : Fin N), σ i = some l.succ → (η l : ℤ) = cartierCoefficient Dg (ξ i) := by
  obtain ⟨b, V, W, hV, hW, heq, hb⟩ := exists_modelChart_function_monomial ρ g u hu c ξ hinj hξ
    σ hc hsupport t ht
  have hb₀ : b 0 = 1 := by exact_mod_cast (hb s₀ 0 hσ₀).trans hone
  rw [hw] at heq
  exact ⟨fun l => b l.succ, Ideal.Quotient.mk _ V, Ideal.Quotient.mk _ W,
    fun h => hV ((hmem V).mp h), fun h => hW ((hmem W).mp h),
    hyperplane_quotient_monomial_one c.coords (etaleCoordinate_ne_zero c.coords c.formallyEtale 0)
      b hb₀ w V W heq, fun i l hi => hb i l.succ hi⟩

/-- The actual order lower bound for a generator gives its quotient divisibility witness, with
a denominator nonvanishing at the selected intersection point. -/
theorem exists_modelChart_generator_quotient_factor
    (c : EtaleChart K T (N + 1)) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Dg (z : T) = 0)
    (j : Fin r) (l : Fin N) (hσj : σ j = some l.succ) (a : ℕ)
    (ha : (a : ℤ) ≤ cartierCoefficient Dg (ξ j)) (t : T) (ht : t ∈ c.U)
    (P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}))
    (hmem : ∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ P ↔
      f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) :
    ∃ q V : Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}, V ∉ P ∧
      Ideal.Quotient.mk _ (modelChartAlgHom (K := K) ρ c.U g) * V =
        hyperplaneCoords c.coords (MvPolynomial.X l) ^ a * q := by
  obtain ⟨b, V, W, hV, -, heq, hb⟩ := exists_modelChart_function_monomial ρ g u hu c ξ hinj hξ
    σ hc hsupport t ht
  have hab : a ≤ b l.succ := by exact_mod_cast ha.trans_eq (hb j l.succ hσj).symm
  obtain ⟨q, hq⟩ := exists_factor_of_monomial_exponent (fun l => c.coords (MvPolynomial.X l)) b
    l.succ a hab _ V W heq
  refine ⟨Ideal.Quotient.mk _ q, Ideal.Quotient.mk _ V, fun h => hV ((hmem V).mp h), ?_⟩
  have h := congrArg (Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)})) hq
  simpa only [map_mul, map_pow, hyperplaneCoords_X] using h

end RegularFunctions

end MixedFujita
