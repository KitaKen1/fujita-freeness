/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformQuotientChart

/-!
Monomial equations for strict transform charts, with their actual component exponents.

The local-product theorem gives an equality in the function field. Injectivity of chart germs
turns it into an equality in the chart ring. The SNC assignment is injective, so the exponent of
an assigned coordinate is exactly the coefficient of that member. Passing to the hyperplane
quotient removes a zero exponent. If the first exponent is one, cancellation of the first
coordinate removes precisely the strict-transform factor before passing to the quotient.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Exponents

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  {n r : ℕ}

/-- Gathering the member exponents by coordinate preserves the exponent of every assigned member. -/
theorem sncChart_gathered_exponent_eq (c : EtaleChart K T n) (ξ : Fin r → T)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (e : Fin r → ℕ)
    (i : Fin r) (l : Fin n) (hi : σ i = some l) :
    (∑ j ∈ Finset.univ.filter (fun j => σ j = some l), e j) = e i := by
  classical
  have hfilter : Finset.univ.filter (fun j => σ j = some l) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hj => hc.1 j i l hj hi, fun hji => hji ▸ hi⟩
  rw [hfilter, Finset.sum_singleton]

end Exponents

section LocalProduct

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  {n r : ℕ}

/-- A chart function which is a local equation of an SNC-supported divisor has an actual chart-ring
monomial factorization, with both extra factors nonvanishing at the given point. The exponents are
the supplied natural coefficients, and are identified on every assigned member. -/
theorem exists_chart_function_monomial
    [∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T))]
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (D : CartierDivisor T) (c : EtaleChart K T n) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient D (z : T) = 0)
    (e : Fin r → ℕ) (he : ∀ i, cartierCoefficient D (ξ i) = (e i : ℤ))
    (t : T) (ht : t ∈ c.U) (f : Γ(T, c.U)) (u : T.functionFieldˣ)
    (hu : (u : T.functionField) = T.germToFunctionField c.U f)
    (hf : D.IsLocalEquationAt t u) :
    ∃ (b : Fin n → ℕ) (V W : Γ(T, c.U)),
      V ∉ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal ∧
      W ∉ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal ∧
      f * V = (∏ l, c.coords (MvPolynomial.X l) ^ b l) * W ∧
      ∀ (i : Fin r) (l : Fin n), σ i = some l → b l = e i := by
  classical
  obtain ⟨W, V, hW, hV, hprod⟩ :=
    exists_chart_local_product hnorm D c ξ hinj hξ σ hc hsupport t ht u hf
  let b : Fin n → ℕ := fun l => ∑ i ∈ Finset.univ.filter (fun i => σ i = some l), e i
  have hexp : (∏ i, sncChartComponentEquation c σ i ^ cartierCoefficient D (ξ i) :
      T.functionFieldˣ) = ∏ i, sncChartComponentEquation c σ i ^ (e i : ℤ) :=
    Finset.prod_congr rfl fun i _ => by rw [he i]
  rw [hexp, sncChart_component_monomial_eq, hu] at hprod
  refine ⟨b, V, W, hV, hW, ?_, fun i l hi => sncChart_gathered_exponent_eq c ξ σ hc e i l hi⟩
  apply Scheme.germToFunctionField_injective T c.U
  rw [map_mul, map_mul]
  exact hprod.trans (mul_comm _ _)

end LocalProduct

section Quotient

variable {K C : Type*} [Field K] [CommRing C] [Algebra K C] {N : ℕ}

/-- A monomial with zero first exponent descends to the remaining coordinates. -/
theorem hyperplane_quotient_monomial_zero
    (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] C) (b : Fin (N + 1) → ℕ) (hb : b 0 = 0)
    (f V W : C) (h : f * V = (∏ l, y (MvPolynomial.X l) ^ b l) * W) :
    Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}) f * Ideal.Quotient.mk _ V =
      (∏ l : Fin N, hyperplaneCoords y (MvPolynomial.X l) ^ b l.succ) *
        Ideal.Quotient.mk _ W := by
  have h' := congrArg (Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)})) h
  rw [Fin.prod_univ_succ, hb, pow_zero, one_mul] at h'
  simpa only [map_mul, map_prod, map_pow, hyperplaneCoords_X] using h'

/-- Cancel exactly one strict-transform factor before descending to the hyperplane quotient. -/
theorem hyperplane_quotient_monomial_one [IsDomain C]
    (y : MvPolynomial (Fin (N + 1)) K →ₐ[K] C) (hy : y (MvPolynomial.X 0) ≠ 0)
    (b : Fin (N + 1) → ℕ) (hb : b 0 = 1)
    (w V W : C) (h : (y (MvPolynomial.X 0) * w) * V =
      (∏ l, y (MvPolynomial.X l) ^ b l) * W) :
    Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}) w * Ideal.Quotient.mk _ V =
      (∏ l : Fin N, hyperplaneCoords y (MvPolynomial.X l) ^ b l.succ) *
        Ideal.Quotient.mk _ W := by
  rw [Fin.prod_univ_succ, hb, pow_one, mul_assoc, mul_assoc] at h
  have h' := congrArg (Ideal.Quotient.mk (Ideal.span {y (MvPolynomial.X 0)}))
    (mul_left_cancel₀ hy h)
  simpa only [map_mul, map_prod, map_pow, hyperplaneCoords_X] using h'

/-- A lower bound on one monomial exponent supplies the divisibility witness needed for every
generator in a strict-transform chart. This is an exact ring equality. -/
theorem exists_factor_of_monomial_exponent {ι : Type*} [Fintype ι]
    (y : ι → C) (b : ι → ℕ) (i : ι) (a : ℕ) (ha : a ≤ b i)
    (f V W : C) (h : f * V = (∏ l, y l ^ b l) * W) :
    ∃ q : C, f * V = y i ^ a * q := by
  have hdiv : y i ^ a ∣ ∏ l, y l ^ b l :=
    (pow_dvd_pow (y i) ha).trans (Finset.dvd_prod_of_mem (fun l => y l ^ b l) (Finset.mem_univ i))
  rw [h]
  exact hdiv.mul_right W

end Quotient

section PointedQuotient

attribute [local instance] cartierBaseOpenAlgebra

variable {K : Type u} [Field K] {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T]
  [T.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))]
  [∀ z : CodimensionOnePoint T, IsDiscreteValuationRing (T.presheaf.stalk (z : T))]
  {N r : ℕ}

/-- A divisor with coefficient zero on the strict-transform member supplies the required monomial
identity on the actual quotient, with both auxiliary factors nonvanishing at its point. -/
theorem exists_quotient_function_monomial
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (D : CartierDivisor T) (c : EtaleChart K T (N + 1)) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient D (z : T) = 0)
    (e : Fin r → ℕ) (he : ∀ i, cartierCoefficient D (ξ i) = (e i : ℤ))
    (s₀ : Fin r) (hσ₀ : σ s₀ = some 0) (he₀ : e s₀ = 0)
    (t : T) (ht : t ∈ c.U) (f : Γ(T, c.U)) (u : T.functionFieldˣ)
    (hu : (u : T.functionField) = T.germToFunctionField c.U f)
    (hf : D.IsLocalEquationAt t u)
    (P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}))
    (hmem : ∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ P ↔
      f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) :
    ∃ (b : Fin N → ℕ) (V W : Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}),
      V ∉ P ∧ W ∉ P ∧ Ideal.Quotient.mk _ f * V =
        (∏ l, hyperplaneCoords c.coords (MvPolynomial.X l) ^ b l) * W ∧
      ∀ (i : Fin r) (l : Fin N), σ i = some l.succ → b l = e i := by
  obtain ⟨b, V, W, hV, hW, hprod, hb⟩ := exists_chart_function_monomial hnorm D c ξ hinj hξ
    σ hc hsupport e he t ht f u hu hf
  refine ⟨fun l => b l.succ, Ideal.Quotient.mk _ V, Ideal.Quotient.mk _ W,
    fun h => hV ((hmem V).mp h), fun h => hW ((hmem W).mp h), ?_, fun i l hi => hb i l.succ hi⟩
  exact hyperplane_quotient_monomial_zero c.coords b ((hb s₀ 0 hσ₀).trans he₀) f V W hprod

/-- A divisor with coefficient one on the strict transform supplies the monomial identity for
the remaining factor w. Cancellation takes place in the domain before passing to the quotient. -/
theorem exists_quotient_factor_monomial
    (hnorm : ∀ z : T, IsIntegrallyClosed (T.presheaf.stalk z))
    (D : CartierDivisor T) (c : EtaleChart K T (N + 1)) (ξ : Fin r → T)
    (hinj : Function.Injective ξ) (hξ : ∀ i, Order.coheight (ξ i) = 1)
    (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (hsupport : ∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
      cartierCoefficient D (z : T) = 0)
    (e : Fin r → ℕ) (he : ∀ i, cartierCoefficient D (ξ i) = (e i : ℤ))
    (s₀ : Fin r) (hσ₀ : σ s₀ = some 0) (he₀ : e s₀ = 1)
    (t : T) (ht : t ∈ c.U) (w : Γ(T, c.U)) (u : T.functionFieldˣ)
    (hu : (u : T.functionField) = T.germToFunctionField c.U (c.coords (MvPolynomial.X 0) * w))
    (hf : D.IsLocalEquationAt t u)
    (P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}))
    (hmem : ∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ P ↔
      f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) :
    ∃ (b : Fin N → ℕ) (V W : Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}),
      V ∉ P ∧ W ∉ P ∧ Ideal.Quotient.mk _ w * V =
        (∏ l, hyperplaneCoords c.coords (MvPolynomial.X l) ^ b l) * W ∧
      ∀ (i : Fin r) (l : Fin N), σ i = some l.succ → b l = e i := by
  obtain ⟨b, V, W, hV, hW, hprod, hb⟩ := exists_chart_function_monomial hnorm D c ξ hinj hξ
    σ hc hsupport e he t ht (c.coords (MvPolynomial.X 0) * w) u hu hf
  refine ⟨fun l => b l.succ, Ideal.Quotient.mk _ V, Ideal.Quotient.mk _ W,
    fun h => hV ((hmem V).mp h), fun h => hW ((hmem W).mp h), ?_, fun i l hi => hb i l.succ hi⟩
  exact hyperplane_quotient_monomial_one c.coords (etaleCoordinate_ne_zero c.coords c.formallyEtale 0)
    b ((hb s₀ 0 hσ₀).trans he₀) w V W hprod

end PointedQuotient

end MixedFujita
