/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformModelCoefficients
public import MixedFujita.ModelChartDivisorEquations

/-!
A common SNC principalizing model from the original nondegenerate finite family of functions.
Zero generators are removed only when forming principal Cartier divisors. The returned bad-member
criterion retains the original indexing, including zero generators. The strict-transform member
has h = 1, k = 0 and a = 0 on this same model.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Functions

variable {A : Type u} [CommRing A] [IsDomain A]

/-- A nonzero regular function on Spec A as a unit of its actual function field. -/
noncomputable def specFunctionRationalUnit (g : A) (hg : g ≠ 0) :
    (Spec (CommRingCat.of A)).functionFieldˣ :=
  regularEquationRationalUnit (Spec (CommRingCat.of A)) ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) (by
      intro h
      apply hg
      have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom h
      simpa using h')

@[simp]
theorem specFunctionRationalUnit_val (g : A) (hg : g ≠ 0) :
    (specFunctionRationalUnit g hg : (Spec (CommRingCat.of A)).functionField) =
      (Spec (CommRingCat.of A)).germToFunctionField ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv g) := rfl

theorem specFunctionRationalUnit_effective (g : A) (hg : g ≠ 0) :
    (principalCartierDivisor (Spec (CommRingCat.of A)) (specFunctionRationalUnit g hg)).IsEffective :=
  (CartierDivisor.isEffective_principalCartierDivisor_iff _).mpr
    ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).inv g, rfl⟩

end Functions

section Model

variable {K : Type u} [Field K] [CharZero K] {A : Type u} [CommRing A] [IsDomain A]
  [Algebra K A] [IsNoetherianRing A] {N : ℕ}
  [SmoothOfRelativeDimension (N + 1) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]

attribute [local instance] specAlgebraOver cartierBaseOpenAlgebra

/-- From the original functions, construct one proper projective SNC model supporting the
Jacobian, hyperplane and every nonzero generator, with the exact coefficient minimum and the
strict-transform coefficients. Bad points of the original family give bad members on this model. -/
theorem exists_nondegenerate_function_snc_model
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 1))
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (hφ : φ.toRingHom.FormallyEtale)
    [(Ideal.span {φ (MvPolynomial.X 0)}).IsPrime]
    {J : Type} [Finite J] (g : J → A) (hnd : ∃ j, g j ∉ Ideal.span {φ (MvPolynomial.X 0)}) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension (N + 1) (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ Spec (CommRingCat.of A)) (_ : IsDominant ρ)
      (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ) (_ : IsProjective ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T (N + 1)) (r : ℕ) (ξ : Fin r → T)
      (Gc : CartierDivisor T) (hGc : Gc.IsEffective),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K (N + 1) ξ ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
          cT etaleCharts_cover) (z : T) = 0) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (z : T) = 0) ∧
      (∀ (j : {j : J // g j ≠ 0}) (z : CodimensionOnePoint T), (z : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2))) (z : T) = 0) ∧
      (∀ z : CodimensionOnePoint T, (z : T) ∉ Set.range ξ → cartierCoefficient Gc (z : T) = 0) ∧
      effectiveCartierIdealSheaf Gc hGc = (⨆ j : {j : J // g j ≠ 0},
        effectiveCartierIdealSheaf (principalCartierDivisor (Spec (CommRingCat.of A))
          (specFunctionRationalUnit (g j.1) j.2)) (specFunctionRationalUnit_effective (g j.1) j.2)).comap ρ ∧
      (∀ t : T,
        (∀ j : {j : J // g j ≠ 0}, cartierCoefficient Gc t ≤ cartierCoefficient
          (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
            (specFunctionRationalUnit (g j.1) j.2))) t) ∧
        ∃ j : {j : J // g j ≠ 0}, cartierCoefficient Gc t = cartierCoefficient
          (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
            (specFunctionRationalUnit (g j.1) j.2))) t) ∧
      (∃ s₀ : Fin r,
        (ρ (ξ s₀)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)} ∧
        Function.Bijective (ρ.stalkMap (ξ s₀)) ∧
        cartierCoefficient (cartierPullback ρ (principalCartierDivisor (Spec (CommRingCat.of A))
          (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0))) (ξ s₀) = 1 ∧
        cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
          cT etaleCharts_cover) (ξ s₀) = 0 ∧ cartierCoefficient Gc (ξ s₀) = 0) ∧
      ∀ (x : Spec (CommRingCat.of A)) (M : ℕ), 1 ≤ M →
        ModelThresholdBadAt cX 1 1
          (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1)) x
          (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M →
        ∃ s₁ : Fin r,
          (M : ℤ) * (1 - cartierCoefficient (crepantBoundaryCartier ρ hρ cX 1 1
            (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
            cT etaleCharts_cover) (ξ s₁)) ≤ cartierCoefficient Gc (ξ s₁) ∧
          x ∈ ρ '' closure ({ξ s₁} : Set T) := by
  classical
  have : Smooth (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth (N + 1) _
  obtain ⟨j₀, hj₀⟩ := hnd
  have hgj₀ : g j₀ ≠ 0 := fun h => hj₀ (h ▸ Ideal.zero_mem _)
  have : Nonempty {j : J // g j ≠ 0} := ⟨⟨j₀, hgj₀⟩⟩
  let u : {j : J // g j ≠ 0} → (Spec (CommRingCat.of A)).functionFieldˣ :=
    fun j => specFunctionRationalUnit (g j.1) j.2
  let D := fun j => principalCartierDivisor (Spec (CommRingCat.of A)) (u j)
  have hD : ∀ j, (D j).IsEffective := fun j => specFunctionRationalUnit_effective (g j.1) j.2
  let H := principalCartierDivisor (Spec (CommRingCat.of A))
    (etaleChartCoordinateRationalUnit (specAlgebraEtaleChart φ hφ) 0)
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, hinj, hcoh, hsnc,
      hsupp, hH, hDsupp, -, -, -, Gc, hGc, hGcI, hGc0, hmin, -⟩ :=
    exists_projective_snc_model_principalizing_sum cX 1 1
      (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1))
      (fun _ : Unit => H) D hD
      (Empty.elim : Empty → (Spec (CommRingCat.of A)).IdealSheafData) (fun j => j.elim)
  have hs₀ := exists_strictTransform_member_coefficients ρ hρ cX cT φ hφ ξ hcoh (hH ())
    (g j₀) (u ⟨j₀, hgj₀⟩) rfl hj₀ Gc hGc (fun t => (hmin t).1 ⟨j₀, hgj₀⟩)
  refine ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hproj, hρ, cT, r, ξ, Gc, hGc,
    hinj, hcoh, hsnc, hsupp, hH (), hDsupp, hGc0, hGcI, hmin, hs₀, ?_⟩
  intro x M hM hbad
  have hbad' : ModelThresholdBadAt cX 1 1
      (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A)) 1)) x
      (fun j => (u j : (Spec (CommRingCat.of A)).functionField)) M := by
    obtain ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxe, hpos, hineq⟩ := hbad
    exact ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hxe, hpos,
      fun j hj => hineq j.1 hj⟩
  exact exists_bad_snc_member_of_modelThresholdBadAt cX u hD M hM ρ hρ cT ξ hinj hcoh hsnc
    hsupp Gc hGc hGc0 hGcI x hbad'

end Model

end MixedFujita
