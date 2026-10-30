/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantKltDescent
public import MixedFujita.BirationalBoundaryEffectivity
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField

/-!
An actual birational function-field isomorphism descends both a rational unit
and a rational top form. Combined with actual crepant klt and effectivity
descent, this constructs a klt pair downstairs in a prescribed Cartier linear
class. The denominator is unchanged; no canonical-bundle-formula input is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))]
  (hf : Function.Bijective (dominantFunctionFieldAlgHom (K := K) f))

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- The form-coordinate algebra structure is the canonical scheme function-field algebra. -/
theorem functionFieldBaseAlgebra_eq_scheme :
    functionFieldBaseAlgebra K X = Scheme.functionFieldBaseAlgebra K X := by
  apply Algebra.algebra_ext
  intro a
  calc
    (haveI := functionFieldBaseAlgebra K X; algebraMap K X.functionField a) =
        (X.germToFunctionField ⊤).hom (Scheme.Modules.baseRingToGlobalSections K X a) := rfl
    _ = Scheme.baseRingToFunctionField K X a :=
      (Scheme.baseRingToFunctionField_apply K X a).symm
    _ = (haveI := Scheme.functionFieldBaseAlgebra K X;
        algebraMap K X.functionField a) := by
      rw [Scheme.algebraMap_functionField_eq_baseRingToFunctionField]

include hf

/-- Every specified rational unit descends through the actual birational field map. -/
theorem birational_rationalUnit_descent (ψ : X.functionFieldˣ) :
    ∃ φ : Y.functionFieldˣ,
      Units.map (dominantFunctionFieldMap f).hom.toMonoidHom φ = ψ := by
  let e := AlgEquiv.ofBijective (dominantFunctionFieldAlgHom (K := K) f) hf
  refine ⟨Units.map e.symm.toMonoidHom ψ, ?_⟩
  apply Units.ext
  change e (e.symm (ψ : X.functionField)) = (ψ : X.functionField)
  exact e.apply_symm_apply _

/-- Descend a specified rational top form by compensating for the actual chart Jacobian. -/
theorem birational_exists_crepantPullbackFormUnit (cY : EtaleChart K Y n)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) :
    ∃ fY : Y.functionFieldˣ, crepantPullbackFormUnit f hf cY fY cX = fX := by
  obtain ⟨fY, hform⟩ := birational_rationalUnit_descent f hf
    (fX * (isUnit_chartRelativeJacobianDet_of_bijective f hf cY cX).unit⁻¹)
  refine ⟨fY, ?_⟩
  unfold crepantPullbackFormUnit
  rw [hform]
  simp [mul_assoc]

/-- Actual birational integral finite-type schemes have the same geometric dimension. -/
theorem birational_topologicalKrullDim_eq
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  rw [TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K]
  have h := congrArg (fun t : Cardinal => (t.toNat : WithBot ℕ∞))
    (AlgEquiv.ofBijective (dominantFunctionFieldAlgHom (K := K) f) hf).trdeg_eq.symm
  rw [← functionFieldBaseAlgebra_eq_scheme (K := K) (X := X),
    ← functionFieldBaseAlgebra_eq_scheme (K := K) (X := Y)]
  exact h

/-- Construct an effective klt pair in the prescribed target linear class.
The actual top form and Cartier pullback recover the supplied source data,
and the source's denominator is preserved. -/
theorem birational_logPair_descent [CharZero K]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))] [IsProper f]
    (hnormY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (hnormX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcovX : CodimOneChartCovered n K X)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (DX : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d DX)
    (hklt : LogPairIsKlt cX fX d DX) (cY : EtaleChart K Y n)
    (H : CartierDivisor Y) (a : ℕ) (ψ : X.functionFieldˣ)
    (hDX : DX = a • cartierPullback f H + principalCartierDivisor X ψ) :
    ∃ (fY : Y.functionFieldˣ) (φ : Y.functionFieldˣ),
      LogPairBoundaryEffective cY fY d (a • H + principalCartierDivisor Y φ) ∧
      LogPairIsKlt cY fY d (a • H + principalCartierDivisor Y φ) ∧
      cartierPullback f (a • H + principalCartierDivisor Y φ) = DX ∧
      crepantPullbackFormUnit f hf cY fY cX = fX := by
  obtain ⟨fY, hform⟩ := birational_exists_crepantPullbackFormUnit f hf cY cX fX
  obtain ⟨φ, hφ⟩ := birational_rationalUnit_descent f hf ψ
  have hpull : cartierPullback f (a • H + principalCartierDivisor Y φ) = DX := by
    rw [cartierPullback_add, cartierPullback_nsmul, cartierPullback_principal, hφ]
    exact hDX.symm
  refine ⟨fY, φ, ?_, ?_, hpull, hform⟩
  · apply logPairBoundaryEffective_of_crepant_pullback f hf hnormY hnormX hcovX
      cY fY d (a • H + principalCartierDivisor Y φ) cX
    simpa only [hform, hpull] using heff
  · apply logPairIsKlt_of_crepant_pullback f hf cY fY d hd
      (a • H + principalCartierDivisor Y φ) cX
    simpa only [hform, hpull] using hklt

end MixedFujita
