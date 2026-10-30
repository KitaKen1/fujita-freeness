/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
The centre of a valuation of the function field on a proper model. Let ρ : T → V be proper with
T integral, R a valuation subring of the function field of T, and i₂ : Spec R → V a morphism with
which the generic point of T forms a commutative square. The valuative criterion lifts Spec R to
T; the image t₀ of the closed point is the centre: the local ring at t₀ maps to R by a local
homomorphism compatible with the inclusions into the function field, and ρ(t₀) is the image of
the closed point under i₂. Only the existence part of the valuative criterion is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {T V : Scheme.{u}} [IsIntegral T]

/-- The centre of a valuation subring of the function field on a proper model. -/
theorem exists_center_of_valuationSubring (ρ : T ⟶ V) [IsProper ρ]
    (R : ValuationSubring T.functionField) (i₂ : Spec (CommRingCat.of R) ⟶ V)
    (hsq : T.fromSpecStalk (genericPoint T) ≫ ρ =
      Spec.map (CommRingCat.ofHom (algebraMap R T.functionField)) ≫ i₂) :
    ∃ (t₀ : T) (φ₀ : T.presheaf.stalk t₀ ⟶ CommRingCat.of R), IsLocalHom φ₀.hom ∧
      ρ t₀ = i₂ (IsLocalRing.closedPoint R) ∧
      ∀ g : T.presheaf.stalk t₀,
        algebraMap R T.functionField (φ₀ g) = algebraMap (T.presheaf.stalk t₀) T.functionField g := by
  let S : ValuativeCommSq ρ :=
    { R := R
      K := T.functionField
      i₁ := T.fromSpecStalk (genericPoint T)
      i₂ := i₂
      commSq := ⟨hsq⟩ }
  have hp : IsProper ρ := inferInstance
  rw [IsProper.eq_valuativeCriterion] at hp
  obtain ⟨l, hl₁, hl₂⟩ := ((ValuativeCriterion.existence hp.1.1.1) S).exists_lift
  refine ⟨l (IsLocalRing.closedPoint R), Scheme.stalkClosedPointTo l, inferInstance, ?_, ?_⟩
  · have h := congrArg (fun f : Spec (CommRingCat.of R) ⟶ V => f (IsLocalRing.closedPoint R)) hl₂
    simpa only [Scheme.Hom.comp_apply] using h
  · have hspec : genericPoint T ⤳ l (IsLocalRing.closedPoint R) :=
      (genericPoint_spec T).specializes trivial
    have hl := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R T.functionField)) ≫
        Spec.map (Scheme.stalkClosedPointTo l) ≫ T.fromSpecStalk (l (IsLocalRing.closedPoint R)) =
        Spec.map (T.presheaf.stalkSpecializes hspec) ≫
          T.fromSpecStalk (l (IsLocalRing.closedPoint R)) := by
      rw [hl, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact hl₁
    rw [← Category.assoc] at h1
    have h2 := (cancel_mono (T.fromSpecStalk (l (IsLocalRing.closedPoint R)))).mp h1
    rw [← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    intro g
    exact congrArg (fun f => f.hom g) h3

end MixedFujita
