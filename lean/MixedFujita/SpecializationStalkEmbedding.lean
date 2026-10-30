/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GeometricJacobianBound
public import MixedFujita.BirationalPrimeLifts

/-! Actual stalk maps needed at an intersection with a prime divisor.
Specialization embeds the intersection stalk in the divisor stalk. A
dominant model map therefore gives an injective map from the image's
stalk through the intersection, with actual germ and scalar compatibility.
No identification with a supplied formal valuation is used. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower

/-- Specialization between actual stalks of an integral scheme is injective. -/
theorem integral_stalkSpecializes_injective {t P : T} (h : t ⤳ P) :
    Function.Injective (T.presheaf.stalkSpecializes h).hom := by
  have hc : T.presheaf.stalkSpecializes h ≫
      CommRingCat.ofHom (algebraMap (T.presheaf.stalk t) T.functionField) =
      CommRingCat.ofHom (algebraMap (T.presheaf.stalk P) T.functionField) :=
    T.presheaf.stalkSpecializes_comp ((genericPoint_spec T).specializes trivial) h
  intro a b hab
  apply IsFractionRing.injective (T.presheaf.stalk P) T.functionField
  have ha := ConcreteCategory.congr_hom hc a
  have hb := ConcreteCategory.congr_hom hc b
  exact ha.symm.trans ((congrArg (algebraMap (T.presheaf.stalk t) T.functionField) hab).trans hb)

/-- Dominance alone makes each actual stalk map injective. -/
theorem dominant_stalkMap_injective (ρ : T ⟶ X) [IsDominant ρ] (t : T) :
    Function.Injective (ρ.stalkMap t).hom := by
  intro a b hab
  apply IsFractionRing.injective (X.presheaf.stalk (ρ t)) X.functionField
  apply (dominantFunctionFieldMap ρ).hom.injective
  rw [dominantFunctionFieldMap_algebraMap, dominantFunctionFieldMap_algebraMap, hab]

variable {K : Type u} [Field K]
  [X.Over (Spec (.of K))] [T.Over (Spec (.of K))]

/-- The generization map of actual stalks respects the existing base-field algebras. -/
noncomputable def schemeStalkSpecializesAlgHom {t P : T} (h : t ⤳ P) :
    T.presheaf.stalk P →ₐ[K] T.presheaf.stalk t :=
  { (T.presheaf.stalkSpecializes h).hom with
    commutes' := fun c => by
      change T.presheaf.stalkSpecializes h
        (T.presheaf.germ ⊤ P trivial (Scheme.Modules.baseRingToGlobalSections K T c)) =
        T.presheaf.germ ⊤ t trivial (Scheme.Modules.baseRingToGlobalSections K T c)
      exact ConcreteCategory.congr_hom
        (T.presheaf.germ_stalkSpecializes (U := ⊤) (y := P) (x := t) trivial h) _ }

/-- The actual map from the image of an intersection point to the prime stalk. -/
noncomputable def modelIntersectionStalkMap (ρ : T ⟶ X) [ρ.IsOver (Spec (.of K))]
    {t P : T} (h : t ⤳ P) : X.presheaf.stalk (ρ P) →ₐ[K] T.presheaf.stalk t :=
  (schemeStalkSpecializesAlgHom (K := K) h).comp (schemeStalkMapAlgHom (K := K) ρ P)

/-- The intersection map is automatically injective, so the strict DVR
estimate does not need an extra injectivity certificate. -/
theorem modelIntersectionStalkMap_injective (ρ : T ⟶ X) [IsDominant ρ]
    [ρ.IsOver (Spec (.of K))] {t P : T} (h : t ⤳ P) :
    Function.Injective (modelIntersectionStalkMap (K := K) ρ h) :=
  (integral_stalkSpecializes_injective h).comp (dominant_stalkMap_injective ρ P)

/-- The map through the intersection agrees with the generic prime map
after actual specialization on the target. -/
theorem modelIntersectionStalkMap_apply (ρ : T ⟶ X) [ρ.IsOver (Spec (.of K))]
    {t P : T} (h : t ⤳ P) (a : X.presheaf.stalk (ρ P)) :
    modelIntersectionStalkMap (K := K) ρ h a =
      ρ.stalkMap t (X.presheaf.stalkSpecializes (h.map ρ.continuous) a) :=
  (ρ.stalkSpecializes_stalkMap_apply t P h a).symm

end MixedFujita
