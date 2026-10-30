/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinCartierLinearReflection
public import MixedFujita.RegularEquationCartier

/-!
Glue actual rational local equations downstairs along an integral Stein-type map. Units of
the actual coordinate rings descend by the all-open ring isomorphisms; comparison in the
function fields reflects their transition equations. A Cartier divisor upstairs whose local
equations on a pulled-back open cover are specified pullbacks is therefore the actual pullback
of a constructed Cartier divisor, with no supplied descent divisor or transition units.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (g : X ⟶ Y) [IsDominant g]
  (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)

include happ

/-- Descend an actual regular unit through the given all-open ring isomorphisms. -/
theorem stein_regularUnit_descent (U : Y.Opens) (w : Γ(X, g ⁻¹ᵁ U)ˣ) :
    ∃ v : Γ(Y, U)ˣ, Units.map (g.app U).hom.toMonoidHom v = w := by
  let e := RingEquiv.ofBijective (g.app U).hom (happ U)
  refine ⟨Units.map e.symm.toMonoidHom w, ?_⟩
  apply Units.ext
  change e (e.symm (w : Γ(X, g ⁻¹ᵁ U))) = (w : Γ(X, g ⁻¹ᵁ U))
  exact e.apply_symm_apply _

/-- Local rational equations on a pulled-back cover construct actual Cartier descent. -/
theorem stein_exists_cartier_descent_of_rational_local_equations {ι : Type*}
    (U : ι → Y.Opens) [∀ i, Nonempty (U i)] (hcover : iSup U = ⊤)
    (f : ι → Y.functionFieldˣ) (E : CartierDivisor X)
    (hloc : ∀ i, ∀ x ∈ g ⁻¹ᵁ U i, E.IsLocalEquationAt x
      (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f i))) :
    ∃ H : CartierDivisor Y, E = cartierPullback g H := by
  letI : ∀ i, Nonempty (g ⁻¹ᵁ U i) := fun i => dominant_preimage_nonempty g (U i)
  have hsrc (i : ι) :
      rationalUnitClass X (g ⁻¹ᵁ U i)
        (Additive.ofMul (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f i))) =
      E |_ (g ⁻¹ᵁ U i) := by
    have := dominant_preimage_nonempty g (U i)
    exact rationalUnitClass_eq_restrict_of_forall_isLocalEquationAt E _ _ (hloc i)
  have htrans (i j : ι) :
      letI := integral_opens_inter_nonempty Y (U i) (U j)
      ∃ v : Γ(Y, U i ⊓ U j)ˣ,
        f i = Units.map (Y.germToFunctionField (U i ⊓ U j)).hom v * f j := by
    have := integral_opens_inter_nonempty Y (U i) (U j)
    have := dominant_preimage_nonempty g (U i ⊓ U j)
    have hi : g ⁻¹ᵁ (U i ⊓ U j) ≤ g ⁻¹ᵁ U i := fun x hx => hx.1
    have hj : g ⁻¹ᵁ (U i ⊓ U j) ≤ g ⁻¹ᵁ U j := fun x hx => hx.2
    have hc : rationalUnitClass X (g ⁻¹ᵁ (U i ⊓ U j))
        (Additive.ofMul (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f i))) =
      rationalUnitClass X (g ⁻¹ᵁ (U i ⊓ U j))
        (Additive.ofMul (Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f j))) := by
      rw [CartierDivisor.rationalUnitClass_eq_of_le hi (hsrc i),
        CartierDivisor.rationalUnitClass_eq_of_le hj (hsrc j)]
    obtain ⟨w, hw⟩ := (rationalUnitClass_eq_rationalUnitClass_iff X _ _ _).mp hc
    obtain ⟨v, hv⟩ := stein_regularUnit_descent g happ (U i ⊓ U j) w
    refine ⟨v, ?_⟩
    have hunit := dominantFunctionFieldMap_regularUnit g (U i ⊓ U j)
      (g ⁻¹ᵁ (U i ⊓ U j)) le_rfl v
    rw [Scheme.Hom.appLE_eq_app, hv] at hunit
    have heq : Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f i) =
        Units.map (dominantFunctionFieldMap g).hom.toMonoidHom
          (Units.map (Y.germToFunctionField (U i ⊓ U j)).hom v * f j) := by
      have hreg : Units.map (Y.germToFunctionField (U i ⊓ U j)).hom v =
          regularUnitToFunctionField Y (U i ⊓ U j) v :=
        (regularUnitToFunctionField_apply Y (U i ⊓ U j) v).symm
      rw [map_mul, hreg, hunit]
      exact hw.symm
    apply Units.ext
    apply (dominantFunctionFieldMap g).hom.injective
    exact congrArg (fun z : X.functionFieldˣ => (z : X.functionField)) heq
  obtain ⟨H, hH, -⟩ := cartierDivisor_existsUnique_of_rationalUnits Y U hcover f htrans
  refine ⟨H, ?_⟩
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.ge (Opens.mem_top (g x)))
  exact ⟨Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f i), hloc i x hi,
    cartierPullback_isLocalEquationAt g H x
      (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq (hH i).symm hi)⟩

end MixedFujita
