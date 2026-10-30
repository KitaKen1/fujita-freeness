/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleH1DirectImageDescent
public import MixedFujita.ExceptionalCartierProjectionFormula
public import MixedFujita.CartierPulledCoherentTwist

/-! 実射影公式による双有理例外捻りから元Cartier H1消滅。 See reports/check-242-H1-descent-klt-adjoint-vanishing.json for the verified scope. Actual H1 direct-image descent needs no local higher acyclicity. The usual smooth SNC KV statement implies actual signed-roundup and original projective klt adjoint H1 vanishing. Usual general KV is still an explicit unproved input; klt BPF global generation, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open TopCat.Presheaf TopCat.Sheaf
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Vanishing on a proper birational normal model with an actual effective
exceptional twist descends to the ORIGINAL Cartier sheaf. The direct-image
isomorphism is constructed internally from the exact projection formula. -/
theorem proper_birational_exceptional_cartier_H1_descent
    (K : Type u) [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p] [p.IsOver (Spec (CommRingCat.of K))]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E : CartierDivisor T) (hE : E.IsEffective)
    (hexc : ∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0) (D : CartierDivisor X)
    (hvan : Subsingleton (Scheme.Modules.Cohomology
      ((Scheme.Modules.pullback p).obj D.sheaf ⊗ E.sheaf) 1)) :
    Subsingleton (Scheme.Modules.Cohomology D.sheaf 1) := by
  let := E.isInvertible_sheaf
  let : E.sheaf.IsCoherent := invertible_module_isCoherent _
  let : ((Scheme.Modules.pullback p).obj D.sheaf ⊗ E.sheaf).IsCoherent :=
    cartierPulledTensor_isCoherent D p E.sheaf
  exact proper_module_H1_subsingleton_of_pushforward_iso K p _ D.sheaf
    (effectiveExceptionalCartierTwistedPushforwardIso hnorm hnormT p hp E hE hexc D) hvan


/-- Pure actual pullback H1 vanishing on a proper birational normal model
implies original H1 vanishing; no local inverse-image acyclicity is required. -/
theorem proper_birational_actual_cartier_pullback_H1_descent
    (K : Type u) [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p] [p.IsOver (Spec (CommRingCat.of K))]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (D : CartierDivisor X)
    (hvan : Subsingleton (Scheme.Modules.Cohomology ((Scheme.Modules.pullback p).obj D.sheaf) 1)) :
    Subsingleton (Scheme.Modules.Cohomology D.sheaf 1) := by
  apply proper_birational_exceptional_cartier_H1_descent K p hp hnorm hnormT 0
    CartierDivisor.isEffective_zero (fun t _ => cartierCoefficient_zero _) D
  let : Subsingleton (Scheme.Modules.Cohomology ((Scheme.Modules.pullback p).obj D.sheaf) 1) := hvan
  exact (actualCohomologyLinearEquivOfIso
    (tensorIso (Iso.refl _) (cartierZeroSheafIso T) ≪≫ rightUnitor _) 1).subsingleton

end MixedFujita
