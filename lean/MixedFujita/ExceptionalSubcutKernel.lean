/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ExceptionalCartierProjectionFormula
public import MixedFujita.CartierSectionLifting

/-! 実例外切断kernelのOXへの単射とCartier商への切断持ち上げ。 See reports/check-244-lc-critical-cut-roundup-kernel.json for the verified scope. Actual lc critical Cartier cuts and effective exceptional roundup parts are constructed. An original projective effective lc non-klt pair yields an internal smooth projective model, nonempty cut, coherent embedded kernel and usual-KV-based H1 vanishing and quotient section lifting. Usual KV and cut-generator existence remain unproved; the kernel is not identified with a reduced lc-center ideal; klt BPF and full F1/F2 remain incomplete. -/

@[expose] public section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- An effective exceptional twist and any actual effective cut give an actual
monomorphism of the cut kernel's direct image into the ORIGINAL structure module.
No local vanishing or identification with a reduced lc-center ideal is assumed. -/
theorem exceptional_subcut_pushforward_embeds_in_unit
    {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    (p : T ⟶ X) [IsDominant p] [IsProper p]
    (hp : Function.Bijective (dominantFunctionFieldMap p).hom)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (E S : CartierDivisor T) (hE : E.IsEffective)
    (hexc : ∀ t : CodimensionOnePoint T, Order.coheight (p (t : T)) = 1 →
      cartierCoefficient E (t : T) = 0) (hS : S.IsEffective) :
    ∃ j : (Scheme.Modules.pushforward p).obj (E - S).sheaf ⟶ SheafOfModules.unit X.ringCatSheaf,
      Mono j := by
  let f := cartierEffectiveInclusion E S hS
  let : Mono f := cartierEffectiveInclusion_mono E S hS
  let a := effectiveExceptionalCartierPushforwardUnitIso hnorm hnormT p hp E hE hexc
  refine ⟨(Scheme.Modules.pushforward p).map f ≫ a.inv, ?_⟩
  infer_instance


/-- H1 vanishing of an ACTUAL embedded submodule gives global lifting to its
actual Cartier-twisted cokernel. The embedded module need not be supplied as an
ideal-subsheme presentation or identified with a reduced closed subset. -/
theorem cartier_twisted_submodule_quotient_sections_surjective_of_H1
    {X : Scheme.{u}} [IsIntegral X] (P : CartierDivisor X) (I : X.Modules)
    (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono j]
    (hvan : Subsingleton (Scheme.Modules.Cohomology (P.sheaf ⊗ I) 1)) :
    Function.Surjective (Scheme.Modules.Hom.app
      (cokernel.π ((cartierTwistFunctor P).map j ≫ (rightUnitor P.sheaf).hom)) ⊤) := by
  let f := (cartierTwistFunctor P).map j ≫ (rightUnitor P.sheaf).hom
  have hseq : (ShortComplex.cokernelSequence f).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f) inferInstance inferInstance
  exact Scheme.Modules.sections_surjective hseq hvan

end MixedFujita
