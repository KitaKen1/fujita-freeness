/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierNefPullback
public import MixedFujita.AmpleEffectiveComparison
public import MixedFujita.CartierPulledCoherentTwist

/-! 非零切断不要の全Cartier有理・実module引き戻し同型。 See reports/check-242-H1-descent-klt-adjoint-vanishing.json for the verified scope. Actual H1 direct-image descent needs no local higher acyclicity. The usual smooth SNC KV statement implies actual signed-roundup and original projective klt adjoint H1 vanishing. Usual general KV is still an explicit unproved input; klt BPF global generation, Ambro and full F1/F2 remain unproved. -/

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


/-- On an original projective target, the actual module pullback equals the
rational Cartier pullback for EVERY Cartier divisor, even without a nonzero
section. Two ample twists and the existing tensor equivalence cancel the twist. -/
theorem cartierPullback_sheaf_iso_modulePullback_of_ample_target
    (K : Type u) [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [X.Over (Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (D : CartierDivisor X) :
    Nonempty ((Scheme.Modules.pullback p).obj D.sheaf ≅ (cartierPullback p D).sheaf) := by
  obtain ⟨a, ha⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH D
  obtain ⟨b, hb⟩ := cartierIsAmpleProj_eventually_twist_globallyGenerated hH 0
  let k := max a b
  let F := k • H
  obtain ⟨s, hs⟩ := cartierIsGloballyGenerated_exists_nonzero_section (ha k (by omega))
  obtain ⟨t, ht⟩ := cartierIsGloballyGenerated_exists_nonzero_section (hb k (by omega))
  have hF : ∃ t : Γ(F.sheaf, ⊤), t ≠ 0 := by
    have he : (0 : CartierDivisor X) + k • H = F := zero_add _
    exact he ▸ ⟨t, ht⟩
  have hFD : ∃ s : Γ((F + D).sheaf, ⊤), s ≠ 0 := by
    have he : D + k • H = F + D := add_comm _ _
    exact he ▸ ⟨s, hs⟩
  obtain ⟨t, ht⟩ := hF
  obtain ⟨s, hs⟩ := hFD
  obtain ⟨aF⟩ := cartierPullback_sheaf_iso_modulePullback p F t ht
  obtain ⟨aFD⟩ := cartierPullback_sheaf_iso_modulePullback p (F + D) s hs
  let c : (cartierPullbackTwistFunctor F p).obj ((Scheme.Modules.pullback p).obj D.sheaf) ≅
      (cartierPullbackTwistFunctor F p).obj (cartierPullback p D).sheaf :=
    (cartierPullbackTensorIso F p D.sheaf).symm ≪≫
      (Scheme.Modules.pullback p).mapIso (cartierTensorSheafIso F D) ≪≫ aFD ≪≫
        eqToIso (congrArg CartierDivisor.sheaf (cartierPullback_add p F D)) ≪≫
          (cartierTensorSheafIso (cartierPullback p F) (cartierPullback p D)).symm ≪≫
            tensorIso aF.symm (Iso.refl _)
  exact ⟨(cartierPullbackTwistFunctor F p).preimageIso c⟩

end MixedFujita
