/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ExceptionalCartierProjectionFormula
public import MixedFujita.GlobalSectionsOfPushforwardIso
public import MixedFujita.CartierGradedPullback
public import MixedFujita.CartierBigDefinition

/-! 非零切断不要の実Cartier引き戻し全切断数・bigness同値。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Actual module pullback preserves all original section counts across a
proper birational normal map. The zero exceptional divisor and the actual
projection formula replace any global-section assumption on the Cartier class. -/
theorem proper_birational_actual_cartier_pullback_sections_finrank
    (K : Type u) [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p] [p.IsOver (Spec (CommRingCat.of K))]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (D : CartierDivisor X) :
    Module.finrank K Γ((Scheme.Modules.pullback p).obj D.sheaf, ⊤) =
      Module.finrank K Γ(D.sheaf, ⊤) := by
  let b := effectiveExceptionalCartierTwistedPushforwardIso hnorm hnormT p hp
    (0 : CartierDivisor T) CartierDivisor.isEffective_zero (fun t _ => cartierCoefficient_zero _) D
  let a : D.sheaf ≅ (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback p).obj D.sheaf) :=
    b ≪≫ (Scheme.Modules.pushforward p).mapIso
      (tensorIso (Iso.refl _) (cartierZeroSheafIso T) ≪≫ rightUnitor _)
  exact (pushforwardGlobalSectionsBaseLinearEquiv K p _).finrank_eq.symm.trans
    (moduleIsoGlobalSectionsBaseLinearEquiv K a).finrank_eq.symm


/-- Every actual pulled Cartier representative preserves and reflects
original bigness under a proper birational normal map of the same dimension. -/
theorem proper_birational_cartier_representative_isBig_iff
    (K : Type u) [Field K] {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
    [IsLocallyNoetherian X] [IsLocallyNoetherian T]
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    (p : T ⟶ X) [IsDominant p] [IsProper p] [p.IsOver (Spec (CommRingCat.of K))]
    (hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t))
    (hdim : topologicalKrullDim T = topologicalKrullDim X)
    (D : CartierDivisor X) (F : CartierDivisor T)
    (a : (Scheme.Modules.pullback p).obj D.sheaf ≅ F.sheaf) :
    CartierIsBig K F ↔ CartierIsBig K D := by
  have hcounts (m : ℕ) : Module.finrank K Γ((m • F).sheaf, ⊤) =
      Module.finrank K Γ((m • D).sheaf, ⊤) :=
    (moduleIsoGlobalSectionsBaseLinearEquiv K (cartierPullbackGradedIso D p F a m)).finrank_eq.symm.trans
      (proper_birational_actual_cartier_pullback_sections_finrank K p hp hnorm hnormT (m • D))
  constructor
  · rintro ⟨d, hd, c, hc, hfreq⟩
    refine ⟨d, hdim.symm.trans hd, c, hc, hfreq.mono fun m hm => ?_⟩
    rwa [hcounts] at hm
  · rintro ⟨d, hd, c, hc, hfreq⟩
    refine ⟨d, hdim.trans hd, c, hc, hfreq.mono fun m hm => ?_⟩
    rwa [hcounts]

end MixedFujita
