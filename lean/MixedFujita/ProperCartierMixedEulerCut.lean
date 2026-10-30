/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedEulerDifference
public import MixedFujita.ProperCartierFlagEuler
public import SGA.Foundations.Cohomology.QuasiCoherentAbelian

/-! 混合Euler一次差分と実有効Cartier切断先Euler標数の同定。 See reports/check-219-mixed-euler-intersection-foundation.json for the verified scope. The ordinary mixed-intersection dimension bound in dimension at least two remains unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The first actual mixed Euler difference is the Euler characteristic of
the actual effective Cartier cut, pushed to the original proper scheme.
Coherence and all cohomology finiteness are derived from the actual exact sequence. -/
theorem proper_cartierMixedEulerDifference_singleton_eq_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (H E : CartierDivisor X) (hH : H.IsEffective) :
    cartierMixedEulerDifference K [H] E =
      Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K))
        ((Scheme.Modules.pushforward (effectiveCartierIdealSheaf H hH).subschemeι).obj
          ((Scheme.Modules.pullback (effectiveCartierIdealSheaf H hH).subschemeι).obj
            (E + H).sheaf)) := by
  let S := cartierCutShortComplex (E + H) H hH
  have hS : S.ShortExact := cartierCutShortComplex_shortExact (E + H) H hH
  let : S.X₁.IsCoherent := by
    change (E + H - H).sheaf.IsCoherent
    let := (E + H - H).isInvertible_sheaf
    exact invertible_module_isCoherent _
  let : S.X₂.IsCoherent := by
    change (E + H).sheaf.IsCoherent
    let := (E + H).isInvertible_sheaf
    exact invertible_module_isCoherent _
  let : S.X₁.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : S.X₃.IsCoherent := CohomologyAux.isCoherent_X₃_of_shortExact hS
  have h := proper_moduleEulerChar_of_shortExact K hS
  change Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (E + H).sheaf =
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (E + H - H).sheaf +
      Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K))
        ((Scheme.Modules.pushforward (effectiveCartierIdealSheaf H hH).subschemeι).obj
          ((Scheme.Modules.pullback (effectiveCartierIdealSheaf H hH).subschemeι).obj
            (E + H).sheaf)) at h
  rw [moduleEulerChar_congr K (eqToIso (congrArg CartierDivisor.sheaf
    (add_sub_cancel_right E H)))] at h
  change Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) (E + H).sheaf -
    Scheme.Modules.eulerChar (X ↘ Spec (CommRingCat.of K)) E.sheaf = _
  omega


/-- Along the actual closed Cartier subscheme the same coefficient is its
own Euler characteristic with the pulled line bundle, not an abstract quotient. -/
theorem proper_cartierMixedEulerDifference_singleton_eq_cut_eulerChar
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (H E : CartierDivisor X) (hH : H.IsEffective)
    [(effectiveCartierIdealSheaf H hH).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf H hH).subschemeι.IsOver (Spec (CommRingCat.of K))] :
    cartierMixedEulerDifference K [H] E =
      Scheme.Modules.eulerChar ((effectiveCartierIdealSheaf H hH).subscheme ↘ Spec (CommRingCat.of K))
        ((Scheme.Modules.pullback (effectiveCartierIdealSheaf H hH).subschemeι).obj
          (E + H).sheaf) := by
  rw [proper_cartierMixedEulerDifference_singleton_eq_cut K H E hH]
  let M := (Scheme.Modules.pullback (effectiveCartierIdealSheaf H hH).subschemeι).obj
    (E + H).sheaf
  let := (E + H).isInvertible_sheaf
  let : M.IsQuasicoherent := invertibleModule_isQuasicoherent M
  have h := Scheme.Modules.eulerChar_pushforward (X ↘ Spec (CommRingCat.of K))
    (effectiveCartierIdealSheaf H hH).subschemeι M
  simpa only [HomIsOver.comp_over] using h

end MixedFujita
