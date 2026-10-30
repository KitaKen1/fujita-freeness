/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GenericMixedEulerComparison
public import MixedFujita.PulledModuleEulerMvPolynomial
public import MixedFujita.ProperClosedImmersionDimension

/-! 最高次実混合係数の真閉支持消滅と一般点同型不変性。 See reports/check-224-effective-cut-generic-intersection.json for the verified scope. Mixed positivity on the actual cut and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- In top dimension, a coherent coefficient supported in ANY proper
closed subset contributes zero. The actual closed subscheme, its smaller
dimension and the nilpotent-support filtration are all internal. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_vanish_of_proper_support
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (M : Y.Modules) [M.IsCoherent]
    (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (T : Set Y) (hT : IsClosed T) (hproper : T ≠ Set.univ)
    (hM : CohomologyAux.VanishesOff M T) :
    cartierPulledModuleMixedEulerDifference K p M D E = 0 := by
  let J : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩
  let j := J.subschemeι
  have hjrange : Set.range j = T := by
    change Set.range J.subschemeι = T
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let : J.subscheme.Over (Spec (CommRingCat.of K)) :=
    ⟨j ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  let : j.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  let : IsProper (J.subscheme ↘ Spec (CommRingCat.of K)) := by
    change IsProper (j ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  have hdimJ : topologicalKrullDim J.subscheme ≤ n :=
    properClosedImmersion_topologicalKrullDim_le_predecessor j
      (by rw [hjrange]; exact hproper) n hdim
  apply cartierPulledModuleMixedEulerDifference_vanish_of_closed_support
    K p D E j ?_ M (by simpa only [hjrange] using hM)
  intro N hN
  let := hN
  exact proper_cartierPulledModuleMixedEulerDifference_vanish_of_length K n hdimJ
    (j ≫ p) N D hlen E


/-- Actual generic morphism invariance for top mixed coefficients, with no
lower-support vanishing premise left to the caller. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_eq_of_generic_morphism
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q)
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set Y).Nonempty)
    (hφ : Function.Bijective (φ.app U)) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  apply cartierPulledModuleMixedEulerDifference_eq_of_generic_morphism K p D E ?_
    G Q φ U hU hne hφ
  intro N hN T hT hproper hNT
  let := hN
  exact proper_cartierPulledModuleMixedEulerDifference_top_vanish_of_proper_support
    K n hdim p N D hlen E T hT hproper hNT


/-- The actual top coefficient only depends on the coherent module on a
nonempty open. No chosen kernel/cokernel or supplied vanishing is needed. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_eq_of_open_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent]
    (W : Y.Opens) (hne : (W : Set Y).Nonempty)
    (e : (Scheme.Modules.pullback W.ι).obj Q ≅ (Scheme.Modules.pullback W.ι).obj G) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  apply cartierPulledModuleMixedEulerDifference_eq_of_open_iso K p D E ?_ G Q W hne e
  intro N hN T hT hproper hNT
  let := hN
  exact proper_cartierPulledModuleMixedEulerDifference_top_vanish_of_proper_support
    K n hdim p N D hlen E T hT hproper hNT


/-- Consequently top squarefree coefficients of the actual multivariate
Euler polynomial are invariant under actual generic coherent isomorphism. -/
theorem proper_cartierPulledModuleEulerMvPolynomial_top_coeff_eq_of_open_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ))
    (p : Y ⟶ X) (D : Fin (n + 1) → CartierDivisor X) (E : CartierDivisor X)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent]
    (W : Y.Opens) (hne : (W : Set Y).Nonempty)
    (e : (Scheme.Modules.pullback W.ι).obj Q ≅ (Scheme.Modules.pullback W.ι).obj G) :
    (cartierPulledModuleEulerMvPolynomial K p G (n + 1) (n + 1) D E).coeff
        (squarefreeExponent (n + 1)) =
      (cartierPulledModuleEulerMvPolynomial K p Q (n + 1) (n + 1) D E).coeff
        (squarefreeExponent (n + 1)) := by
  rw [cartierPulledModuleEulerMvPolynomial_squarefree_top_coeff,
    cartierPulledModuleEulerMvPolynomial_squarefree_top_coeff]
  exact congrArg (fun z : ℤ => (z : ℚ))
    (proper_cartierPulledModuleMixedEulerDifference_top_eq_of_open_iso K n hdim p
      (List.ofFn D) (by simp) E G Q W hne e)

end MixedFujita
