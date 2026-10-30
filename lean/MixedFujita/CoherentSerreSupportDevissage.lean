/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACoherentSerreVanishing
public import SGA.Foundations.Cohomology.Devissage
public import MixedFujita.ProperCartierCohomology

/-! 全連接Serre消滅と整閉支持上Serre消滅の同値。 See reports/check-237-component-ample-serre-section-lifting.json for the verified scope. Ampleness on actual integral components gives full coherent Serre vanishing on the original possibly nonreduced proper scheme and actual eventual quotient-section lifting on effective Cartier cuts over any field. Component ampleness is an explicit input. The cohomological converse, nonreduced cut global generation, universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- The generic SGA support induction applies to the actual all-positive-
degree Serre property. Nilpotent layers and reducible supports are internal. -/
theorem sgaEventuallyCohomologyVanish_of_integral_step
    {X : Scheme.{u}} [IsNoetherian X] (L : X.LineBundle)
    (hint : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      (∀ G : Z.Modules, G.IsCoherent → ∀ T : Set Z, IsClosed T → T ≠ Set.univ →
        CohomologyAux.VanishesOff G T → sgaEventuallyCohomologyVanish (L.pullback i) G) →
      ∀ G : Z.Modules, G.IsCoherent → sgaEventuallyCohomologyVanish (L.pullback i) G)
    (M : X.Modules) [M.IsCoherent] : sgaEventuallyCohomologyVanish L M := by
  refine CohomologyAux.prop_of_integral_step (sgaEventuallyCohomologyVanish L)
    (fun N _ hN => sgaEventuallyCohomologyVanish_zero_sections L N hN)
    (fun S hS _ _ _ h₁ h₃ => sgaEventuallyCohomologyVanish_of_shortExact L hS h₁ h₃)
    ?_ M
  intro Z i _ _ hsmall G hG
  apply (sgaEventuallyCohomologyVanish_closed_pushforward_iff L i G).mpr
  apply hint Z i ?_ G hG
  intro N hN T hT hTne hNT
  exact (sgaEventuallyCohomologyVanish_closed_pushforward_iff L i N).mp
    (hsmall N hN T hT hTne hNT)


/-- Ampleness on ALL actual integral closed supports supplies coherent
Serre vanishing on the original proper scheme, without reducing it. -/
theorem proper_sga_coherent_serreVanishing_of_integral_closed_ample
    (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (L : Y.LineBundle)
    (hL : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
      (L.pullback i).IsAmple)
    (M : Y.Modules) [M.IsCoherent] : sgaEventuallyCohomologyVanish L M := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  apply sgaEventuallyCohomologyVanish_of_integral_step L ?_ M
  intro Z i _ _ _ G hG
  let := hG
  let : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  exact sga_isAmple_coherent_serreVanishing K (L.pullback i) (hL Z i) G


/-- On a noetherian scheme, full coherent Serre vanishing is equivalent
to the same property on all actual integral closed supports. -/
theorem sga_coherent_serreVanishing_iff_integral_closed
    {X : Scheme.{u}} [IsNoetherian X] (L : X.LineBundle) :
    (∀ (M : X.Modules) [M.IsCoherent], sgaEventuallyCohomologyVanish L M) ↔
      ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
        (M : Z.Modules) [M.IsCoherent], sgaEventuallyCohomologyVanish (L.pullback i) M := by
  constructor
  · intro h Z i _ _ M _
    let := CohomologyAux.isCoherent_pushforward_of_isClosedImmersion i M
    exact (sgaEventuallyCohomologyVanish_closed_pushforward_iff L i M).mp (h _)
  · intro h M _
    apply sgaEventuallyCohomologyVanish_of_integral_step L ?_ M
    intro Z i _ _ _ N hN
    let := hN
    exact h Z i N

end MixedFujita
