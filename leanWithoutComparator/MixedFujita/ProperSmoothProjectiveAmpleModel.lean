/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ChowCartierAmpleModel
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.BirationalComposition
public import MixedFujita.BirationalLogPairDescent
public import MixedFujita.KodairaLemmaStatementProof

/-! 任意proper整源の元ampleを備えた滑らかな射影的双有理モデル。 See reports/check-241-general-nef-chow-proper-big-add-nef.json for the verified scope. Arbitrary original nef mixed nonnegativity and the original unrestricted-proper BigAddNefStatement are proved. Actual Chow and resolution supply a smooth projective source internally. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Every proper integral source in characteristic zero has an actual
smooth projective birational model with an original ample Cartier divisor.
No projective embedding or ample class on the target is assumed. -/
theorem proper_integral_exists_smooth_projective_birational_ample_model
    (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim X = n) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T) (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (q : T ⟶ X) (_ : IsDominant q) (_ : q.IsOver (Spec (CommRingCat.of K))) (_ : IsProper q),
      Function.Bijective (dominantFunctionFieldAlgHom (K := K) q) ∧
        topologicalKrullDim T = n ∧ ∃ A : CartierDivisor T, CartierIsAmpleProj K A := by
  obtain ⟨Y, hY, hYo, p, hover, hproj, hsurj, U, hU, hiso, A, hA⟩ :=
    proper_integral_exists_chow_model_with_ample_cartier K (X := X)
  let := hY
  let := hYo
  let := hover
  let := hproj
  let := hsurj
  let := hiso
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  have hp : Function.Bijective (dominantFunctionFieldAlgHom (K := K) p) :=
    dominantFunctionFieldMap_bijective_of_isIso_nonempty_restrict p U hU
  have hdimY : topologicalKrullDim Y = n :=
    (birational_topologicalKrullDim_eq p hp).trans hdim
  obtain ⟨cY⟩ := nonempty_etaleChart_of_charZero (K := K) hdimY
  obtain ⟨T, hT, hTo, hTN, hTs, ρ, hdom, hrover, hrprop, hρ, cT, r, ξ,
      hinj, hcoh, hsnc, hsupp, hG, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cY (1 : Y.functionFieldˣ) 1 0
      (fun i : PEmpty.{1} => i.elim) hA
  let := hT
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hrover
  let := hrprop
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  let q := ρ ≫ p
  refine ⟨T, inferInstance, inferInstance, inferInstance, inferInstance, q,
    inferInstance, inferInstance, inferInstance, ?_, etaleChart_topologicalKrullDim cT,
    J, cartierIsAmpleProj_of_veryAmple hJ⟩
  exact dominantFunctionFieldAlgHom_comp_bijective p ρ hp hρ

end MixedFujita
