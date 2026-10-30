/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GenericRankMixedEulerCoefficient

/-! 非被約proper源の最高次非負性還元と一つの正の閉商による正値性。 See reports/check-225-generic-rank-positive-quotient.json for the verified scope. Integral-unit nonnegativity and a positive actual quotient remain geometric inputs; full mixed ample positivity is unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- SGA coherent-support devissage and the actual generic-rank formula
reduce top nonnegativity on an ARBITRARY proper, possibly nonreduced source
to structure coefficients on its actual integral closed subschemes. No
coherent-coefficient positivity premise or multiplicity decomposition is supplied. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_integral_units
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ)) (p : Y ⟶ X)
    (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (hunit : ∀ (Z : Scheme.{u}) [IsIntegral Z] [Z.Over (Spec (CommRingCat.of K))]
      [IsProper (Z ↘ Spec (CommRingCat.of K))]
      (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))],
      0 ≤ cartierPulledModuleMixedEulerDifference K (i ≫ p) (CohomologyAux.unitModule Z) D E)
    (M : Y.Modules) [M.IsCoherent] :
    0 ≤ cartierPulledModuleMixedEulerDifference K p M D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  refine CohomologyAux.prop_of_integral_step
    (fun N : Y.Modules => 0 ≤ cartierPulledModuleMixedEulerDifference K p N D E)
    (fun N _ hN => by rw [cartierPulledModuleMixedEulerDifference_zero_sections K p N hN])
    ?_ ?_ M
  · intro S hS h₁ h₂ h₃ hP₁ hP₃
    let := h₁
    let := h₂
    let := h₃
    rw [cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S) hS]
    exact add_nonneg hP₁ hP₃
  · intro Z i _ _ hsmall G hG
    let : Z.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (Y ↘ Spec (CommRingCat.of K))⟩
    let : i.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (Z ↘ Spec (CommRingCat.of K)) := by
      change IsProper (i ≫ (Y ↘ Spec (CommRingCat.of K)))
      infer_instance
    let := hG
    rw [cartierPulledModuleMixedEulerDifference_closed_pushforward K p i G D E]
    exact proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_unit_nonneg K n
      (i.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim)
      (i ≫ p) G D hlen E (hunit Z i)


/-- For top coefficients on a possibly nonreduced proper source, ONE
positive closed quotient of the structure module suffices for strict
positivity. The coherent kernel is nonnegative by integral-unit devissage.
All exactness, coherence and projection identities are supplied internally;
no cycle-multiplicity decomposition is a premise. -/
theorem proper_cartierPulledModuleMixedEulerDifference_top_unit_positive_of_closed_quotient
    (K : Type u) [Field K] {X Y Z : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ (n + 1 : ℕ)) (p : Y ⟶ X)
    (D : List (CartierDivisor X)) (hlen : n < D.length) (E : CartierDivisor X)
    (hunit : ∀ (T : Scheme.{u}) [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
      [IsProper (T ↘ Spec (CommRingCat.of K))]
      (t : T ⟶ Y) [IsClosedImmersion t] [t.IsOver (Spec (CommRingCat.of K))],
      0 ≤ cartierPulledModuleMixedEulerDifference K (t ≫ p) (CohomologyAux.unitModule T) D E)
    (i : Z ⟶ Y) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (hpos : 0 < cartierPulledModuleMixedEulerDifference K (i ≫ p) (CohomologyAux.unitModule Z) D E) :
    0 < cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let O : Y.Modules := CohomologyAux.unitModule Y
  let N : Z.Modules := (Scheme.Modules.pullback i).obj O
  let a : N ≅ CohomologyAux.unitModule Z := Scheme.Modules.pullbackObjUnitIso i
  let : (CohomologyAux.unitModule Z).IsCoherent := invertible_module_isCoherent _
  let : (CohomologyAux.unitModule Z).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  let : N.IsQuasicoherent := Scheme.Modules.isQuasicoherent_of_iso a.symm
  let : N.IsFiniteType := Scheme.Modules.isFiniteType_of_iso a.symm
  let : N.IsCoherent := ⟨inferInstance, inferInstance⟩
  let : O.IsCoherent := invertible_module_isCoherent O
  let : O.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let Q := (Scheme.Modules.pushforward i).obj N
  let : Q.IsCoherent := CohomologyAux.isCoherent_pushforward_of_isClosedImmersion i N
  let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let π : O ⟶ Q := CohomologyAux.unitPushPull i O
  let : Epi π := inferInstance
  let S := ShortComplex.kernelSequence π
  have hS : S.ShortExact := CohomologyAux.shortExact_kernelSequence π
  let : S.X₁.IsQuasicoherent := CohomologyAux.isQuasicoherent_kernel π
  let : S.X₂.IsCoherent := inferInstanceAs O.IsCoherent
  let : S.X₃.IsCoherent := inferInstanceAs Q.IsCoherent
  let : S.X₁.IsCoherent := CohomologyAux.isCoherent_X₁_of_shortExact hS
  have hker := proper_cartierPulledModuleMixedEulerDifference_top_nonneg_of_integral_units
    K n hdim p D hlen E hunit S.X₁
  have h := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S) hS
  have hq : cartierPulledModuleMixedEulerDifference K p Q D E =
      cartierPulledModuleMixedEulerDifference K (i ≫ p) (CohomologyAux.unitModule Z) D E :=
    (cartierPulledModuleMixedEulerDifference_closed_pushforward K p i N D E).trans
      (cartierPulledModuleMixedEulerDifference_coefficient_iso K (i ≫ p) D E a)
  change cartierPulledModuleMixedEulerDifference K p O D E =
    cartierPulledModuleMixedEulerDifference K p S.X₁ D E +
      cartierPulledModuleMixedEulerDifference K p Q D E at h
  change 0 < cartierPulledModuleMixedEulerDifference K p O D E
  rw [h, hq]
  exact add_pos_of_nonneg_of_pos hker hpos

end MixedFujita
