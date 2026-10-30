/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffinePulledMixedEulerProjection
public import MixedFujita.GenericRankMixedEulerCoefficient
public import MixedFujita.ProperCoherentPushforward
public import MixedFujita.MixedAmpleCartierIntersection
public import MixedFujita.ProjectiveCartierSheafPullback

/-! 有限優勢写像の全最高次混合係数を比較する同じ正整数倍を内部構成。 See reports/check-232-nef-semiample-mixed-nonnegative.json for the verified scope. One original nef factor with a semiample tail and numerical-trivial-factor vanishing are proved in the declared scope. General nef-plus-ample ampleness, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A finite dominant map between equidimensional proper integral sources
multiplies EVERY actual top mixed coefficient by the SAME positive integer.
The rank and its positivity are constructed internally using an ample test. -/
theorem finite_dominant_exists_positive_top_mixed_multiplier
    (K : Type u) [Field K] [Infinite K] {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [Y.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
    [IsProper (Y ↘ Spec (CommRingCat.of K))] [IsProper (Z ↘ Spec (CommRingCat.of K))]
    (n : ℕ) (hn : 1 ≤ n) (hdimY : topologicalKrullDim Y = n) (hdimZ : topologicalKrullDim Z = n)
    (hProj : ∃ A : CartierDivisor Y, CartierIsAmpleProj K A)
    (f : Z ⟶ Y) [IsFinite f] [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))] :
    ∃ k : ℕ, 0 < k ∧ ∀ (X : Scheme.{u}) [IsIntegral X] (p : Y ⟶ X)
      (D : List (CartierDivisor X)), D.length = n → ∀ E : CartierDivisor X,
      cartierPulledModuleMixedEulerDifference K (f ≫ p) (CohomologyAux.unitModule Z) D E =
        (k : ℤ) * cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : IsAffineHom (pullback.diagonal (terminal.from Z)) :=
    CohomologyAux.isAffineHom_diagonal_of_isSeparated (Z ↘ Spec (CommRingCat.of K))
  let M := (Scheme.Modules.pushforward f).obj (CohomologyAux.unitModule Z)
  let : M.IsCoherent := proper_module_pushforward_isCoherent f _
  obtain ⟨W, hW, k, ⟨a⟩⟩ := coherent_exists_nonempty_open_unitBiproduct_iso M
  have hdim : topologicalKrullDim Y ≤ ((n - 1) + 1 : ℕ) := by
    simpa only [Nat.sub_add_cancel hn] using hdimY.le
  let : (CohomologyAux.unitBiproduct Y k).IsCoherent := unitBiproduct_isCoherent Y k
  have hformula : ∀ (X : Scheme.{u}) [IsIntegral X] (p : Y ⟶ X)
      (D : List (CartierDivisor X)), D.length = n → ∀ E : CartierDivisor X,
      cartierPulledModuleMixedEulerDifference K (f ≫ p) (CohomologyAux.unitModule Z) D E =
        (k : ℤ) * cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E := by
    intro X _ p D hlen E
    rw [← cartierPulledModuleMixedEulerDifference_affine_pushforward K p f]
    have h := proper_cartierPulledModuleMixedEulerDifference_top_eq_of_open_iso
      K (n - 1) hdim p D (by omega) E M (CohomologyAux.unitBiproduct Y k) W hW
      (modulePullbackUnitBiproductIso W.ι k ≪≫ a.symm)
    exact h.trans (proper_cartierPulledModuleMixedEulerDifference_unitBiproduct K p D E k)
  have hk : 0 < k := by
    obtain ⟨A, hA⟩ := hProj
    obtain ⟨m, hm, r, e, he, hover, g, hg, hgen, v, hrel⟩ := hA
    let := he
    have hgenZ : g ∉ ((f ≫ e) (genericPoint Z)).asHomogeneousIdeal := by
      simpa only [Scheme.Hom.comp_apply, dominant_map_genericPoint f] using hgen
    let HY := projectiveHyperplaneCartier e g hg hgen
    let HZ := projectiveHyperplaneCartier (f ≫ e) g hg hgenZ
    have hHZ : CartierIsAmpleProj K HZ := projectiveHyperplaneCartier_isAmpleProj_of_finite
      (f ≫ e) g hg hgenZ (by simp only [Category.assoc, hover, HomIsOver.comp_over])
    let b : (Scheme.Modules.pullback f).obj HY.sheaf ≅ HZ.sheaf :=
      projectiveHomogeneousCartierPullbackIso e f 1 g hg one_pos hgen hgenZ
    have hrep : ∀ j : ℕ, List.Forall₂
        (fun H J => Nonempty ((Scheme.Modules.pullback f).obj H.sheaf ≅ J.sheaf))
        (List.replicate j HY) (List.replicate j HZ) := by
      intro j
      induction j with
      | zero => exact .nil
      | succ j ih => exact .cons ⟨b⟩ ih
    have hpos : 0 < cartierPulledModuleMixedEulerDifference K f
        (CohomologyAux.unitModule Z) (List.replicate n HY) 0 := by
      rw [cartierPulledModuleMixedEulerDifference_unit_eq_of_representations K f (hrep n) 0 0
        ((Scheme.Modules.pullback f).mapIso (cartierZeroSheafIso Y) ≪≫
          Scheme.Modules.pullbackObjUnitIso f ≪≫ (cartierZeroSheafIso Z).symm)]
      exact proper_ample_cartierMixedEuler_diagonal_positive K n hdimZ hn HZ hHZ 0
    by_contra hnot
    have hk0 : k = 0 := by omega
    have h := hformula Y (𝟙 Y) (List.replicate n HY) (List.length_replicate ..) 0
    simp only [hk0, Nat.cast_zero, zero_mul, Category.comp_id] at h
    exact (ne_of_gt hpos) h
  exact ⟨k, hk, hformula⟩

end MixedFujita
