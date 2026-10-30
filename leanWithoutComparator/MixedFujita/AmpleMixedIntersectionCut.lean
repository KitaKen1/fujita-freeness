/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierMixedIntersectionCut
public import MixedFujita.TopMixedEulerHomogeneity
public import MixedFujita.AmpleEffectiveComparison

/-! 元ample因子の正整数倍と実低次元有効Cartier切断への内部還元。 See reports/check-224-effective-cut-generic-intersection.json for the verified scope. Mixed positivity on the actual cut and the manuscript numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A positive multiple represented by an effective Cartier divisor gives
an exact scaled cut formula for the ORIGINAL first intersection factor. -/
theorem proper_cartierMixedIntersection_scaled_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H G : CartierDivisor X) (hG : G.IsEffective)
    (q : ℕ) (a : (q • H).sheaf ≅ G.sheaf)
    (hdim : topologicalKrullDim X = D.length + 1) :
    let I := effectiveCartierIdealSheaf G hG
    letI : I.subscheme.Over (Spec (CommRingCat.of K)) :=
      ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
    (q : ℤ) * cartierMixedIntersection K (H :: D) (by simpa using hdim) =
      cartierPulledModuleMixedEulerDifference K I.subschemeι
        (SheafOfModules.unit I.subscheme.ringCatSheaf) D 0 := by
  have hrefl : ∀ L : List (CartierDivisor X),
      List.Forall₂ (fun L N : CartierDivisor X => Nonempty (L.sheaf ≅ N.sheaf)) L L := by
    intro L
    induction L with
    | nil => exact .nil
    | cons J L ih => exact .cons ⟨Iso.refl _⟩ ih
  have heq := cartierMixedEulerDifference_direction_isos K (.cons ⟨a⟩ (hrefl D)) 0
  have hscale := proper_cartierMixedEulerDifference_top_nsmul_factor K (D.length + 1)
    hdim.le [] D (by simp) H 0 q
  change cartierMixedEulerDifference K ((q • H) :: D) 0 =
    (q : ℤ) * cartierMixedEulerDifference K (H :: D) 0 at hscale
  exact hscale.symm.trans (heq.trans
    (proper_cartierMixedIntersection_eq_canonical_effective_cut K D G hG hdim))


/-- Any original ample factor reduces to an ACTUAL lower-dimensional
effective Cartier cut after a positive integer scaling. The scale, effective
representative, principal comparison, canonical K-structure and dimension
drop are supplied internally, over any field. Mixed positivity is the
remaining geometric obligation on this actual cut. -/
theorem proper_cartierMixedIntersection_ample_exists_effective_cut
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : List (CartierDivisor X)) (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (hdim : topologicalKrullDim X = D.length + 1) :
    ∃ q : ℕ, 1 ≤ q ∧ ∃ (G : CartierDivisor X) (hG : G.IsEffective),
      topologicalKrullDim (effectiveCartierIdealSheaf G hG).subscheme ≤ D.length ∧
      let I := effectiveCartierIdealSheaf G hG
      letI : I.subscheme.Over (Spec (CommRingCat.of K)) :=
        ⟨I.subschemeι ≫ (X ↘ Spec (CommRingCat.of K))⟩
      (q : ℤ) * cartierMixedIntersection K (H :: D) (by simpa using hdim) =
        cartierPulledModuleMixedEulerDifference K I.subschemeι
          (SheafOfModules.unit I.subscheme.ringCatSheaf) D 0 := by
  obtain ⟨q₀, hq₀⟩ := cartierIsAmpleProj_eventually_effective_comparison hH 0
  let q := max q₀ 1
  obtain ⟨f, hf⟩ := hq₀ q (le_max_left _ _)
  let G := q • H + principalCartierDivisor X f
  have hG : G.IsEffective := by simpa only [sub_zero] using hf
  refine ⟨q, le_max_right _ _, G, hG,
    effectiveCartierCut_topologicalKrullDim_le G hG D.length hdim.le, ?_⟩
  exact proper_cartierMixedIntersection_scaled_effective_cut K D H G hG q
    (cartierSheafPrincipalShiftIso (q • H) f).symm hdim

end MixedFujita
