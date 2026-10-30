/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperAffineCohomologyComparison
public import MixedFujita.EffectiveCutCohomologyStabilization
public import MixedFujita.ProjectiveCutCartierSerreVanishing

/-! 実切断の正の射影冪表示から任意固定捻りの全大冪大域切断持ち上げ。 See reports/check-233-effective-cut-section-lifting.json for the verified scope. The actual cut may be nonreduced. One positive hyperplane power on the cut gives all sufficiently large fixed-twist section lifts; ambient H1 need not vanish. Global generation of the ambient source, numerical ampleness criteria, general nef-plus-ample, KV, BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- The ACTUAL cut H1 hypothesis, rather than pushforward cohomology,
suffices for eventual surjectivity of the original Cartier restriction maps. -/
theorem proper_effectiveCut_eventually_sections_surjective_of_cut_h1_vanish
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (E G : CartierDivisor X) (hG : G.IsEffective)
    (hvan : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Subsingleton
      (Scheme.Modules.Cohomology
        ((Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj
          (E + (m + 1) • G).sheaf) 1)) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Function.Surjective (Scheme.Modules.Hom.app (cartierSuccessiveCutShortComplex E G hG m).g ⊤) := by
  apply proper_effectiveCut_eventually_sections_surjective K E G hG
  obtain ⟨m₀, hm₀⟩ := hvan
  refine ⟨m₀, ?_⟩
  intro m hm
  let i := (effectiveCartierIdealSheaf G hG).subschemeι
  let Y := (effectiveCartierIdealSheaf G hG).subscheme
  let : Y.Over (Spec (CommRingCat.of K)) := ⟨i ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let M := (Scheme.Modules.pullback i).obj (E + (m + 1) • G).sheaf
  let : SheafOfModules.isInvertible Y M := cartierPullbackSheaf_isInvertible (E + (m + 1) • G) i
  let : M.IsCoherent := invertible_module_isCoherent _
  let : M.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Subsingleton (Scheme.Modules.Cohomology M 1) := hm₀ m hm
  exact (properAffineCohomologyAddEquiv K i M 1).symm.subsingleton


/-- An actual hyperplane presentation of ONE POSITIVE POWER on the
possibly nonreduced Cartier cut gives global lifting for every sufficiently
large E+mG with fixed E, without ambient H1 vanishing or supplied rank data. -/
theorem proper_effectiveCut_eventually_sections_surjective_of_projective_power
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (E G : CartierDivisor X) (hG : G.IsEffective) (d : ℕ) (hd : 0 < d) (r : ℕ)
    (e : (effectiveCartierIdealSheaf G hG).subscheme ⟶ polynomialProjectiveScheme (r + 1) K)
    [IsClosedImmersion e]
    (a : (Scheme.Modules.pullback (effectiveCartierIdealSheaf G hG).subschemeι).obj (d • G).sheaf ≅
      ((projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e).toModules 1) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      Function.Surjective (Scheme.Modules.Hom.app (cartierSuccessiveCutShortComplex E G hG m).g ⊤) := by
  apply proper_effectiveCut_eventually_sections_surjective_of_cut_h1_vanish K E G hG
  obtain ⟨m₀, hm₀⟩ := projective_cut_positive_power_eventually_cartier_cohomology_vanish K
    (effectiveCartierIdealSheaf G hG).subschemeι G E d hd r e a
  exact ⟨m₀, fun m hm => hm₀ (m + 1) (by omega) 0⟩

end MixedFujita
