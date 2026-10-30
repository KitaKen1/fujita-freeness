/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SingularProjectiveIntegralCurveExistence
public import MixedFujita.AmpleCartierPullbackRepresentatives
public import MixedFujita.ZeroDimensionalIntegralScheme
public import SGA.Foundations.Cohomology.Devissage

/-! 非被約射影閉源の整閉曲線不存在から有限性・全整成分の内部処理。 See reports/check-236-semiample-positive-curve-ampleness.json for the verified scope. Actual finite smooth-curve degree positivity makes the actual section morphism finite; original semiampleness then implies original Cartier ampleness over an algebraically closed characteristic-zero field. No source normality or smoothness, reduced fibers, supplied fiber curves or finiteness witnesses are required. Universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- A possibly NONREDUCED actual closed source in a proper projective
scheme is finite if it contains no actual integral closed curve. All
integral component structures and their ordinary dimensions are internal. -/
theorem projective_closed_source_finite_of_no_integral_curves
    (K : Type u) [Field K] [IsAlgClosed K] {X F : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hProj : ∃ A : CartierDivisor X, CartierIsAmpleProj K A)
    (j : F ⟶ X) [IsClosedImmersion j]
    (h : ∀ (C : Scheme.{u}) [IsIntegral C] (i : C ⟶ F) [IsClosedImmersion i],
      topologicalKrullDim C = 1 → False) : Finite F := by
  classical
  let : F.Over (Spec (CommRingCat.of K)) := ⟨j ≫ (X ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (F ↘ Spec (CommRingCat.of K)) := by
    change IsProper (j ≫ (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  let := properOverField_scheme_isNoetherian (K := K) (X := F)
  have hcfin (Z : Set F) (hZ : Z ∈ irreducibleComponents F) : Z.Finite := by
    obtain ⟨T, i, hi, hT, hrange⟩ := CohomologyAux.exists_integral_closedImmersion Z
      (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
    let := hi
    let := hT
    let q := i ≫ j
    let : T.Over (Spec (CommRingCat.of K)) := ⟨q ≫ (X ↘ Spec (CommRingCat.of K))⟩
    let : q.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
    let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
      change IsProper (q ≫ (X ↘ Spec (CommRingCat.of K)))
      infer_instance
    obtain ⟨A, hA⟩ := integral_closed_source_exists_original_ample_cartier K q hProj
    obtain ⟨n, hn⟩ : ∃ n : ℕ, topologicalKrullDim T = n :=
      ⟨_, TauCeti.AlgebraicGeometry.topologicalKrullDim_eq_toNat_trdeg_functionField K⟩
    by_cases hn0 : n = 0
    · have hdim0 : topologicalKrullDim T = 0 := by simpa only [hn0, Nat.cast_zero] using hn
      let := zeroDimensional_integral_subsingleton hdim0
      have hfin : (Set.range i).Finite := Set.finite_range i
      rwa [hrange] at hfin
    · obtain ⟨m, hm, M, eT, heTc, heT, g, hg, hgg, f, hEq⟩ := hA
      let := heTc
      obtain ⟨C, iC, hC, hiC, hdimC⟩ := polynomialProjective_exists_integral_closed_curve K eT heT n hn (by omega)
      let := hC
      let := hiC
      exact False.elim (h C (iC ≫ i) hdimC)
  have hfin := NoetherianSpace.finite_irreducibleComponents.biUnion hcfin
  have hcover : (⋃ Z ∈ irreducibleComponents F, Z) = (Set.univ : Set F) := by
    ext x
    constructor
    · intro _; exact Set.mem_univ _
    · intro _
      exact Set.mem_iUnion.mpr ⟨irreducibleComponent x,
        Set.mem_iUnion.mpr ⟨irreducibleComponent_mem_irreducibleComponents x, mem_irreducibleComponent⟩⟩
  exact Finite.of_finite_univ (hcover ▸ hfin)

end MixedFujita
