/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACoherentSerreVanishing
public import MixedFujita.PulledLineBundlePowerIsomorphisms
public import MixedFujita.AmpleCartierHilbertPolynomial
public import MixedFujita.PulledModuleEulerPolynomial

/-! 元ampleの非被約閉引き戻しの全Serre消滅・実Hilbert多項式。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- An original ample Cartier divisor gives eventual positive cohomology
vanishing after restriction to any actual closed source, including nilpotents. -/
theorem proper_closed_pulled_cartier_serreVanishing
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsClosedImmersion p] (H E : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ q : ℕ, Subsingleton
      (Scheme.Modules.Cohomology ((Scheme.Modules.pullback p).obj (E + m • H).sheaf) (q + 1)) := by
  let L := cartierSGALineBundle H
  let M := (Scheme.Modules.pullback p).obj E.sheaf
  let : IsLocallyNoetherian Y := by
    let := properOverField_scheme_isNoetherian (K := K) (X := X)
    exact LocallyOfFiniteType.isLocallyNoetherian p
  let : SheafOfModules.isInvertible Y M := cartierPullbackSheaf_isInvertible E p
  let : M.IsCoherent := invertible_module_isCoherent _
  let : ((Scheme.Modules.pushforward p).obj M).IsCoherent :=
    CohomologyAux.isCoherent_pushforward_of_isClosedImmersion p M
  have hv := (sgaEventuallyCohomologyVanish_closed_pushforward_iff L p M).mp
    (sga_isAmple_coherent_serreVanishing K L ((cartierIsAmpleProj_iff_sga K H).mp hH) _)
  obtain ⟨m₀, hm₀⟩ := hv
  refine ⟨m₀, fun m hm q => ?_⟩
  let := hm₀ m hm q
  exact (actualCohomologyLinearEquivOfIso
    (cartierPulledSGAAffinePowerIso p H E (L.pullback p)
      (cartierPulledSheafSGAPowerOneIso H p).symm m) (q + 1)).subsingleton


/-- The actual pulled Euler polynomial is eventually the actual section
count on an arbitrary closed source; reducedness and integrality are unnecessary. -/
theorem proper_closed_pulled_cartierEulerPolynomial_eventually_eq_sections
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    [Y.Over (Spec (CommRingCat.of K))]
    (p : Y ⟶ X) [IsClosedImmersion p] [p.IsOver (Spec (CommRingCat.of K))]
    (n : ℕ) (hdim : topologicalKrullDim Y ≤ n) (H E : CartierDivisor X)
    (hH : CartierIsAmpleProj K H) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      (cartierPulledModuleEulerPolynomial K p (SheafOfModules.unit Y.ringCatSheaf) n H E).eval (m : ℚ) =
        (Module.finrank K Γ((Scheme.Modules.pullback p).obj (E + m • H).sheaf, ⊤) : ℚ) := by
  let : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    rw [← (HomIsOver.comp_over (f := p))]
    infer_instance
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let : O.IsCoherent := invertible_module_isCoherent _
  obtain ⟨m₀, hm₀⟩ := proper_closed_pulled_cartier_serreVanishing K p H E hH
  refine ⟨m₀, fun m hm => ?_⟩
  have h := proper_cartierPulledModuleEulerPolynomial_eval_int K p O n hdim H E (m : ℤ)
  simp only [natCast_zsmul, Int.cast_natCast] at h
  have he := moduleEulerChar_congr K
    (rightUnitor ((Scheme.Modules.pullback p).obj (E + m • H).sheaf))
  change Scheme.Modules.eulerChar (Y ↘ Spec (CommRingCat.of K))
      ((cartierPullbackTwistFunctor (E + m • H) p).obj O) = _ at he
  rw [he] at h
  rw [moduleEulerChar_eq_finrank_sections_of_positive_cohomology_zero K _ (hm₀ m hm)] at h
  simpa only [Int.cast_natCast] using h

end MixedFujita
