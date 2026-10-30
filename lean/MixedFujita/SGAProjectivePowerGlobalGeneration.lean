/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGANaturalSectionModuleDictionary
public import SGA.Foundations.Projective.LineBundle
public import SGA.Foundations.Cohomology.ProjectiveSpaceTwist

/-! 実射影座標の冪による非被約源上の超平面全正冪の大域生成。 See reports/check-234-effective-cut-semiampleness.json for the verified scope. An explicit positive hyperplane power on the actual possibly nonreduced cut gives original global generation of all sufficiently large divisible multiples of the effective ambient divisor and hence original semiampleness. General numerical ampleness criteria, nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true


/-- Powers of an actual SGA degree-one section, using its actual local
coordinates rather than choosing Cartier representatives on the source. -/
noncomputable def sgaLineBundleSectionPower {X : Scheme.{u}} (L : X.LineBundle)
    (s : L.sections 1) (j : ℕ) : L.sections j := by
  refine ⟨fun i => s.val i ^ j, ?_⟩
  intro i k
  simpa only [map_pow, pow_one, mul_pow] using congrArg (fun a => a ^ j) (s.property i k)


/-- A positive power preserves the actual nonvanishing locus. -/
theorem sgaLineBundleSectionPower_nonvanishingLocus {X : Scheme.{u}} (L : X.LineBundle)
    (s : L.sections 1) (j : ℕ) (hj : 0 < j) :
    L.nonvanishingLocus (sgaLineBundleSectionPower L s j) = L.nonvanishingLocus s := by
  unfold Scheme.LineBundle.nonvanishingLocus
  apply iSup_congr
  intro i
  exact X.basicOpen_pow (s.val i) hj


/-- Every positive hyperplane power pulled along any actual projective
map is globally generated on the actual possibly nonreduced source. -/
theorem moduleIsGloballyGenerated_projective_hyperplane_power
    (K : Type u) [Field K] {Y : Scheme.{u}} (r : ℕ)
    (e : Y ⟶ polynomialProjectiveScheme (r + 1) K) (j : ℕ) (hj : 0 < j) :
    moduleIsGloballyGenerated
      (((projectiveSpace.twistingBundle (Fin (r + 1)) K).pullback e).toModules (j : ℤ)) := by
  let L := projectiveSpace.twistingBundle (Fin (r + 1)) K
  apply moduleIsGloballyGenerated_sga_of_nonvanishing_cover
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show e y ∈ ⨆ i : Fin (r + 1), projectiveSpace.stdCover (Fin (r + 1)) K i by
    rw [projectiveSpace.iSup_stdCover]
    exact Opens.mem_top _)
  let sb : L.sections 1 := Proj.twistingSheaf.homogeneousSection
    (fun k : ULift.{u} (Fin (r + 1)) => MvPolynomial.X k.down)
    (fun k => projectiveSpace.X_mem k.down) projectiveSpace.iSup_stdCover_ulift (projectiveSpace.X_mem i)
  let s := sb.pullback L e
  refine ⟨sgaLineBundleSectionPower (L.pullback e) s j, ?_⟩
  rw [sgaLineBundleSectionPower_nonvanishingLocus _ _ j hj,
    Scheme.LineBundle.nonvanishingLocus_pullback]
  change e y ∈ L.nonvanishingLocus sb
  rw [Proj.twistingSheaf.nonvanishingLocus_homogeneousSection]
  exact hi

end MixedFujita
