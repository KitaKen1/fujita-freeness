/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.OnePointLinePowerGeneration
public import MixedFujita.CoherentSerreClosedPointLifting
public import MixedFujita.SGAPowerSectionGeneration
public import MixedFujita.ModulePushforwardGlobalSections
public import Mathlib.AlgebraicGeometry.ResidueField

/-! 任意Noetherian非被約源の連接Serre消滅から正の大域生成冪。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- Coherent Serre vanishing supplies an actual positive-power section
nonvanishing at each closed point of a noetherian scheme. -/
theorem sga_closed_point_positive_power_section_of_coherent_serre
    {X : Scheme.{u}} [IsNoetherian X] (L : X.LineBundle)
    (hL : ∀ (M : X.Modules) [M.IsCoherent], sgaEventuallyCohomologyVanish L M)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : L.sections n, x ∈ L.nonvanishingLocus s := by
  let P := Spec (X.residueField x)
  let i := X.fromSpecResidueField x
  let : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  obtain ⟨n₀, hn₀⟩ := sga_eventually_surjective_to_closed_pullback_of_coherent_serre L hL i
  let n := n₀ + 1
  obtain ⟨f, hf⟩ := hn₀ n (by omega)
  have hN : moduleIsGloballyGenerated ((Scheme.Modules.pullback i).obj (L.toModules (n : ℤ))) :=
    moduleIsGloballyGenerated_of_iso (sgaLineBundlePullbackPowerIso L i n).symm
      (sga_moduleIsGloballyGenerated_of_subsingleton (L.pullback i) n)
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ k, L.U k by rw [L.iSup_eq_top]; trivial)
  let M := L.toModules (n : ℤ)
  let e := sgaLineBundleOverFrameIso L n k
  let d : M.restrict (L.U k).ι ≅ SheafOfModules.unit (L.U k).toScheme.ringCatSheaf :=
    ((Scheme.Modules.overFunctorEquiv (L.U k)).app M).symm ≪≫
      (Scheme.Modules.overEquiv (L.U k)).functor.mapIso e ≪≫
        (L.U k).sheafOfModulesEquivOverUnit X.ringCatSheaf
  let y : P := IsLocalRing.closedPoint (X.residueField x)
  have hy : i y = x := Scheme.fromSpecResidueField_apply x y
  obtain ⟨t, ht⟩ := module_generating_section_at_image_of_surjective_pushforward i M f hf hN
    y (L.U k) (by rw [hy]; exact hk) d
  rw [moduleRestrictFrameOverIso_roundTrip] at ht
  obtain ⟨s, hs⟩ := (sgaNaturalSectionToModule_bijective L n).surjective t
  refine ⟨n, by omega, s, (L.mem_nonvanishingLocus s).mpr ⟨k, ?_⟩⟩
  rw [← hs] at ht
  have ht' : IsUnit (moduleOverFrameGlobalCoefficientGerm (L.toModules (n : ℤ))
      (L.U k) (sgaLineBundleOverFrameIso L n k) x hk (sgaNaturalSectionToModule L n s)) := by
    change IsUnit (moduleOverFrameGlobalCoefficientGerm M (L.U k) e (i y)
      (show i y ∈ L.U k from by rw [hy]; exact hk) (sgaNaturalSectionToModule L n s)) at ht
    have move : ∀ (z : X) (hz : z ∈ L.U k), z = x →
        IsUnit (moduleOverFrameGlobalCoefficientGerm M (L.U k) e z hz (sgaNaturalSectionToModule L n s)) →
        IsUnit (moduleOverFrameGlobalCoefficientGerm M (L.U k) e x hk (sgaNaturalSectionToModule L n s)) := by
      intro z hz he h
      subst z
      exact h
    exact move (i y) _ hy ht
  unfold moduleOverFrameGlobalCoefficientGerm at ht'
  rw [sgaNaturalSectionToModule_frame_coefficient] at ht'
  exact (X.mem_basicOpen (s.val k) x hk).mpr ht'


/-- On every noetherian scheme, coherent Serre vanishing constructs a
positive globally generated power of the actual line bundle. Neither a
projective embedding nor reducedness is needed. -/
theorem sga_semiample_of_coherent_serre
    {X : Scheme.{u}} [IsNoetherian X] (L : X.LineBundle)
    (hL : ∀ (M : X.Modules) [M.IsCoherent], sgaEventuallyCohomologyVanish L M) :
    ∃ q : ℕ, 0 < q ∧ moduleIsGloballyGenerated (L.toModules (q : ℤ)) := by
  apply sga_exists_positive_generated_power_of_power_section_cover L
  exact sga_positive_power_section_cover_of_closed_points L
    (sga_closed_point_positive_power_section_of_coherent_serre L hL)

end MixedFujita
