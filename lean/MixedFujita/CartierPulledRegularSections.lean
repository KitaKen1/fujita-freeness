/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ModuleFixedSectionFrameUnits
public import MixedFujita.SGAFiniteAffineFrames
public import MixedFujita.AffineAssociatedPrimeRegularity
public import MixedFujita.CartierSectionFiniteAvoidance
public import MixedFujita.CartierGlobalGenerationFiniteFamily

/-! 元Cartier有限点回避による任意非被約引き戻し源の実正則切断。 See reports/check-239-regular-pulled-section-cut-count-bounds.json for the verified scope. Actual regular pulled sections, all negative-twist injections and finite effective-cut section-loss bounds are proved on possibly nonreduced sources. Asymptotic numerical Morse nonvanishing, universal nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- A generated ambient Cartier line supplies a pulled natural section
nonvanishing at any finite set of points on an arbitrary source. The
source need not be integral or reduced, nor a closed subscheme. -/
theorem cartier_sga_pullback_exists_finite_nonvanishing_section
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X)
    (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    (Z : Set Y) (hZ : Z.Finite) :
    ∃ s : ((cartierSGALineBundle H).pullback p).sections 1,
      ∀ y ∈ Z, y ∈ ((cartierSGALineBundle H).pullback p).nonvanishingLocus s := by
  obtain ⟨r, t, ht⟩ := cartierIsGloballyGenerated_exists_fin_basePointFree H hH
  obtain ⟨a, ha, ⟨v, hv⟩, hgood⟩ :=
    cartierSections_general_finite_nonvanishing (K := K) H t ht (p '' Z) (hZ.image p)
  let τ := cartierSGASection H (∑ j, v j • t j)
  refine ⟨τ.pullback (cartierSGALineBundle H) p, fun y hy => ?_⟩
  rw [Scheme.LineBundle.nonvanishingLocus_pullback]
  change p y ∈ (cartierSGALineBundle H).nonvanishingLocus τ
  rw [cartierSGASection_nonvanishingLocus]
  exact not_not.mp (hgood v hv (p y) ⟨y, hy, rfl⟩)


/-- A generated ambient Cartier line has a pulled section whose actual
coefficient is a nonzerodivisor on EVERY member of a supplied finite
affine frame cover. All associated and embedded prime points are internal. -/
theorem cartier_sga_pullback_exists_regular_section_on_finite_affine_cover
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsLocallyNoetherian Y]
    (p : Y ⟶ X) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H)
    {ι : Type u} [Finite ι] (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (e : ∀ i, (((cartierSGALineBundle H).pullback p).toModules 1).over (U i) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over (U i))) :
    ∃ s : ((cartierSGALineBundle H).pullback p).sections 1, ∀ i,
      moduleOverFrameCoefficient (((cartierSGALineBundle H).pullback p).toModules 1)
        (U i) (e i) (U i) le_rfl
          ((((cartierSGALineBundle H).pullback p).toModules 1).presheaf.map
            (homOfLE le_top : U i ⟶ ⊤).op
              (sgaNaturalSectionToModule ((cartierSGALineBundle H).pullback p) 1 s)) ∈
                nonZeroDivisors Γ(Y, U i) := by
  classical
  let L := (cartierSGALineBundle H).pullback p
  let : ∀ i, IsNoetherianRing Γ(Y, U i) := fun i => IsLocallyNoetherian.component_noetherian ⟨U i, hU i⟩
  let A (i : ι) := {P : Ideal Γ(Y, U i) // P ∈ associatedPrimes Γ(Y, U i) Γ(Y, U i)}
  let point (i : ι) (P : A i) : Y := (hU i).fromSpec (⟨P.val, P.property.isPrime⟩ : PrimeSpectrum Γ(Y, U i))
  let Z : Set Y := ⋃ i, Set.range (point i)
  have hZ : Z.Finite := by
    apply Set.finite_iUnion
    intro i
    let : Finite (A i) := (associatedPrimes.finite Γ(Y, U i) Γ(Y, U i)).to_subtype
    exact Set.finite_range (point i)
  obtain ⟨s, hs⟩ := cartier_sga_pullback_exists_finite_nonvanishing_section K p H hH Z hZ
  refine ⟨s, fun i => ?_⟩
  apply affine_function_regular_of_associated_point_unit (hU i)
  intro P hP
  let Q : A i := ⟨P, hP⟩
  let y := point i Q
  have hy : y ∈ U i := by
    have hmem : y ∈ (hU i).fromSpec.opensRange := ⟨_, rfl⟩
    rwa [(hU i).opensRange_fromSpec] at hmem
  have hyZ : y ∈ Z := Set.mem_iUnion.mpr ⟨i, ⟨Q, rfl⟩⟩
  have hu := sga_nonvanishing_section_unit_in_any_frame L 1 s y (hs y hyZ) (U i) hy (e i)
  exact (Y.mem_basicOpen _ y hy).mpr hu


/-- On an arbitrary noetherian source, a generated ambient Cartier line
has an internally constructed finite affine frame cover and a single pulled
section regular on every chart, including charts with nilpotents. -/
theorem cartier_sga_pullback_exists_regular_section_affine_frames
    (K : Type u) [Field K] [Infinite K] {X Y : Scheme.{u}} [IsIntegral X] [CompactSpace X]
    [X.Over (Spec (CommRingCat.of K))] [IsNoetherian Y]
    (p : Y ⟶ X) (H : CartierDivisor X) (hH : CartierIsGloballyGenerated H) :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → Y.Opens) (_ : ∀ i, IsAffineOpen (U i))
      (e : ∀ i, (((cartierSGALineBundle H).pullback p).toModules 1).over (U i) ≅
        SheafOfModules.unit (Y.ringCatSheaf.over (U i))), (⨆ i, U i) = ⊤ ∧
      ∃ s : ((cartierSGALineBundle H).pullback p).sections 1, ∀ i,
        moduleOverFrameCoefficient (((cartierSGALineBundle H).pullback p).toModules 1)
          (U i) (e i) (U i) le_rfl
            ((((cartierSGALineBundle H).pullback p).toModules 1).presheaf.map
              (homOfLE le_top : U i ⟶ ⊤).op
                (sgaNaturalSectionToModule ((cartierSGALineBundle H).pullback p) 1 s)) ∈
                  nonZeroDivisors Γ(Y, U i) := by
  obtain ⟨ι, hι, U, hU, e, hcover⟩ := sga_exists_finite_affine_frame_cover ((cartierSGALineBundle H).pullback p) 1
  let := hι
  exact ⟨ι, hι, U, hU, e, hcover,
    cartier_sga_pullback_exists_regular_section_on_finite_affine_cover K p H hH U hU e⟩

end MixedFujita
