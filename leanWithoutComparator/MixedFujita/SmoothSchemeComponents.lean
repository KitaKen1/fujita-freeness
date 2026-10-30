/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionZeroSmooth
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
public import TauCeti.RingTheory.RegularLocalRing.Basic
public import TauCeti.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent

/-!
Separate the irreducible components of a smooth scheme without asserting that the scheme is
irreducible or nonempty. Domain stalks give a unique component through each point. Noetherianity
then makes every component open as well as closed. A closed immersion carries the generic
points of these components to a finite, disjoint closed decomposition of its actual image.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- A domain localization prevents two distinct components of a prime spectrum from meeting. -/
theorem primeSpectrum_components_eq_of_domain_localization {R : Type u} [CommRing R]
    {Z W : Set (PrimeSpectrum R)} (hZ : Z ∈ irreducibleComponents (PrimeSpectrum R))
    (hW : W ∈ irreducibleComponents (PrimeSpectrum R)) (x : PrimeSpectrum R)
    [IsDomain (Localization.AtPrime x.asIdeal)] (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hWc := isClosed_of_mem_irreducibleComponents W hW
  have hP := PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr (hZc.closure_eq ▸ hZ)
  have hQ := PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr (hWc.closure_eq ▸ hW)
  have : (PrimeSpectrum.vanishingIdeal Z).IsPrime := hP.1.1
  have : (PrimeSpectrum.vanishingIdeal W).IsPrime := hQ.1.1
  have hPx : PrimeSpectrum.vanishingIdeal Z ≤ x.asIdeal :=
    fun a ha => (PrimeSpectrum.mem_vanishingIdeal Z a).mp ha x hxZ
  have hQx : PrimeSpectrum.vanishingIdeal W ≤ x.asIdeal :=
    fun a ha => (PrimeSpectrum.mem_vanishingIdeal W a).mp ha x hxW
  have hPQ : PrimeSpectrum.vanishingIdeal Z = PrimeSpectrum.vanishingIdeal W :=
    le_antisymm (TauCeti.le_of_mem_minimalPrimes_of_isDomain_localization hP hPx hQx)
      (TauCeti.le_of_mem_minimalPrimes_of_isDomain_localization hQ hQx hPx)
  rw [← hZc.closure_eq, ← hWc.closure_eq,
    ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hPQ]

/-- Domain stalks give a unique irreducible component through each point of a scheme. -/
theorem scheme_components_eq_of_domain_stalk {X : Scheme.{u}} {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (x : X) [IsDomain (X.presheaf.stalk x)] (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let y := hU.primeIdealOf ⟨x, hxU⟩
  have hy : hU.fromSpec y = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hZ' := preimage_mem_irreducibleComponents hZ hU.fromSpec.isOpenEmbedding
    ⟨x, hxZ, y, hy⟩
  have hW' := preimage_mem_irreducibleComponents hW hU.fromSpec.isOpenEmbedding
    ⟨x, hxW, y, hy⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk (⟨x, hxU⟩ : U)
  have : IsDomain (Localization.AtPrime y.asIdeal) :=
    (IsLocalization.algEquiv y.asIdeal.primeCompl (X.presheaf.stalk x)
      (Localization.AtPrime y.asIdeal)).toRingEquiv.symm.toMulEquiv.isDomain _
  have hyZ : y ∈ hU.fromSpec ⁻¹' Z := by simpa only [Set.mem_preimage, hy] using hxZ
  have hyW : y ∈ hU.fromSpec ⁻¹' W := by simpa only [Set.mem_preimage, hy] using hxW
  have hpre : hU.fromSpec ⁻¹' Z = hU.fromSpec ⁻¹' W :=
    primeSpectrum_components_eq_of_domain_localization hZ' hW' y
      hyZ hyW
  have hz := closure_image_preimage_of_isPreirreducible hU.fromSpec
    hU.fromSpec.isOpenEmbedding.isOpenMap Z ⟨y, hyZ⟩ hZ.1.2
    (isClosed_of_mem_irreducibleComponents Z hZ)
  have hw := closure_image_preimage_of_isPreirreducible hU.fromSpec
    hU.fromSpec.isOpenEmbedding.isOpenMap W ⟨y, hyW⟩ hW.1.2
    (isClosed_of_mem_irreducibleComponents W hW)
  exact hz.symm.trans ((congrArg (fun A => closure (hU.fromSpec '' A)) hpre).trans hw)

/-- A scheme with domain stalks has pairwise disjoint irreducible components. -/
theorem scheme_components_pairwise_disjoint {X : Scheme.{u}}
    [∀ x : X, IsDomain (X.presheaf.stalk x)] :
    (irreducibleComponents X).Pairwise Disjoint := by
  intro Z hZ W hW hne
  rw [Set.disjoint_left]
  intro x hxZ hxW
  exact hne (scheme_components_eq_of_domain_stalk hZ hW x hxZ hxW)

/-- Finitely many disjoint closed components are also open. -/
theorem scheme_component_isOpen {X : Scheme.{u}} [NoetherianSpace X]
    [∀ x : X, IsDomain (X.presheaf.stalk x)] (Z : Set X)
    (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  have heq : Z = (⋃₀ (irreducibleComponents X \ {Z}))ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_sdiff,
      Set.mem_singleton_iff, not_exists, not_and]
    constructor
    · intro hx W hW hxW
      exact hW.2 (scheme_components_eq_of_domain_stalk hW.1 hZ x hxW hx)
    · intro hx
      have hxC := mem_irreducibleComponent (x := x)
      have hC := irreducibleComponent_mem_irreducibleComponents x
      by_cases he : irreducibleComponent x = Z
      · exact he ▸ hxC
      · exact False.elim (hx _ ⟨hC, he⟩ hxC)
  rw [heq]
  rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
  exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
    fun W hW => isClosed_of_mem_irreducibleComponents W hW.1

/-- Smoothness over a field supplies domain stalks, via TauCeti's regularity theorems. -/
theorem smoothScheme_stalk_isDomain {K : Type u} [Field K] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  have : ∀ y : Spec (CommRingCat.of K),
      IsRegularLocalRing ((Spec (CommRingCat.of K)).presheaf.stalk y) :=
    fun y => inferInstance
  have := TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth g x
  infer_instance

/-- The closures of the mapped generic points are the actual images of the components. -/
theorem closedImmersion_genericPoint_closure {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsClosedImmersion f] (η : genericPoints Y) :
    closure ({f η} : Set X) = f '' closure ({η.1} : Set Y) := by
  rw [← Set.image_singleton, f.isClosedEmbedding.closure_image_eq]

/-- A closed immersion from a Noetherian scheme has a finite generic-point decomposition. -/
theorem closedImmersion_image_eq_iUnion_genericPoint_closures {X Y : Scheme.{u}}
    [NoetherianSpace Y] (f : Y ⟶ X) [IsClosedImmersion f] :
    Set.range f = ⋃ η : genericPoints Y, closure ({f η} : Set X) := by
  have hcover : (⋃ η : genericPoints Y, closure ({η.1} : Set Y)) = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    let C : irreducibleComponents Y := ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
    refine ⟨genericPoints.ofComponent C, ?_⟩
    rw [genericPoints.isGenericPoint_ofComponent]
    exact mem_irreducibleComponent
  rw [← Set.image_univ, ← hcover, Set.image_iUnion]
  congr 1
  funext η
  exact (closedImmersion_genericPoint_closure f η).symm

end MixedFujita
