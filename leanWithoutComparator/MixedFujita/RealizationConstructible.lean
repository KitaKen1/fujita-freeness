/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealizationThresholdReduction
public import MixedFujita.RealizationSpecialization
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-!
The closedness of the realization sets from their constructibility (§2.2–2.3; step 9).

The realization sets R_α = {y | α ∈ Q(y)} are stable under specialization
(`stableUnderSpecialization_realizationSet`). On a scheme, a locally constructible set that is
stable under specialization is closed
(`isClosed_of_stableUnderSpecialization_of_isLocallyConstructible`; on an affine open this is
Stacks 00I0 (1), `PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible`).
Hence the point closedness assumed for (6) follows from the local constructibility of the sets
R_α (`isClosed_realizationSet_of_isLocallyConstructible`), and F1 follows from KV (sum), Lemma 3
at closed points, this constructibility, the degenerate form of Lemma 3 and the local statement
(`mixedFujitaFreeness_of_kawamataViehwegSum_of_lemmaThree_of_constructible`).

On a locally noetherian scheme every closed set is locally constructible
(`isLocallyConstructible_of_isClosed`), so the constructibility is a weaker hypothesis than the
closedness it replaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- On a scheme, a locally constructible set that is stable under specialization is closed. -/
theorem isClosed_of_stableUnderSpecialization_of_isLocallyConstructible {X : Scheme.{u}}
    {s : Set X} (hs : StableUnderSpecialization s) (hs' : IsLocallyConstructible s) :
    IsClosed s := by
  refine closure_subset_iff_isClosed.mp fun x hx => ?_
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨p, rfl⟩ : x ∈ Set.range hU.fromSpec := by rwa [hU.range_fromSpec]
  have hemb : IsOpenEmbedding hU.fromSpec := hU.fromSpec.isOpenEmbedding
  have hc : IsConstructible (hU.fromSpec ⁻¹' s : Set (PrimeSpectrum Γ(X, U))) :=
    @IsLocallyConstructible.isConstructible (PrimeSpectrum Γ(X, U)) _ _ _ _ _
      (hs'.preimage_of_isOpenEmbedding hemb)
  have ht : IsClosed (hU.fromSpec ⁻¹' s : Set (PrimeSpectrum Γ(X, U))) :=
    PrimeSpectrum.isClosed_of_stableUnderSpecialization_of_isConstructible
      (hs.preimage hemb.continuous) hc
  have hp : p ∈ closure (hU.fromSpec ⁻¹' s) := by
    rw [← hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous]
    exact hx
  exact ht.closure_subset hp

/-- On a locally noetherian scheme every closed set is locally constructible. -/
theorem isLocallyConstructible_of_isClosed {X : Scheme.{u}} [IsLocallyNoetherian X] {s : Set X}
    (hs : IsClosed s) : IsLocallyConstructible s := by
  intro x
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  refine ⟨U, U.2.mem_nhds hxU, U.2, ?_⟩
  have hopen : IsOpen (Subtype.val ⁻¹' s : Set U)ᶜ :=
    (hs.preimage continuous_subtype_val).isOpen_compl
  exact (IsRetrocompact.isConstructible hopen
    (fun _ _ _ => NoetherianSpace.isCompact _)).of_compl

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- A realization set is closed as soon as it is locally constructible. -/
theorem isClosed_realizationSet_of_isLocallyConstructible (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (N : ℕ) (q : Fin N → ℝ)
    (h : IsLocallyConstructible {y : Y | q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y}) :
    IsClosed {y : Y | q ∈ sncWeightNormalizedProfiles cY fY d D₀ D N y} :=
  isClosed_of_stableUnderSpecialization_of_isLocallyConstructible
    (stableUnderSpecialization_realizationSet cY fY d D₀ D N q) h

/-- F1 from the Kawamata–Viehweg statement (sum), Lemma 3 at closed points, the local
constructibility of the realization sets in the point, the degenerate form of Lemma 3 and the
local statement with the fixed part of the base ideal. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_lemmaThree_of_constructible
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hlct : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (x : X), IsClosed ({x} : Set X) →
      IdealThresholdZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ))) x)
    (hptc : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsLocallyConstructible {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (hdeg : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [DecidableEq K],
      ThresholdDegenerationStatement K)
    (hmodel : ThresholdBaseModelStatement.{u}) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_lemmaThree_of_thresholdBaseModel hKV hlct
    (fun K _ _ _ _ X _ _ n _ c₀ A hA x hx => (hptc K X n c₀ A hA x hx).mono fun _ hj α =>
      isClosed_realizationSet_of_isLocallyConstructible c₀ 1 1 _ _ _ _ (hj α))
    hdeg hmodel

end MixedFujita
