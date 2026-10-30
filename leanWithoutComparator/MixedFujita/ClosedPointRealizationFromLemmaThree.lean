/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothLemmaThreeRealization
public import MixedFujita.ZeroNormalizedProfile
public import MixedFujita.ThresholdDegenerationFromLemmaThree
public import MixedFujita.ProjectiveCurveCohomology

/-!
The closedness of the realization sets in the point (the hypothesis hpt of F1, section 2.2 of
the manuscript), from Lemma 3 in the model form on the affine opens of a smooth variety
(`closedPointRealization_of_smoothAffineLemmaThree`). For a rational profile α with a positive
entry, Q-membership is the countable intersection of the realization by test primes of the
(1 − 1/(l + 2)) α⁺ (`isClosedOnClosedPoints_normalizedProfiles_of_realized`, with the closedness
in the tuple at closed points as the slice of Lemma 3), and these realization sets are closed on
closed points by the properness of the flag variety in polynomial form
(`isClosedOnClosedPoints_realized_of_smoothAffineLemmaThree`). A profile with no positive entry is
realized at every closed point (`zero_mem_sncWeightNormalizedProfiles`), and a variety of dimension
zero is a point. The variety is proper since it has an ample sum.

F1 follows from sum KV (or the usual KV and big plus nef), Lemma 3 at closed points, Lemma 3 in
the model form on affine opens of smooth varieties and Lemma 3 in the model form on affine space:
the closedness hypothesis of the realization sets in the point is no longer assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
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

section Dimension

/-- An irreducible quasi-sober T0 space of topological Krull dimension zero is a point. -/
theorem subsingleton_of_topologicalKrullDim_eq_zero {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] [QuasiSober T] [T0Space T] (h : topologicalKrullDim T = 0) :
    Subsingleton T := by
  have hgen : ∀ z : T, z = genericPoint T := by
    intro z
    by_contra hz
    have hne : closure ({z} : Set T) ≠ Set.univ := by
      intro hcl
      apply hz
      have h1 : IsGenericPoint z (Set.univ : Set T) := hcl
      exact h1.eq (genericPoint_spec T)
    have hlt : (⟨closure ({z} : Set T), isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds T) < ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩ :=
      lt_of_le_of_ne (fun _ _ => trivial) (fun heq => hne (congrArg IrreducibleCloseds.carrier heq))
    have hpos := Order.krullDim_pos_iff.mpr ⟨_, _, hlt⟩
    rw [topologicalKrullDim] at h
    rw [h] at hpos
    exact lt_irrefl _ hpos
  exact ⟨fun x y => (hgen x).trans (hgen y).symm⟩

/-- Every set of a point is closed on closed points. -/
theorem isClosedOnClosedPoints_of_subsingleton {T : Type*} [TopologicalSpace T] [Subsingleton T]
    (s : Set T) : IsClosedOnClosedPoints s := by
  refine ⟨s, ?_, fun _ _ => Iff.rfl⟩
  rcases s.eq_empty_or_nonempty with hs | ⟨x, hx⟩
  · rw [hs]
    exact isClosed_empty
  · have : s = Set.univ := Set.eq_univ_of_forall fun y => (Subsingleton.elim x y) ▸ hx
    rw [this]
    exact isClosed_univ

end Dimension

section Profiles

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} {Y : Scheme.{u}}
  [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of K))] [IsSeparated (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- The normalized realization sets of every rational profile are closed on closed points, from
Lemma 3 in the model form on affine opens. -/
theorem isClosedOnClosedPoints_normalizedProfiles_of_smoothAffineLemmaThree
    (hL3 : SmoothAffineLemmaThreeStatement K) (cY : EtaleChart K Y n) (D : CartierDivisor Y)
    {N : ℕ} (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (α : Fin N → ℚ) :
    IsClosedOnClosedPoints {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D N y} := by
  classical
  set αp : Fin N → ℚ := fun i => max (α i) 0 with hαp
  have hset : {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
      (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D N y} =
      {y : Y | (fun i => (αp i : ℝ)) ∈ sncWeightNormalizedProfiles cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D N y} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [mem_sncWeightNormalizedProfiles_iff_max_zero]
    have h : (fun i => max ((α i : ℝ)) 0) = fun i => ((αp i : ℚ) : ℝ) := by
      funext i
      simp [hαp]
    rw [h]
  rw [hset]
  by_cases hpos : ∃ i, 0 < α i
  · obtain ⟨i₀, hi₀⟩ := hpos
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) i₀.isLt
    exact isClosedOnClosedPoints_normalizedProfiles_of_realized cY (1 : Y.functionFieldˣ) 1 le_rfl
      _ (smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl) D
      (fun y hy => realizationSetsZariskiClosed_of_smoothAffineLemmaThree hL3 cY D y hy) b₀
      (fun β hβ => isClosedOnClosedPoints_realized_of_smoothAffineLemmaThree hL3 cY D hN b₀ β hβ)
      αp (fun i => le_max_right _ _) ⟨i₀, lt_max_of_lt_left hi₀⟩
  · push Not at hpos
    have hzero : αp = 0 := by
      funext i
      exact max_eq_right (hpos i)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hdim := etaleChart_topologicalKrullDim (K := K) cY
      have : Subsingleton Y := subsingleton_of_topologicalKrullDim_eq_zero (by simpa using hdim)
      exact isClosedOnClosedPoints_of_subsingleton _
    · refine ⟨Set.univ, isClosed_univ, fun y hy => ?_⟩
      simp only [Set.mem_univ, iff_true, Set.mem_ofPred_eq]
      have h0 : (fun i => ((αp i : ℚ) : ℝ)) = 0 := by
        funext i
        simp [hzero]
      rw [h0]
      exact zero_mem_sncWeightNormalizedProfiles hn cY D b₀ y hy

end Profiles

section ClosedPoints

/-- The closedness of the realization sets in the point, in the form of the hypothesis of F1,
from Lemma 3 in the model form on affine opens of smooth varieties. -/
theorem closedPointRealization_of_smoothAffineLemmaThree
    (hL3 : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothAffineLemmaThreeStatement K) :
    ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosedOnClosedPoints {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y} := by
  intro K _ _ _ _ X _ _ n _ c₀ A hA x _
  obtain ⟨m, hm, s, hs, Ns, e, hci, he, g, hg, hggen, c, hc, f, hmA⟩ := hA
  have : IsClosedImmersion (e ⟨0, hs⟩) := hci ⟨0, hs⟩
  have hprop : IsProper (X ↘ Spec (CommRingCat.of K)) :=
    polynomialProjective_closedImmersion_isProper_over_field (e ⟨0, hs⟩) (he ⟨0, hs⟩)
  refine Filter.Eventually.of_forall fun j α => ?_
  by_cases hfd : Module.Finite K Γ((j • A).sheaf, ⊤)
  · exact isClosedOnClosedPoints_normalizedProfiles_of_smoothAffineLemmaThree (hL3 K) c₀ (j • A)
      (Module.finBasis K Γ((j • A).sheaf, ⊤)) α
  · refine ⟨∅, isClosed_empty, fun y _ => ?_⟩
    simp only [Set.mem_empty_iff_false, iff_false, Set.mem_ofPred_eq]
    rintro ⟨B, -⟩
    exact hfd (Module.Finite.of_basis B)

end ClosedPoints

section Freeness

/-- F1 from sum KV, Lemma 3 at closed points, Lemma 3 in the model form on affine opens of smooth
varieties and on affine space; the closedness of the realization sets in the point is no longer
assumed. -/
theorem mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_smoothAffineLemmaThree
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hlct : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (x : X), IsClosed ({x} : Set X) →
      IdealThresholdZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ))) x)
    (hL3s : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothAffineLemmaThreeStatement K)
    (hL3a : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], AffineLemmaThreeStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_lemmaThree_of_closedPoints_and_affineLemmaThree hKV hlct
    (closedPointRealization_of_smoothAffineLemmaThree hL3s) hL3a

/-- F1 from the usual KV, big plus nef, Lemma 3 at closed points and Lemma 3 in the model form on
affine opens of smooth varieties and on affine space. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_smoothAffineLemmaThree
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hlct : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (x : X), IsClosed ({x} : Set X) →
      IdealThresholdZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ))) x)
    (hL3s : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], SmoothAffineLemmaThreeStatement K)
    (hL3a : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], AffineLemmaThreeStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_lemmaThree_of_closedPoints_and_affineLemmaThree hKV hba
    hlct (closedPointRealization_of_smoothAffineLemmaThree hL3s) hL3a

end Freeness

end MixedFujita
