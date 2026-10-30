/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StratumCentralSlice
public import Mathlib.Topology.KrullDimension

/-!
The number of tangent coordinates is at most the dimension of the image of the centre
(section 5.1 of the manuscript: the tangent directions are directions of the image W).

* A chain of k + 1 points of a T0 space, each a proper generization of the previous one, gives a
  chain of k + 1 irreducible closed sets, so k is at most the Krull dimension; and k is at most
  the Krull dimension of the closure of the last point.
* Let z be a point of a chart with Taylor coordinates given by the chart, in the closure of the
  generic point η of a component of the stratum of the members of positive weight, and T a set of
  coordinates outside those of the members of positive weight which are pullbacks of functions on
  an open set U of the base containing π(z). Adding the coordinates of T one at a time to the
  crossing coordinates gives prime ideals of the local ring at z (the ideals of coordinates are
  prime), hence points of the chart from η down towards z; the image of each is a proper
  specialization of the previous one, because the function of the added coordinate vanishes at
  the new point and not at the previous one. Hence the number of elements of T is at most the
  Krull dimension of the closure of π(η).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

section Topology

variable {T : Type*} [TopologicalSpace T] [T0Space T]

/-- A chain of k + 1 points, each a proper generization of the previous one, bounds the Krull
dimension from below. -/
theorem le_topologicalKrullDim_of_generization_chain (k : ℕ) (p : Fin (k + 1) → T)
    (hsp : ∀ i : Fin k, p i.succ ⤳ p i.castSucc) (hne : ∀ i : Fin k, p i.succ ≠ p i.castSucc) :
    (k : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  have hF : StrictMono (fun i : Fin (k + 1) =>
      (⟨closure {p i}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        IrreducibleCloseds T)) := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp (hsp i)) fun heq => ?_
    have h1 : closure ({p i.castSucc} : Set T) = closure {p i.succ} :=
      congrArg IrreducibleCloseds.carrier heq
    have h2 : p i.castSucc ⤳ p i.succ := by
      rw [specializes_iff_mem_closure, h1]
      exact subset_closure rfl
    exact hne i ((hsp i).antisymm h2).eq
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk k _ hF)

/-- The same, in the closure of the last point of the chain. -/
theorem le_topologicalKrullDim_closure_of_generization_chain (k : ℕ) (w : Fin (k + 1) → T)
    (hsp : ∀ i : Fin k, w i.succ ⤳ w i.castSucc) (hne : ∀ i : Fin k, w i.succ ≠ w i.castSucc) :
    (k : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({w (Fin.last k)} : Set T)) := by
  have hmem : ∀ i : Fin (k + 1), w i ∈ closure ({w (Fin.last k)} : Set T) := by
    intro i
    refine specializes_iff_mem_closure.mp ?_
    induction i using Fin.reverseInduction with
    | last => exact specializes_rfl
    | cast i ih => exact ih.trans (hsp i)
  exact le_topologicalKrullDim_of_generization_chain k
    (fun i => (⟨w i, hmem i⟩ : closure ({w (Fin.last k)} : Set T)))
    (fun i => (subtype_specializes_iff _ _).mpr (hsp i))
    (fun i h => hne i (congrArg Subtype.val h))

end Topology

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}}
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))] (π : X ⟶ Y)

/-- The number of tangent coordinates is at most the dimension of the closure of π(η). -/
theorem tangent_card_le_topologicalKrullDim {r : ℕ} (ξ : Fin r → X) (c : EtaleChart K X n)
    (σc : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σc) (w : Fin r → ℝ) (η : X)
    (hη : η ∈ c.U) (hwη : ∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X))
    (hmax : ∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η)
    (z : X) (hz : z ∈ c.U) (hηz : η ⤳ z)
    (ez : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk z))
      (X.presheaf.stalk z) ≃ₐ[K] MvPowerSeries (Fin n) K)
    (hez : ∀ i, stalkTaylorExpansion z ez (etaleChartStalkCoords c z hz (MvPolynomial.X i)) =
      MvPowerSeries.X i)
    (Tan : Finset (Fin n)) (hTanS : ∀ b ∈ Tan, ¬ ∃ k, w k ≠ 0 ∧ σc k = some b)
    (U : Y.Opens) (hzU : π z ∈ U)
    (hTanU : ∀ b ∈ Tan, ∃ g : Γ(Y, U), etaleChartStalkCoords c z hz (MvPolynomial.X b) =
      π.stalkMap z (Y.presheaf.germ U (π z) hzU g)) :
    (Tan.card : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({π η} : Set Y)) := by
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin n), S = {a | ∃ k, w k ≠ 0 ∧ σc k = some a} := ⟨_, rfl⟩
  -- an enumeration of the tangent coordinates
  obtain ⟨b, hbinj, hbmem⟩ : ∃ b : Fin Tan.card → Fin n, Function.Injective b ∧ ∀ j, b j ∈ Tan :=
    ⟨fun j => (Tan.equivFin.symm j : Fin n),
      fun j j' h => Tan.equivFin.symm.injective (Subtype.ext h),
      fun j => (Tan.equivFin.symm j).2⟩
  -- the sets of coordinates: the crossing coordinates and the tangent coordinates from i on
  obtain ⟨Sset, hSset⟩ : ∃ Sset : Fin (Tan.card + 1) → Set (Fin n),
      ∀ i a, a ∈ Sset i ↔ a ∈ S ∨ ∃ j : Fin Tan.card, (i : ℕ) ≤ (j : ℕ) ∧ a = b j :=
    ⟨fun i => S ∪ {a | ∃ j : Fin Tan.card, (i : ℕ) ≤ (j : ℕ) ∧ a = b j}, fun _ _ => Iff.rfl⟩
  have hprime : ∀ i, (Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) ''
      Sset i)).IsPrime := fun i => stalk_span_coords_isPrime c z hz ez hez (Sset i)
  -- the primes of the chart
  obtain ⟨𝔮, h𝔮def⟩ : ∃ 𝔮 : Fin (Tan.card + 1) → Ideal Γ(X, c.U), ∀ i, 𝔮 i =
      (Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) '' Sset i)).comap
        (X.presheaf.germ c.U z hz).hom := ⟨_, fun _ => rfl⟩
  have h𝔮mem : ∀ i (f : Γ(X, c.U)), f ∈ 𝔮 i ↔ X.presheaf.germ c.U z hz f ∈
      Ideal.span ((fun a => etaleChartStalkCoords c z hz (MvPolynomial.X a)) '' Sset i) := by
    intro i f
    rw [h𝔮def]
    rfl
  have h𝔮prime : ∀ i, (𝔮 i).IsPrime := by
    intro i
    have := hprime i
    rw [h𝔮def]
    exact Ideal.comap_isPrime _ _
  have hin : ∀ i a, a ∈ Sset i → c.coords (MvPolynomial.X a) ∈ 𝔮 i := by
    intro i a ha
    rw [h𝔮mem]
    exact Ideal.subset_span ⟨a, ha, rfl⟩
  have hnot : ∀ i a, a ∉ Sset i → c.coords (MvPolynomial.X a) ∉ 𝔮 i := by
    intro i a ha hmem
    have h1 := rescale_stalkTaylor_eq_zero_of_mem_span c z hz ez hez (Sset i) _
      ((h𝔮mem i _).mp hmem)
    have h2 : stalkTaylorExpansion z ez
        (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a))) = MvPowerSeries.X a := hez a
    rw [h2] at h1
    have h3 := (rescale_stratumScale_eq_zero_iff _ _).mp h1 (Finsupp.single a 1) (fun i' hi' => by
      rw [Finsupp.single_apply, ite_eq_right]
      rintro rfl
      exact ha hi')
    rw [MvPowerSeries.coeff_X, ite_eq_left rfl] at h3
    exact one_ne_zero h3
  -- the points of the chart
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Fin (Tan.card + 1) → X, ∀ i, ζ i = c.isAffine.fromSpec
      (⟨𝔮 i, h𝔮prime i⟩ : PrimeSpectrum Γ(X, c.U)) := ⟨_, fun _ => rfl⟩
  have hζU : ∀ i, ζ i ∈ c.U := by
    intro i
    rw [← SetLike.mem_coe, ← c.isAffine.range_fromSpec, hζ]
    exact ⟨_, rfl⟩
  have hζprime : ∀ i, c.isAffine.primeIdealOf ⟨ζ i, hζU i⟩ =
      (⟨𝔮 i, h𝔮prime i⟩ : PrimeSpectrum Γ(X, c.U)) := by
    intro i
    apply c.isAffine.fromSpec.isOpenEmbedding.injective
    rw [c.isAffine.fromSpec_primeIdealOf]
    exact hζ i
  have hunit : ∀ i (f : Γ(X, c.U)), f ∈ 𝔮 i ↔ ¬ IsUnit (X.presheaf.germ c.U (ζ i) (hζU i) f) := by
    intro i f
    rw [← etaleChart_mem_primeIdealOf_iff c (ζ i) (hζU i) f, hζprime i]
  have hζz : ∀ i, ζ i ⤳ z := by
    intro i
    have hle : 𝔮 i ≤ (c.isAffine.primeIdealOf ⟨z, hz⟩).asIdeal := by
      intro f hf
      rw [etaleChart_mem_primeIdealOf_iff c z hz]
      have h1 := IsLocalRing.le_maximalIdeal (hprime i).ne_top ((h𝔮mem i f).mp hf)
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h1
    have h1 : (⟨𝔮 i, h𝔮prime i⟩ : PrimeSpectrum Γ(X, c.U)) ⤳ c.isAffine.primeIdealOf ⟨z, hz⟩ :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map c.isAffine.fromSpec.continuous
    rw [c.isAffine.fromSpec_primeIdealOf] at h2
    rw [hζ i]
    exact h2
  have hζstep : ∀ i : Fin Tan.card, ζ i.succ ⤳ ζ i.castSucc := by
    intro i
    have hsub : Sset i.succ ⊆ Sset i.castSucc := by
      intro a ha
      rw [hSset] at ha ⊢
      rcases ha with ha | ⟨j, hj, rfl⟩
      · exact Or.inl ha
      · refine Or.inr ⟨j, ?_, rfl⟩
        rw [Fin.val_succ] at hj
        rw [Fin.val_castSucc]
        omega
    have hle : 𝔮 i.succ ≤ 𝔮 i.castSucc := by
      intro f hf
      rw [h𝔮mem] at hf ⊢
      exact Ideal.span_mono (Set.image_mono hsub) hf
    have h1 : (⟨𝔮 i.succ, h𝔮prime i.succ⟩ : PrimeSpectrum Γ(X, c.U)) ⤳
        (⟨𝔮 i.castSucc, h𝔮prime i.castSucc⟩ : PrimeSpectrum Γ(X, c.U)) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map c.isAffine.fromSpec.continuous
    rw [hζ i.succ, hζ i.castSucc]
    exact h2
  -- the last point is η
  have hSlast : ∀ a, a ∈ Sset (Fin.last Tan.card) ↔ a ∈ S := by
    intro a
    rw [hSset]
    constructor
    · rintro (ha | ⟨j, hj, -⟩)
      · exact ha
      · rw [Fin.val_last] at hj
        exact absurd j.2 (by omega)
    · exact Or.inl
  have hSeq : Sset (Fin.last Tan.card) = S := Set.ext hSlast
  have hSη : ∀ a ∈ S, ¬ IsUnit (X.presheaf.germ c.U η hη (c.coords (MvPolynomial.X a))) := by
    intro a ha
    rw [hS] at ha
    obtain ⟨k, hk, hka⟩ := ha
    exact (isSNCChart_mem_closure_iff hc η hη hka).mp (hwη k hk)
  have hlast : ζ (Fin.last Tan.card) = η := by
    have hp : c.isAffine.primeIdealOf ⟨η, hη⟩ =
        (⟨𝔮 (Fin.last Tan.card), h𝔮prime _⟩ : PrimeSpectrum Γ(X, c.U)) := by
      refine PrimeSpectrum.ext (Ideal.ext fun f => ?_)
      rw [etaleChart_mem_primeIdealOf_iff c η hη, h𝔮mem, hSeq]
      constructor
      · intro hnu
        have ht : X.presheaf.stalkSpecializes hηz (X.presheaf.germ c.U z hz f) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
          rw [TopCat.Presheaf.germ_stalkSpecializes_apply, IsLocalRing.mem_maximalIdeal,
            mem_nonunits_iff]
          exact hnu
        have h1 := stalk_mem_span_coords_of_stalkSpecializes_mem ξ c σc hc w η hη hwη hmax z hz
          hηz ez hez _ ht
        rw [hS]
        exact h1
      · intro hmem
        have h1 := stalkSpecializes_mem_maximalIdeal_of_mem_span_coords c S η hη z hz hηz hSη _
          hmem
        rwa [TopCat.Presheaf.germ_stalkSpecializes_apply, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff] at h1
    rw [hζ, ← hp, c.isAffine.fromSpec_primeIdealOf]
  -- the images form a chain of proper generizations
  have hne : ∀ i : Fin Tan.card, π (ζ i.succ) ≠ π (ζ i.castSucc) := by
    intro i heq
    obtain ⟨g, hg⟩ := hTanU (b i) (hbmem i)
    -- the germ of the coordinate at a generization of z is the pullback of the germ of g
    have hgerm : ∀ (p : X) (hpU : p ∈ c.U) (hpz : p ⤳ z) (hpY : π p ∈ U),
        X.presheaf.germ c.U p hpU (c.coords (MvPolynomial.X (b i))) =
          π.stalkMap p (Y.presheaf.germ U (π p) hpY g) := by
      intro p hpU hpz hpY
      have e1 : X.presheaf.stalkSpecializes hpz (X.presheaf.germ c.U z hz
          (c.coords (MvPolynomial.X (b i)))) =
            X.presheaf.germ c.U p hpU (c.coords (MvPolynomial.X (b i))) :=
        TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf _ _ _
      have e2 : X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X (b i))) =
          π.stalkMap z (Y.presheaf.germ U (π z) hzU g) := hg
      rw [e2, ← Scheme.Hom.stalkSpecializes_stalkMap_apply π p z hpz,
        TopCat.Presheaf.germ_stalkSpecializes_apply] at e1
      exact e1.symm
    have hYmem : ∀ j, π (ζ j) ∈ U := fun j =>
      (π.base.hom.map_specializes (hζz j)).mem_open U.isOpen hzU
    -- the coordinate b i belongs to the set of castSucc i and not to the set of succ i
    have hbin : b i ∈ Sset i.castSucc := by
      rw [hSset]
      exact Or.inr ⟨i, by rw [Fin.val_castSucc], rfl⟩
    have hbout : b i ∉ Sset i.succ := by
      rw [hSset]
      rintro (hbS | ⟨j, hj, hbj⟩)
      · rw [hS] at hbS
        exact hTanS (b i) (hbmem i) hbS
      · have hij : i = j := hbinj hbj
        rw [Fin.val_succ, ← hij] at hj
        omega
    -- g is a unit at the image of the more general point and not at the image of the other
    have hu1 : IsUnit (Y.presheaf.germ U (π (ζ i.succ)) (hYmem i.succ) g) := by
      have h1 : IsUnit (X.presheaf.germ c.U (ζ i.succ) (hζU i.succ)
          (c.coords (MvPolynomial.X (b i)))) :=
        not_not.mp ((hunit i.succ _).not.mp (hnot i.succ (b i) hbout))
      rw [hgerm (ζ i.succ) (hζU i.succ) (hζz i.succ) (hYmem i.succ)] at h1
      exact (isUnit_map_iff (π.stalkMap (ζ i.succ)).hom _).mp h1
    have hu2 : ¬ IsUnit (Y.presheaf.germ U (π (ζ i.castSucc)) (hYmem i.castSucc) g) := by
      intro hu
      have h1 : ¬ IsUnit (X.presheaf.germ c.U (ζ i.castSucc) (hζU i.castSucc)
          (c.coords (MvPolynomial.X (b i)))) :=
        (hunit i.castSucc _).mp (hin i.castSucc (b i) hbin)
      rw [hgerm (ζ i.castSucc) (hζU i.castSucc) (hζz i.castSucc) (hYmem i.castSucc)] at h1
      exact h1 (hu.map (π.stalkMap (ζ i.castSucc)).hom)
    have hb1 : π (ζ i.succ) ∈ Y.basicOpen g := (Y.mem_basicOpen _ _ (hYmem i.succ)).mpr hu1
    have hb2 : π (ζ i.castSucc) ∉ Y.basicOpen g := fun h =>
      hu2 ((Y.mem_basicOpen _ _ (hYmem i.castSucc)).mp h)
    exact hb2 (heq ▸ hb1)
  have hchain := le_topologicalKrullDim_closure_of_generization_chain Tan.card
    (fun i => π (ζ i)) (fun i => π.base.hom.map_specializes (hζstep i)) hne
  rw [hlast] at hchain
  exact hchain

end MixedFujita
