/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StratumTaylorRestriction
public import MixedFujita.GeometricJacobianBound

/-!
The coordinates at a general closed point of the centre of a weight (section 5.1 of the
manuscript: crossing coordinates, tangent coordinates coming from the base, fibre coordinates).

Let π : X → Y be a morphism over an algebraically closed field of characteristic zero, X smooth
with a simple normal crossing family, w a weight on the family and η the generic point of a
component of the stratum of the members of positive weight. Let U be an affine open of Y
containing π(η) and 𝒢 a set of functions on U generating the functions on U as an algebra.
Near every point of the closure of η in general position there is a closed point z of the closure
of η and a simple normal crossing chart at z and η, all of whose coordinates vanish at z, whose
selected coordinates are exactly the coordinates of the members of positive weight, with a set T of
further coordinates (the tangent coordinates) such that

* each coordinate of T is the pullback of g - g(π(z)) for a function g of 𝒢, and
* for every germ h at π(η) the derivatives of the pullback of h in the coordinates outside the
  family and outside T (the fibre coordinates) lie in the maximal ideal of η.

By the statements on the restriction to the stratum, the Taylor expansion at z of the pullback of
every germ at π(z), reduced modulo the crossing coordinates, is then a power series in the tangent
coordinates only.

* The coordinate derivations do not change when the coordinates are translated by constants; the
  centred chart; its stalk coordinates.
* The pullbacks of all the germs at π(η) lie in the subalgebra of the germs with derivatives in the
  maximal ideal as soon as the pullbacks of the functions of 𝒢 do.
* The chart at a general closed point, also in the general form where the closed point is taken
  in a given set whose closed points are dense in the closure of η (for the very general points
  of the specialization comparison (6)).
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

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Algebra

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S] {n : ℕ}

/-- The coordinate derivations do not change when the coordinates are translated by constants. -/
theorem etaleCoordinateDerivation_of_sub_algebraMap (y y' : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale) (κ : Fin n → K)
    (h : ∀ i, y' (MvPolynomial.X i) = y (MvPolynomial.X i) - algebraMap K S (κ i)) (j : Fin n) :
    etaleCoordinateDerivation y' hy' j = etaleCoordinateDerivation y hy j := by
  refine derivation_ext_etaleCoordinates y' hy' fun i => ?_
  rw [etaleCoordinateDerivation_coordinate, h i, map_sub, Derivation.map_algebraMap, sub_zero,
    etaleCoordinateDerivation_coordinate]

end Algebra

section Centred

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}

/-- Translating a simple normal crossing chart by constants that vanish on the coordinates of the
family keeps the simple normal crossing position. -/
theorem isSNCChart_etaleChartCentered {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σ) (α : Γ(X, c.U) →ₐ[K] K)
    (hα : ∀ k a, σ k = some a → α (c.coords (MvPolynomial.X a)) = 0) :
    IsSNCChart (etaleChartCentered c α) ξ σ := by
  refine ⟨hc.1, fun k => ?_⟩
  have h := hc.2 k
  cases hσ : σ k with
  | none =>
    rw [hσ] at h
    exact h
  | some a =>
    rw [hσ, Option.elim_some] at h
    change closure ({ξ k} : Set X) ∩ c.U = X.zeroLocus
      ({(centeredPolynomialChart c.coords α (MvPolynomial.X a))} : Set Γ(X, c.U)) ∩ c.U
    rw [centeredPolynomialChart_variable, hα k a hσ, map_zero, sub_zero]
    exact h

/-- The stalk coordinates of the translated chart. -/
theorem etaleChartStalkCoords_centered (c : EtaleChart K X n) (α : Γ(X, c.U) →ₐ[K] K) (p : X)
    (hp : p ∈ c.U) (i : Fin n) :
    etaleChartStalkCoords (etaleChartCentered c α) p hp (MvPolynomial.X i) =
      etaleChartStalkCoords c p hp (MvPolynomial.X i) -
        algebraMap K (X.presheaf.stalk p) (α (c.coords (MvPolynomial.X i))) := by
  change sectionStalkAlgHom (K := K) c.U p hp
    (centeredPolynomialChart c.coords α (MvPolynomial.X i)) = _
  rw [centeredPolynomialChart_variable, map_sub, AlgHom.commutes]
  rfl

end Centred

section Generators

variable {K : Type u} [Field K] {n : ℕ} {Y X : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  [X.Over (Spec (CommRingCat.of K))] (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]

/-- The pullbacks of all the germs at π(η) lie in the subalgebra of the germs at η whose
derivatives in the coordinates of F lie in the maximal ideal, as soon as the pullbacks of a set of
generators of the functions on an affine open containing π(η) do. -/
theorem stalkMap_mem_coordinateConstantSubalgebra_of_adjoin (η : X) (U : Y.Opens)
    (hU : IsAffineOpen U) (hηU : π η ∈ U) (𝒢 : Set Γ(Y, U)) (h𝒢 : Algebra.adjoin K 𝒢 = ⊤)
    (y : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk η) (hy : y.toRingHom.FormallyEtale)
    (F : Set (Fin n))
    (hG : ∀ g ∈ 𝒢, π.stalkMap η (Y.presheaf.germ U (π η) hηU g) ∈
      coordinateConstantSubalgebra y hy F)
    (h' : Y.presheaf.stalk (π η)) :
    π.stalkMap η h' ∈ coordinateConstantSubalgebra y hy F := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Γ(Y, U) →ₐ[K] X.presheaf.stalk η,
      ∀ a, ψ a = π.stalkMap η (Y.presheaf.germ U (π η) hηU a) :=
    ⟨(schemeStalkMapAlgHom (K := K) π η).comp (sectionStalkAlgHom (K := K) U (π η) hηU),
      fun _ => rfl⟩
  have hall : ∀ a : Γ(Y, U), π.stalkMap η (Y.presheaf.germ U (π η) hηU a) ∈
      coordinateConstantSubalgebra y hy F := by
    intro a
    have hle : Algebra.adjoin K 𝒢 ≤ (coordinateConstantSubalgebra y hy F).comap ψ :=
      Algebra.adjoin_le fun g hg => by
        change ψ g ∈ coordinateConstantSubalgebra y hy F
        rw [hψ g]
        exact hG g hg
    rw [h𝒢] at hle
    have h1 : ψ a ∈ coordinateConstantSubalgebra y hy F := hle Algebra.mem_top
    rw [hψ a] at h1
    exact h1
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨π η, hηU⟩ : U)
  have hloc := hU.isLocalization_stalk (⟨π η, hηU⟩ : U)
  obtain ⟨⟨a, u⟩, hau⟩ := IsLocalization.surj (hU.primeIdealOf ⟨π η, hηU⟩).asIdeal.primeCompl h'
  have hau' : h' * Y.presheaf.germ U (π η) hηU (u : Γ(Y, U)) = Y.presheaf.germ U (π η) hηU a :=
    hau
  have hu : IsUnit (Y.presheaf.germ U (π η) hηU (u : Γ(Y, U))) :=
    IsLocalization.map_units (Y.presheaf.stalk (π η)) u
  have hmul : π.stalkMap η h' * π.stalkMap η (Y.presheaf.germ U (π η) hηU (u : Γ(Y, U))) =
      π.stalkMap η (Y.presheaf.germ U (π η) hηU a) := by
    rw [← map_mul, hau']
  exact coordinateConstantSubalgebra_of_mul_eq y hy F (hall a) (hall u)
    (hu.map (π.stalkMap η).hom) hmul

end Generators

section Centre

variable {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ} {Y X : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))]
  (π : X ⟶ Y) [π.IsOver (Spec (CommRingCat.of K))]

/-- The coordinates at a closed point of the centre of a weight lying in a given set G whose closed
points are dense in the closure of η: as `exists_closedPoint_tangent_chart_of_weight`, with z in
G. There is a point η on all
the members of positive weight, specializing to the given point y and with no proper generization
on all of them, such that for every affine open U of the base containing π(η), every set 𝒢 of
generators of the functions on U and every open set V containing η there are a closed point z of
the closure of η in V over U and a simple normal crossing chart at z and η with: all coordinates
vanish at z; the selected coordinates are exactly those of the members of positive weight; the
coordinates of a set T outside the family are pullbacks of g - κ with g in 𝒢 and κ constant; for
every germ h at π(η) the derivatives of the pullback of h in the coordinates outside the family and
outside T lie in the maximal ideal of η. -/
theorem exists_closedPoint_tangent_chart_of_weight_dense {r : ℕ} (ξ : Fin r → X)
    (hsnc : IsSNCFamily K n ξ) (w : Fin r → ℝ) (y : X)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      (∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η) ∧
      ∀ (U : Y.Opens) (_ : IsAffineOpen U) (_ : π η ∈ U) (𝒢 : Set Γ(Y, U)),
        Algebra.adjoin K 𝒢 = ⊤ → ∀ V : Set X, IsOpen V → η ∈ V → ∀ G : Set X,
        (∀ O : Set X, IsOpen O → η ∈ O →
          ∃ z ∈ G, IsClosed ({z} : Set X) ∧ z ∈ closure ({η} : Set X) ∧ z ∈ O) →
        ∃ (z : X) (_ : IsClosed ({z} : Set X)) (_ : η ⤳ z) (_ : z ∈ V) (_ : z ∈ G)
          (hzU : π z ∈ U)
          (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hz : z ∈ c.U) (hη : η ∈ c.U)
          (T : Finset (Fin n)), IsSNCChart c ξ σc ∧
          (∀ a, ¬ IsUnit (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a)))) ∧
          (∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0) ∧
          (∀ b ∈ T, (∀ k, σc k ≠ some b) ∧ ∃ g ∈ 𝒢, ∃ κ : K,
            etaleChartStalkCoords c z hz (MvPolynomial.X b) =
              π.stalkMap z (Y.presheaf.germ U (π z) hzU (g - algebraMap K Γ(Y, U) κ))) ∧
          ∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ T →
            etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
              (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
                IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨η, hη, hηy, hmax, havoid⟩ := exists_stratum_generic_point_avoiding K n ξ hsnc w y hwy
  refine ⟨η, hη, hηy, hmax, fun U hU hηU 𝒢 h𝒢 V hV hηV G hG => ?_⟩
  -- a chart at η inside V and the preimage of U, away from the members of weight zero
  obtain ⟨c₀, σ₀, hη₀, hc₀⟩ := hsnc η
  obtain ⟨C, hCdef⟩ : ∃ C : Set X, C = (⋃ k ∈ (Finset.univ.filter fun k => w k = 0),
      closure ({ξ k} : Set X)) ∪ (V ∩ (π ⁻¹ᵁ U : Set X))ᶜ := ⟨_, rfl⟩
  have hCclosed : IsClosed C := by
    rw [hCdef]
    exact (isClosed_biUnion_finset fun k _ => isClosed_closure).union
      (hV.inter (π ⁻¹ᵁ U).isOpen).isClosed_compl
  have hηC : η ∉ C := by
    rw [hCdef]
    rintro (h | h)
    · simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨k, hk, hηk⟩ := h
      exact havoid k hk hηk
    · exact h ⟨hηV, hηU⟩
  obtain ⟨c₁, hη₁, hdisj, hc₁⟩ := exists_snc_chart_avoiding hc₀ hη₀ hCclosed hηC
  have hc₁C : ∀ p ∈ c₁.U, p ∉ C := by
    intro p hp hpC
    have h1 : p ∈ (c₁.U : Set X) ∩ C := ⟨hp, hpC⟩
    rw [hdisj] at h1
    exact h1
  have hc₁V : ∀ p ∈ c₁.U, p ∈ V ∧ π p ∈ U := by
    intro p hp
    by_contra hcon
    exact hc₁C p hp (by rw [hCdef]; exact Or.inr hcon)
  have hc₁0 : ∀ k, w k = 0 → closure ({ξ k} : Set X) ∩ c₁.U = ∅ := by
    intro k hk
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hpk hpU
    refine hc₁C p hpU ?_
    rw [hCdef]
    refine Or.inl ?_
    simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, hk, hpk⟩
  -- the selection: the members of positive weight
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : Fin r → Option (Fin n),
      ∀ k, σ₁ k = if w k = 0 then none else σ₀ k := ⟨_, fun _ => rfl⟩
  have hσ₁some : ∀ k a, σ₁ k = some a → w k ≠ 0 ∧ σ₀ k = some a := by
    intro k a hka
    by_cases hk : w k = 0
    · rw [hσ₁ k, ite_eq_left hk] at hka
      exact absurd hka (by simp)
    · rw [hσ₁ k, ite_eq_right hk] at hka
      exact ⟨hk, hka⟩
  have hc₁' : IsSNCChart c₁ ξ σ₁ := by
    refine ⟨fun i j a hi hj => hc₁.1 i j a (hσ₁some i a hi).2 (hσ₁some j a hj).2, fun k => ?_⟩
    by_cases hk : w k = 0
    · rw [hσ₁ k, ite_eq_left hk]
      exact hc₁0 k hk
    · rw [hσ₁ k, ite_eq_right hk]
      exact hc₁.2 k
  have hσ₁iff : ∀ k, (∃ a, σ₁ k = some a) ↔ w k ≠ 0 := by
    intro k
    constructor
    · rintro ⟨a, hka⟩
      exact (hσ₁some k a hka).1
    · intro hk
      obtain ⟨a, ha⟩ := isSNCChart_exists_some_of_mem_closure hc₁ η hη₁ (hη k hk)
      exact ⟨a, by rw [hσ₁ k, ite_eq_right hk]; exact ha⟩
  -- the tangent coordinates
  obtain ⟨H, hH⟩ : ∃ H : Set (X.presheaf.stalk η),
      H = {h | ∃ g ∈ 𝒢, h = π.stalkMap η (Y.presheaf.germ U (π η) hηU g)} := ⟨_, rfl⟩
  obtain ⟨c₂, hη₂, T, hle₂, hc₂, hT, -, hsat⟩ :=
    exists_tangent_saturated_chart ξ σ₁ η H c₁ hη₁ hc₁'
  have hsatall : ∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σ₁ k ≠ some b) → b ∉ T →
      etaleCoordinateDerivation (etaleChartStalkCoords c₂ η hη₂)
        (etaleChartStalkCoords_formallyEtale c₂ η hη₂) b (π.stalkMap η h') ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
    intro h' b hb hbT
    have hmem := stalkMap_mem_coordinateConstantSubalgebra_of_adjoin π η U hU hηU 𝒢 h𝒢
      (etaleChartStalkCoords c₂ η hη₂) (etaleChartStalkCoords_formallyEtale c₂ η hη₂)
      {b | (∀ k, σ₁ k ≠ some b) ∧ b ∉ T}
      (fun g hg b' hb' => hsat _ (by rw [hH]; exact ⟨g, hg, rfl⟩) b' hb'.1 hb'.2) h'
    exact hmem b ⟨hb, hbT⟩
  -- a closed point of the closure of η in the chart and in G
  obtain ⟨z, hzG, hzcl', hzη, hzU₂⟩ := hG (c₂.U : Set X) c₂.U.isOpen hη₂
  have hspz : η ⤳ z := specializes_iff_mem_closure.mpr hzη
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) z hzcl'
  obtain ⟨hzV, hzU⟩ := hc₁V z (hle₂ hzU₂)
  -- the coordinates of the family vanish at z
  have hα0 : ∀ k a, σ₁ k = some a →
      rationalAffineGermPoint z hzU₂ β (c₂.coords (MvPolynomial.X a)) = 0 := by
    intro k a hka
    have hzk : z ∈ closure ({ξ k} : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr (hη k ((hσ₁iff k).mp ⟨a, hka⟩)))
        isClosed_closure hzη
    have hnu := (isSNCChart_mem_closure_iff hc₂ z hzU₂ hka).mp hzk
    change β (X.presheaf.germ c₂.U z hzU₂ (c₂.coords (MvPolynomial.X a))) = 0
    exact not_not.mp ((rationalLocalPoint_isUnit_iff β _).not.mp hnu)
  have hpre : c₂.U ≤ π ⁻¹ᵁ U := fun p hp => (hc₁V p (hle₂ hp)).2
  refine ⟨z, hzcl', hspz, hzV, hzG, hzU, etaleChartCentered c₂ (rationalAffineGermPoint z hzU₂ β),
    σ₁,
    hzU₂, hη₂, T, isSNCChart_etaleChartCentered hc₂ _ hα0,
    fun a => etaleChartCentered_germ_not_isUnit c₂ z hzU₂ β a, hσ₁iff,
    fun b hb => ⟨(hT b hb).1, ?_⟩, fun h' b hb hbT => ?_⟩
  · -- the tangent coordinate b is the pullback of a function of 𝒢 minus a constant
    obtain ⟨g, hg, hgη⟩ : ∃ g ∈ 𝒢, etaleChartStalkCoords c₂ η hη₂ (MvPolynomial.X b) =
        π.stalkMap η (Y.presheaf.germ U (π η) hηU g) := by
      have h1 := (hT b hb).2
      rw [hH] at h1
      exact h1
    have hsec : c₂.coords (MvPolynomial.X b) = X.presheaf.map (homOfLE hpre).op (π.app U g) := by
      apply AlgebraicGeometry.germ_injective_of_isIntegral X η hη₂
      rw [TopCat.Presheaf.germ_res_apply, ← Scheme.Hom.germ_stalkMap_apply]
      exact hgη
    refine ⟨g, hg, rationalAffineGermPoint z hzU₂ β (c₂.coords (MvPolynomial.X b)), ?_⟩
    rw [etaleChartStalkCoords_centered, map_sub, map_sub]
    congr 1
    · change X.presheaf.germ c₂.U z hzU₂ (c₂.coords (MvPolynomial.X b)) = _
      rw [hsec, TopCat.Presheaf.germ_res_apply, ← Scheme.Hom.germ_stalkMap_apply]
    · change _ = schemeStalkMapAlgHom (K := K) π z
        (sectionStalkAlgHom (K := K) U (π z) hzU (algebraMap K Γ(Y, U) _))
      rw [AlgHom.commutes, AlgHom.commutes]
  · -- the derivations of the translated chart are those of the chart
    rw [etaleCoordinateDerivation_of_sub_algebraMap (etaleChartStalkCoords c₂ η hη₂) _
      (etaleChartStalkCoords_formallyEtale c₂ η hη₂) _
      (fun i => rationalAffineGermPoint z hzU₂ β (c₂.coords (MvPolynomial.X i)))
      (fun i => etaleChartStalkCoords_centered c₂ _ η hη₂ i) b]
    exact hsatall h' b hb hbT

/-- The coordinates at a general closed point of the centre of a weight. There is a point η on all
the members of positive weight, specializing to the given point y and with no proper generization
on all of them, such that for every affine open U of the base containing π(η), every set 𝒢 of
generators of the functions on U and every open set V containing η there are a closed point z of
the closure of η in V over U and a simple normal crossing chart at z and η with: all coordinates
vanish at z; the selected coordinates are exactly those of the members of positive weight; the
coordinates of a set T outside the family are pullbacks of g - κ with g in 𝒢 and κ constant; for
every germ h at π(η) the derivatives of the pullback of h in the coordinates outside the family and
outside T lie in the maximal ideal of η. -/
theorem exists_closedPoint_tangent_chart_of_weight {r : ℕ} (ξ : Fin r → X)
    (hsnc : IsSNCFamily K n ξ) (w : Fin r → ℝ) (y : X)
    (hwy : ∀ k, w k ≠ 0 → y ∈ closure ({ξ k} : Set X)) :
    ∃ η : X, (∀ k, w k ≠ 0 → η ∈ closure ({ξ k} : Set X)) ∧ η ⤳ y ∧
      (∀ η' : X, (∀ k, w k ≠ 0 → η' ∈ closure ({ξ k} : Set X)) → η' ⤳ η → η' = η) ∧
      ∀ (U : Y.Opens) (_ : IsAffineOpen U) (_ : π η ∈ U) (𝒢 : Set Γ(Y, U)),
        Algebra.adjoin K 𝒢 = ⊤ → ∀ V : Set X, IsOpen V → η ∈ V →
        ∃ (z : X) (_ : IsClosed ({z} : Set X)) (_ : η ⤳ z) (_ : z ∈ V) (hzU : π z ∈ U)
          (c : EtaleChart K X n) (σc : Fin r → Option (Fin n)) (hz : z ∈ c.U) (hη : η ∈ c.U)
          (T : Finset (Fin n)), IsSNCChart c ξ σc ∧
          (∀ a, ¬ IsUnit (X.presheaf.germ c.U z hz (c.coords (MvPolynomial.X a)))) ∧
          (∀ k, (∃ a, σc k = some a) ↔ w k ≠ 0) ∧
          (∀ b ∈ T, (∀ k, σc k ≠ some b) ∧ ∃ g ∈ 𝒢, ∃ κ : K,
            etaleChartStalkCoords c z hz (MvPolynomial.X b) =
              π.stalkMap z (Y.presheaf.germ U (π z) hzU (g - algebraMap K Γ(Y, U) κ))) ∧
          ∀ (h' : Y.presheaf.stalk (π η)) (b : Fin n), (∀ k, σc k ≠ some b) → b ∉ T →
            etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
              (etaleChartStalkCoords_formallyEtale c η hη) b (π.stalkMap η h') ∈
                IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  have hsm : Smooth (X ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hjac : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨η, hη, hηy, hmax, hall⟩ :=
    exists_closedPoint_tangent_chart_of_weight_dense π ξ hsnc w y hwy
  refine ⟨η, hη, hηy, hmax, fun U hU hηU 𝒢 h𝒢 V hV hηV => ?_⟩
  obtain ⟨z, hzcl, hηz, hzV, -, h⟩ := hall U hU hηU 𝒢 h𝒢 V hV hηV Set.univ fun O hO hηO => by
    obtain ⟨z, ⟨hzη, hzO⟩, hzcl⟩ := nonempty_inter_closedPoints
      (Z := closure ({η} : Set X) ∩ O) ⟨η, subset_closure rfl, hηO⟩
      (isClosed_closure.isLocallyClosed.inter hO.isLocallyClosed)
    exact ⟨z, Set.mem_univ z, mem_closedPoints_iff.mp hzcl, hzη, hzO⟩
  exact ⟨z, hzcl, hηz, hzV, h⟩

end Centre

end MixedFujita
