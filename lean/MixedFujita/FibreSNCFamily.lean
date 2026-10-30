/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreSNCCharts

/-!
The simple normal crossing family of a fibre (step 10, R4-3).

* `isSNCChart_fibre`: let `X` be a scheme over `A` with fibres `Y = X ×_A K` (`A ⊆ K`) and
  `Y' = X ×_A κ`, and let `V` be an affine open of `X` with étale coordinates. If the chart of `Y`
  over `V` is simple normal crossing for `ξ` (normalized: components with a coordinate meet the
  chart), and points `ξ'_k` of `Y'` have closures the preimages of the closures of the images
  `g(ξ_k)`, then the chart of `Y'` over `V` is simple normal crossing for `ξ'` (checks 525, 522).
* `exists_ne_zero_forall_mem_cover_fibre`: for `X` universally closed over a domain `A`, opens of `X`
  covering the image of `Y = X ×_A K` cover every fibre over a field in which a certain `f ≠ 0` is a
  unit. The complement `C` of the opens is closed, its image in `Spec A` is closed (universal
  closedness) and misses the generic point (a point of `X` over the generic point comes from `Y`);
  a basic open `D(f)` avoids it.

Simple normal crossing charts covering a scheme give a simple normal crossing family
(`isSNCFamily_of_cover`). For the closure `T_A` with the charts of check 512 these give the simple
normal crossing family of the fibre `T_κ` (with the boundary points of check 523) for check 491.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Simple normal crossing charts covering a scheme give a simple normal crossing family. -/
theorem isSNCFamily_of_cover {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of K))] {d r : ℕ} (ξ : Fin r → X) {ι : Type*}
    (c : ι → EtaleChart K X d) (σ : ι → Fin r → Option (Fin d))
    (hc : ∀ i, IsSNCChart (c i) ξ (σ i)) (hcov : ∀ x : X, ∃ i, x ∈ (c i).U) :
    IsSNCFamily K d ξ := fun x =>
  let ⟨i, hi⟩ := hcov x
  ⟨c i, σ i, hi, hc i⟩

section Chart

attribute [local instance] structureSectionsAlgebra

variable {A K κ : Type u} [CommRing A] [Field K] [Algebra A K] [Field κ] [Algebra A κ]
  {X Y Y' : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of K))]
  [Y'.Over (Spec (CommRingCat.of κ))] {g : Y ⟶ X} {g' : Y' ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of K)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A K))))
  (H' : IsPullback g' (Y' ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
  [IsAffineHom g] [IsAffineHom g'] [IsIntegral Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {d : ℕ} {V : X.Opens} (hV : IsAffineOpen V) (y : MvPolynomial (Fin d) A →ₐ[A] Γ(X, V))
  (hy : y.toRingHom.FormallyEtale) (hne : Nonempty (g ⁻¹ᵁ V)) (hne' : Nonempty (g' ⁻¹ᵁ V))

include hy in
/-- **The charts of a fibre are simple normal crossing** for the points whose closures are the
preimages of the closures of the boundary points of the generic chart. -/
theorem isSNCChart_fibre [Algebra.FinitePresentation A Γ(X, V)]
    (hK : Function.Injective (algebraMap A K)) {r : ℕ} (ξ : Fin r → Y)
    (σ : Fin r → Option (Fin d)) (hc : IsSNCChart (fibreEtaleChart H hV y hy hne) ξ σ)
    (hσ : ∀ k a, σ k = some a → ξ k ∈ g ⁻¹ᵁ V) (ξ' : Fin r → Y')
    (hξ' : ∀ k, closure ({ξ' k} : Set Y') = g' ⁻¹' closure ({g (ξ k)} : Set X)) :
    IsSNCChart (fibreEtaleChart H' hV y hy hne') ξ' σ := by
  refine ⟨hc.1, fun k => ?_⟩
  cases hk : σ k with
  | none =>
    rw [Option.elim_none]
    apply closure_fibrePoint_inter_eq_empty (hξ' k)
    apply closure_inter_eq_empty_of_notMem V.isOpen
    intro hgξ
    have h := hc.2 k
    rw [hk, Option.elim_none] at h
    have hmem : ξ k ∈ closure ({ξ k} : Set Y) ∩ (fibreEtaleChart H hV y hy hne).U :=
      ⟨subset_closure rfl, hgξ⟩
    rw [h] at hmem
    exact hmem
  | some a =>
    rw [Option.elim_some]
    have hR := closure_image_inter_eq_zeroLocus H hV y hy hne hK ξ σ hc k a hk (hσ k a hk)
    have h := closure_fibrePoint_inter (hξ' k) (y (MvPolynomial.X a)) hR
    rw [fibreEtaleChart_coords_X H' hV y hy hne' a]
    exact h

end Chart

section Cover

variable {A K : Type u} [CommRing A] [IsDomain A] [Field K] [Algebra A K] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of K))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of K)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A K))))

include H in
/-- **Opens covering the generic fibre cover the fibres away from one element.** -/
theorem exists_ne_zero_forall_mem_cover_fibre [UniversallyClosed (X ↘ Spec (CommRingCat.of A))]
    (hK : Function.Injective (algebraMap A K)) {ι : Type*} (V : ι → X.Opens)
    (hcov : ∀ t : Y, ∃ i, g t ∈ V i) :
    ∃ f : A, f ≠ 0 ∧ ∀ (κ : Type u) [Field κ] [Algebra A κ], IsUnit (algebraMap A κ f) →
      ∀ (Y' : Scheme.{u}) [Y'.Over (Spec (CommRingCat.of κ))] (g' : Y' ⟶ X),
        IsPullback g' (Y' ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
          (Spec.map (CommRingCat.ofHom (algebraMap A κ))) →
        ∀ t : Y', ∃ i, g' t ∈ V i := by
  classical
  let q := X ↘ Spec (CommRingCat.of A)
  let C : Set X := ⋂ i, ((V i : Set X))ᶜ
  have hC : IsClosed C := isClosed_iInter fun i => (V i).isOpen.isClosed_compl
  have hqC : IsClosed (q '' C) := q.isClosedMap C hC
  -- the generic point of `Spec A` is not in the image of `C`
  let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : (η : Spec (CommRingCat.of A)) ∉ q '' C := by
    rintro ⟨x, hxC, hxη⟩
    let s : Spec (CommRingCat.of K) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hs : q x = Spec.map (CommRingCat.ofHom (algebraMap A K)) s := by
      rw [hxη, Spec.map_apply, CommRingCat.hom_ofHom]
      refine PrimeSpectrum.ext ?_
      ext a
      change a ∈ (⊥ : Ideal A) ↔ algebraMap A K a ∈ (⊥ : Ideal K)
      rw [Ideal.mem_bot, Ideal.mem_bot]
      exact ⟨fun h => by rw [h, map_zero], fun h => hK (h.trans (map_zero _).symm)⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x s hs
    obtain ⟨i, hi⟩ := hcov (H.isoPullback.inv z)
    have : g (H.isoPullback.inv z) = x := by
      rw [← Scheme.Hom.comp_apply, H.isoPullback_inv_fst, hz]
    rw [this] at hi
    exact Set.mem_iInter.1 hxC i hi
  -- a basic open around the generic point avoids the image
  obtain ⟨_, ⟨f, rfl⟩, hηf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show (η : PrimeSpectrum A) ∈ (q '' C)ᶜ from hη) hqC.isOpen_compl
  refine ⟨f, ?_, fun κ _ _ hf Y' _ g' H' t => ?_⟩
  · rintro rfl
    simp at hηf
  · by_contra hnot
    have htC : g' t ∈ C := Set.mem_iInter.2 fun i hi => hnot ⟨i, hi⟩
    apply hsub _ ⟨g' t, htC, rfl⟩
    -- the image of `t` in `Spec A` lies over `D(f)`
    have hw : q (g' t) = Spec.map (CommRingCat.ofHom (algebraMap A κ))
        ((Y' ↘ Spec (CommRingCat.of κ)) t) := by
      rw [← Scheme.Hom.comp_apply, H'.w, Scheme.Hom.comp_apply]
    change q (g' t) ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A))
    rw [hw, Spec.map_apply, CommRingCat.hom_ofHom, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    exact fun h => ((Y' ↘ Spec (CommRingCat.of κ)) t).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hf)

end Cover

end MixedFujita
