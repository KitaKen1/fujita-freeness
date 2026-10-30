/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartSectionExtension
public import MixedFujita.CartierSectionRatioGenerators

/-!
An affine map from a proper integral scheme to polynomial projective space makes the explicit
pullback hyperplane Cartier divisor ample in the projective-embedding definition. Indeed every
sufficiently large multiple is very ample. On each nonempty coordinate open choose actual finite
algebra generators. Extend them to section ratios in one common degree, adjoin the coordinate
power denominators, and apply the existing closed-immersion criterion. In particular this
applies to the finite map on the actual Stein target, without any supplied embedding of it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra cartierBaseOpenAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  (e : X ⟶ polynomialProjectiveScheme n K)
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)

/-- Every sufficiently large multiple of the actual hyperplane divisor is very ample when
the source is proper over K and the map to projective space is affine. -/
theorem projectiveHyperplaneCartier_eventually_veryAmple_of_affine
    [IsAffineHom e] [IsProper (X ↘ Spec (CommRingCat.of K))] :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      CartierIsVeryAmpleProj K (N • projectiveHyperplaneCartier e g hg hggen) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace
    (X ↘ Spec (CommRingCat.of K))
  let J := ULift.{u} {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}
  have haff (j : J) : IsAffineOpen (projectivePullbackCoordinateOpen e j.down.val) :=
    (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K j.down.val) one_pos).preimage e
  obtain ⟨jg, hjg⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint X))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨jg, ⟨⟨genericPoint X, hjg⟩⟩⟩
  choose m f hf using fun j : J => Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (sectionsBaseOpen_finiteType (K := K) (haff j))
  choose B hBpos hB using fun (j : J) (l : Fin (m j)) =>
    projectiveChart_regular_function_eventually_section_ratio e g hg hggen j₀ j.down
      (f j (MvPolynomial.X l))
  let N₀ := max 1 (Finset.univ.sup fun j : J => Finset.univ.sup (B j))
  refine ⟨N₀, lt_of_lt_of_le one_pos (le_max_left _ _), fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hN)
  have hBN (j : J) (l : Fin (m j)) : B j l ≤ N :=
    (Finset.le_sup (f := B j) (Finset.mem_univ l)).trans
      ((Finset.le_sup (f := fun j : J => Finset.univ.sup (B j)) (Finset.mem_univ j)).trans
        ((le_max_right _ _).trans hN))
  choose s hs using fun (j : J) (l : Fin (m j)) => hB j l N (hBN j l)
  let H := projectiveHyperplaneCartier e g hg hggen
  let den (j : J) : Γ((N • H).sheaf, ⊤) :=
    cartierSectionPower H (projectiveCoordinateCartierSection e g hg hggen j₀ j.down.val) N
  have hdenV (j : J) : cartierSectionNonvanishingOpen (N • H) (den j) =
      projectivePullbackCoordinateOpen e j.down.val := by
    rw [cartierSectionPower_nonvanishingOpen _ _ hNpos,
      projectiveCoordinateCartierSection_nonvanishing]
  have hdenne (j : J) : den j ≠ 0 :=
    (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp (by rw [hdenV]; exact j.down.property)
  let I := (j : J) × Option (Fin (m j))
  let sec (a : I) : Γ((N • H).sheaf, ⊤) := a.2.elim (den a.1) (s a.1)
  let eqv := Fintype.equivFin I
  let t (q : Fin (Fintype.card I)) : Γ((N • H).sheaf, ⊤) := sec (eqv.symm q)
  let idx (j : J) := eqv ⟨j, none⟩
  have htden (j : J) : t (idx j) = den j := by
    change sec (eqv.symm (eqv ⟨j, none⟩)) = den j
    rw [Equiv.symm_apply_apply]
    rfl
  have htne (j : J) : t (idx j) ≠ 0 := by rw [htden]; exact hdenne j
  have htV (j : J) : cartierSectionNonvanishingOpen (N • H) (t (idx j)) =
      projectivePullbackCoordinateOpen e j.down.val := by rw [htden, hdenV]
  have hcover : (⨆ j : J, cartierSectionNonvanishingOpen (N • H) (t (idx j))) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨j, hj⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
    refine Opens.mem_iSup.mpr ⟨ULift.up ⟨j, ⟨⟨x, hj⟩⟩⟩, ?_⟩
    rwa [htV]
  refine cartierIsVeryAmpleProj_of_sections (K := K) (N • H) t idx htne hcover ?_ ?_
  · intro j
    rw [htV]
    exact haff j
  · intro j
    have := j.down.property
    refine eval₂Hom_cartierSectionRatio_surjective_of_generators (N • H) t (idx j) (htne j)
      (projectivePullbackCoordinateOpen e j.down.val) (htV j) (f j) (hf j) ?_
    intro l
    refine ⟨eqv ⟨j, some l⟩, ?_⟩
    have hts : t (eqv ⟨j, some l⟩) = s j l := by
      change sec (eqv.symm (eqv ⟨j, some l⟩)) = s j l
      rw [Equiv.symm_apply_apply]
      rfl
    rw [htden, hts]
    exact hs j l

/-- Ampleness here is the actual projective-embedding Cartier definition. -/
theorem projectiveHyperplaneCartier_isAmpleProj_of_affine
    [IsAffineHom e] [IsProper (X ↘ Spec (CommRingCat.of K))] :
    CartierIsAmpleProj K (projectiveHyperplaneCartier e g hg hggen) := by
  obtain ⟨N, hN, h⟩ := projectiveHyperplaneCartier_eventually_veryAmple_of_affine e g hg hggen
  obtain ⟨r, i, hi, hbase, F, hF, hFgen, φ, heq⟩ := h N le_rfl
  exact ⟨N, hN, r, i, hi, hbase, F, hF, hFgen, φ, heq⟩

/-- A finite projective-space morphism over K supplies projective Cartier ampleness of its
explicit hyperplane divisor; properness of the source is derived, not assumed separately. -/
theorem projectiveHyperplaneCartier_isAmpleProj_of_finite [IsFinite e]
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K)) :
    CartierIsAmpleProj K (projectiveHyperplaneCartier e g hg hggen) := by
  have := polynomialProjectiveToBase_isProper n K
  have : IsProper (X ↘ Spec (CommRingCat.of K)) := by rw [← he]; infer_instance
  exact projectiveHyperplaneCartier_isAmpleProj_of_affine e g hg hggen

end MixedFujita
