/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveCoordinateAtlas
public import MixedFujita.ProjectiveIdealGeneration

/-!
Generators of a centre ideal on the coordinate atlas of a projective scheme. Let X be a closed
subscheme of projective space over a field and I an ideal sheaf on X. By the extension of
sections of the pinned SlopdeGeometrieAlgebrique, every element of I on a standard chart is, for
all large d, the chart component of a global section of the d-th twist of the pushed forward
ideal. The chart components of such a twisted section are elements g_i of I(U_i) with
g_i = (x_k/x_i)^d g_k on overlaps. Applying this to finitely many generators on each chart, with
one d, gives one finite family of such compatible elements generating I on every chart: the
dehomogenizations of forms of degree d generating the ideal of the centre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open AlgebraicGeometry.Scheme.IdealSheafData

namespace MixedFujita

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Transition

variable {K : Type u} [CommRing K] {n : ℕ}

/-- On the overlap of two standard charts, the transition function of the d-th twist is the d-th
power of the ratio x_k/x_i. -/
theorem polynomialProjective_trans_restrict (d : ℕ) (i k : Fin n)
    (hU : projectiveSpace.topStd (Fin n) K i ⊓ projectiveSpace.topStd (Fin n) K k ≤
      projectiveSpace.topStd₂ (Fin n) K i k) :
    (Proj (homogeneousSubmodule (Fin n) K)).presheaf.map (homOfLE hU).op
        ((Proj (homogeneousSubmodule (Fin n) K)).presheaf.map
          (homOfLE (inf_le_right : projectiveSpace.topStd₂ (Fin n) K i k ≤
            projectiveSpace.stdCover (Fin n) K i ⊓ projectiveSpace.stdCover (Fin n) K k)).op
          ((projectiveSpace.twistingBundle (Fin n) K).trans (d : ℤ)
            (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k))) =
      (Proj (homogeneousSubmodule (Fin n) K)).presheaf.map
        (homOfLE (inf_le_left : projectiveSpace.topStd (Fin n) K i ⊓
          projectiveSpace.topStd (Fin n) K k ≤ projectiveSpace.topStd (Fin n) K i)).op
        (projectiveSpace.ratio K k i) ^ d := by
  have h : (projectiveSpace.twistingBundle (Fin n) K).trans (d : ℤ)
      (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k) =
      Proj.fracSection _ (projectiveSpace.X_mem k) (projectiveSpace.X_mem i)
        (projectiveSpace.stdCover (Fin n) K i ⊓ projectiveSpace.stdCover (Fin n) K k)
        inf_le_left ^ d := projectiveSpace.transStd_natCast d i k
  rw [h, map_pow, map_pow]
  rfl

end Transition

section Components

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e] (I : X.IdealSheafData)

/-- The preimage of the overlap of two standard charts. -/
noncomputable abbrev projectiveAtlasOpen₂ (i k : Fin n) : X.affineOpens :=
  ⟨e ⁻¹ᵁ projectiveSpace.topStd₂ (Fin n) K i k,
    (projectiveSpace.isAffineOpen_topStd₂ (σ := Fin n) (A := K) i k).preimage e⟩

/-- The chart component of a twisted global section of the pushed forward ideal, as an element
of the ideal on the chart. -/
noncomputable def twistedIdealComponent (d : ℕ)
    (t : (projectiveSpace.twistingBundle (Fin n) K).twistAddSubgroup
      ((Scheme.Modules.pushforward e).obj I.toModules) (d : ℤ) ⊤) (i : Fin n) :
    I.ideal (projectiveAtlasOpen e i) :=
  I.toModulesSectionsEquiv (projectiveAtlasOpen e i)
    (@id Γ(I.toModules, (projectiveAtlasOpen e i).1) (t.1 (projectiveSpace.idx (Fin n) K i)))

/-- The compatibility of the chart components of a twisted section, on the preimage of the
overlap of two standard charts. -/
theorem twistedIdealComponent_overlap (d : ℕ)
    (t : (projectiveSpace.twistingBundle (Fin n) K).twistAddSubgroup
      ((Scheme.Modules.pushforward e).obj I.toModules) (d : ℤ) ⊤) (i k : Fin n)
    (hi : projectiveAtlasOpen₂ e i k ≤ projectiveAtlasOpen e i)
    (hk : projectiveAtlasOpen₂ e i k ≤ projectiveAtlasOpen e k) :
    X.presheaf.map (homOfLE hi).op
        (twistedIdealComponent e I d t i : Γ(X, projectiveAtlasOpen e i)) =
      e.app (projectiveSpace.topStd₂ (Fin n) K i k)
          ((polynomialProjectiveScheme n K).presheaf.map
            (homOfLE (inf_le_right : projectiveSpace.topStd₂ (Fin n) K i k ≤
              projectiveSpace.stdCover (Fin n) K i ⊓ projectiveSpace.stdCover (Fin n) K k)).op
            ((projectiveSpace.twistingBundle (Fin n) K).trans (d : ℤ)
              (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k))) *
        X.presheaf.map (homOfLE hk).op
          (twistedIdealComponent e I d t k : Γ(X, projectiveAtlasOpen e k)) := by
  have key : I.toModules.presheaf.map (homOfLE hi).op
        (@id Γ(I.toModules, (projectiveAtlasOpen e i).1)
          (t.1 (projectiveSpace.idx (Fin n) K i))) =
      e.app (projectiveSpace.topStd₂ (Fin n) K i k)
          ((polynomialProjectiveScheme n K).presheaf.map
            (homOfLE (inf_le_right : projectiveSpace.topStd₂ (Fin n) K i k ≤
              projectiveSpace.stdCover (Fin n) K i ⊓ projectiveSpace.stdCover (Fin n) K k)).op
            ((projectiveSpace.twistingBundle (Fin n) K).trans (d : ℤ)
              (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k))) •
        I.toModules.presheaf.map (homOfLE hk).op
          (@id Γ(I.toModules, (projectiveAtlasOpen e k).1)
            (t.1 (projectiveSpace.idx (Fin n) K k))) :=
    t.2 (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k)
  have h := congrArg (fun z : Γ(I.toModules, (projectiveAtlasOpen₂ e i k).1) =>
    ((I.toModulesSectionsEquiv (projectiveAtlasOpen₂ e i k) z :
      I.ideal (projectiveAtlasOpen₂ e i k)) : Γ(X, projectiveAtlasOpen₂ e i k))) key
  rw [I.coe_toModulesSectionsEquiv_smul] at h
  exact h

/-- On the overlap of two charts the components of a twisted section differ by the d-th power
of the ratio of the two coordinates. -/
theorem twistedIdealComponent_cocycle (d : ℕ)
    (t : (projectiveSpace.twistingBundle (Fin n) K).twistAddSubgroup
      ((Scheme.Modules.pushforward e).obj I.toModules) (d : ℤ) ⊤) (i k : Fin n) :
    X.presheaf.map (homOfLE (inf_le_left :
        (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
          (projectiveAtlasOpen e i).1)).op
        (twistedIdealComponent e I d t i : Γ(X, projectiveAtlasOpen e i)) =
      X.presheaf.map (homOfLE (inf_le_left :
          (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
            (projectiveAtlasOpen e i).1)).op (projectiveAtlasRatio e i k) ^ d *
        X.presheaf.map (homOfLE (inf_le_right :
          (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
            (projectiveAtlasOpen e k).1)).op
          (twistedIdealComponent e I d t k : Γ(X, projectiveAtlasOpen e k)) := by
  have hi : projectiveAtlasOpen₂ e i k ≤ projectiveAtlasOpen e i :=
    fun x hx => (show e x ∈ projectiveSpace.topStd (Fin n) K i from ⟨trivial, hx.2.1⟩)
  have hk : projectiveAtlasOpen₂ e i k ≤ projectiveAtlasOpen e k :=
    fun x hx => (show e x ∈ projectiveSpace.topStd (Fin n) K k from ⟨trivial, hx.2.2⟩)
  have hU : projectiveSpace.topStd (Fin n) K i ⊓ projectiveSpace.topStd (Fin n) K k ≤
      projectiveSpace.topStd₂ (Fin n) K i k := fun y hy => ⟨trivial, hy.1.2, hy.2.2⟩
  have hV : (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
      (projectiveAtlasOpen₂ e i k).1 := fun x hx => hU hx
  have eW : (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
      e ⁻¹ᵁ (projectiveSpace.topStd (Fin n) K i ⊓ projectiveSpace.topStd (Fin n) K k) :=
    le_rfl
  have hs : X.presheaf.map (homOfLE hV).op
        (e.app (projectiveSpace.topStd₂ (Fin n) K i k)
          ((polynomialProjectiveScheme n K).presheaf.map
            (homOfLE (inf_le_right : projectiveSpace.topStd₂ (Fin n) K i k ≤
              projectiveSpace.stdCover (Fin n) K i ⊓ projectiveSpace.stdCover (Fin n) K k)).op
            ((projectiveSpace.twistingBundle (Fin n) K).trans (d : ℤ)
              (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k)))) =
      X.presheaf.map (homOfLE (inf_le_left :
          (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
            (projectiveAtlasOpen e i).1)).op (projectiveAtlasRatio e i k) ^ d := by
    have h1 := schemeHom_app_restrict_apply e hV hU eW
      ((polynomialProjectiveScheme n K).presheaf.map
        (homOfLE (inf_le_right : projectiveSpace.topStd₂ (Fin n) K i k ≤
          projectiveSpace.stdCover (Fin n) K i ⊓ projectiveSpace.stdCover (Fin n) K k)).op
        ((projectiveSpace.twistingBundle (Fin n) K).trans (d : ℤ)
          (projectiveSpace.idx (Fin n) K i) (projectiveSpace.idx (Fin n) K k)))
    have h2 := schemeHom_app_restrict_apply e
      (inf_le_left : (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
        (projectiveAtlasOpen e i).1)
      (inf_le_left : projectiveSpace.topStd (Fin n) K i ⊓ projectiveSpace.topStd (Fin n) K k ≤
        projectiveSpace.topStd (Fin n) K i) eW (projectiveSpace.ratio K k i)
    have h3 := congrArg (e.appLE
      (projectiveSpace.topStd (Fin n) K i ⊓ projectiveSpace.topStd (Fin n) K k)
      ((projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1) eW)
      (polynomialProjective_trans_restrict (K := K) d i k hU)
    rw [map_pow] at h3
    exact h1.trans (h3.trans (congrArg (· ^ d) h2.symm))
  exact (CohomologyAux.presheaf_map_map hi hV _).symm.trans
    ((congrArg (fun z => (X.presheaf.map (homOfLE hV).op) z)
      (twistedIdealComponent_overlap e I d t i k hi hk)).trans
    ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) hs (CohomologyAux.presheaf_map_map hk hV _))))

end Components

section Generators

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e] (I : X.IdealSheafData)

/-- A centre ideal on a closed subscheme of projective space is generated, on every chart of the
coordinate atlas, by one finite family of elements that differ on overlaps by the d-th powers of
the ratios of the coordinates. -/
theorem exists_projective_ideal_atlas_generators :
    ∃ (d m : ℕ) (g : ∀ i, Fin m → I.ideal (projectiveAtlasOpen e i)),
      (∀ i, Ideal.span (Set.range fun l => (g i l : Γ(X, projectiveAtlasOpen e i))) =
        I.ideal (projectiveAtlasOpen e i)) ∧
      ∀ i k l,
        X.presheaf.map (homOfLE (inf_le_left :
            (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
              (projectiveAtlasOpen e i).1)).op (g i l : Γ(X, projectiveAtlasOpen e i)) =
          X.presheaf.map (homOfLE (inf_le_left :
              (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
                (projectiveAtlasOpen e i).1)).op (projectiveAtlasRatio e i k) ^ d *
            X.presheaf.map (homOfLE (inf_le_right :
              (projectiveAtlasOpen e i).1 ⊓ (projectiveAtlasOpen e k).1 ≤
                (projectiveAtlasOpen e k).1)).op (g k l : Γ(X, projectiveAtlasOpen e k)) := by
  classical
  have hqc : I.toModules.IsQuasicoherent := ideal_toModules_isQuasicoherent I
  have hF : ((Scheme.Modules.pushforward e).obj I.toModules).IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_pushforward e I.toModules
  have hfg : ∀ i, ∃ S : Finset Γ(X, projectiveAtlasOpen e i),
      Ideal.span (S : Set Γ(X, projectiveAtlasOpen e i)) = I.ideal (projectiveAtlasOpen e i) := by
    intro i
    have : IsNoetherianRing Γ(X, projectiveAtlasOpen e i) :=
      IsLocallyNoetherian.component_noetherian (projectiveAtlasOpen e i)
    exact IsNoetherian.noetherian (I.ideal (projectiveAtlasOpen e i))
  choose S hS using hfg
  have hmem : ∀ j : (Σ i : Fin n, ↥(S i)),
      (j.2 : Γ(X, projectiveAtlasOpen e j.1)) ∈ I.ideal (projectiveAtlasOpen e j.1) :=
    fun j => hS j.1 ▸ Ideal.subset_span j.2.2
  have hex : ∀ j : (Σ i : Fin n, ↥(S i)), ∃ n₀ : ℕ, ∀ d ≥ n₀,
      ∃ t : (projectiveSpace.twistingBundle (Fin n) K).twistAddSubgroup
        ((Scheme.Modules.pushforward e).obj I.toModules) (d : ℤ) ⊤,
        twistedIdealComponent e I d t j.1 = ⟨j.2, hmem j⟩ := by
    intro j
    obtain ⟨n₀, hn₀⟩ := projectiveSpace.exists_twist_section_eq
      ((Scheme.Modules.pushforward e).obj I.toModules) j.1
      (@id Γ((Scheme.Modules.pushforward e).obj I.toModules,
          projectiveSpace.topStd (Fin n) K j.1)
        ((I.toModulesSectionsEquiv (projectiveAtlasOpen e j.1)).symm ⟨j.2, hmem j⟩))
    refine ⟨n₀, fun d hd => ?_⟩
    obtain ⟨t, ht⟩ := hn₀ d hd
    refine ⟨t, ?_⟩
    have h := congrArg (fun z : Γ(I.toModules, (projectiveAtlasOpen e j.1).1) =>
      I.toModulesSectionsEquiv (projectiveAtlasOpen e j.1) z) ht
    exact h.trans (LinearEquiv.apply_symm_apply _ _)
  choose n₀ hn₀ using hex
  have hd : ∀ j, n₀ j ≤ Finset.univ.sup n₀ := fun j => Finset.le_sup (Finset.mem_univ j)
  choose t ht using fun j => hn₀ j (Finset.univ.sup n₀) (hd j)
  refine ⟨Finset.univ.sup n₀, Fintype.card (Σ i : Fin n, ↥(S i)),
    fun i l => twistedIdealComponent e I (Finset.univ.sup n₀)
      (t ((Fintype.equivFin (Σ i : Fin n, ↥(S i))).symm l)) i, ?_, ?_⟩
  · intro i
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨l, rfl⟩
      exact (twistedIdealComponent e I (Finset.univ.sup n₀)
        (t ((Fintype.equivFin (Σ i : Fin n, ↥(S i))).symm l)) i).2
    · refine (hS i).symm.le.trans (Ideal.span_mono ?_)
      intro a ha
      refine ⟨Fintype.equivFin (Σ i : Fin n, ↥(S i)) ⟨i, a, ha⟩, ?_⟩
      have h := congrArg (fun z : I.ideal (projectiveAtlasOpen e i) =>
        (z : Γ(X, projectiveAtlasOpen e i))) (ht ⟨i, a, ha⟩)
      simp only [Equiv.symm_apply_apply]
      exact h
  · intro i k l
    exact twistedIdealComponent_cocycle e I (Finset.univ.sup n₀)
      (t ((Fintype.equivFin (Σ i : Fin n, ↥(S i))).symm l)) i k

end Generators

end MixedFujita
