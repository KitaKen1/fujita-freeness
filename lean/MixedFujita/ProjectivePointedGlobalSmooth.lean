/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointedBasis
public import MixedFujita.ProjectivePullbackIdealComparison
public import MixedFujita.ProjectiveCurveCohomology
public import MixedFujita.EtaleChartDimension
public import MixedFujita.PointedEtaleBertini
public import MixedFujita.CartierSectionZeroSmooth

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierBaseOpenAlgebra cartierBaseLocalAlgebra cartierBaseGlobalAlgebra
variable {K : Type u} [Field K] {Y : Scheme.{u}}
  [Y.Over (Spec (CommRingCat.of K))] {n : ℕ}
noncomputable def sectionOpenRestrictionAlgHom
    {U V : Y.Opens} (h : V ≤ U) : Γ(Y, U) →ₐ[K] Γ(Y, V) where
  toRingHom := (Y.presheaf.map (homOfLE h).op).hom
  commutes' a := by
    change (Y.presheaf.map (homOfLE h).op).hom
      (((Y.baseRingToStructurePresheaf K).app (op U)).hom a) =
      ((Y.baseRingToStructurePresheaf K).app (op V)).hom a
    rw [← CommRingCat.comp_apply, ← (Y.baseRingToStructurePresheaf K).naturality]
    rfl

theorem smoothProjective_exists_finite_etale_coordinate_atlas
    [PerfectField K] [IsIntegral Y] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (d : ℕ) (hdim : topologicalKrullDim Y = d) :
    ∃ (T : Finset Y) (c : T → EtaleChart K Y d) (k : T → Fin n),
      (∀ z : Y, ∃ j, z ∈ (c j).U) ∧
      ∀ j, (c j).U ≤ projectivePullbackCoordinateOpen e (k j) := by
  classical
  have := polynomialProjective_closedImmersion_isProper_over_field e he
  have : CompactSpace Y :=
    (quasiCompact_iff_compactSpace (Y ↘ Spec (CommRingCat.of K))).mp inferInstance
  have hloc (z : Y) : ∃ (c : EtaleChart K Y d) (k : Fin n),
      z ∈ c.U ∧ c.U ≤ projectivePullbackCoordinateOpen e k := by
    have hzsm : z ∈ (Y ↘ Spec (CommRingCat.of K)).smoothLocus := by
      rw [Scheme.Hom.smoothLocus_eq_top]
      trivial
    obtain ⟨m, c, hzc⟩ := exists_etaleChart_of_mem_smoothLocus (K := K) hzsm
    have hmd : m = d := by
      exact_mod_cast (etaleChart_topologicalKrullDim c).symm.trans hdim
    subst m
    obtain ⟨k, hzk⟩ := polynomialProjective_exists_coordinate_chart n K (e z)
    obtain ⟨g, hle, hzg⟩ := c.isAffine.exists_basicOpen_le
      (V := projectivePullbackCoordinateOpen e k) ⟨z, hzk⟩ hzc
    exact ⟨etaleChartBasicOpen c g ⟨⟨z, hzg⟩⟩, k, hzg, hle⟩
  choose c k hc hk using hloc
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun z => ((c z).U : Set Y))
    (fun z => (c z).U.isOpen) (fun z _ => Set.mem_iUnion.mpr ⟨z, hc z⟩)
  refine ⟨T, fun j => c j, fun j => k j, fun z => ?_, fun j => hk j⟩
  obtain ⟨z', hz', hzz'⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ z))
  exact ⟨⟨z', hz'⟩, hzz'⟩

theorem projectivePointedBasis_general_smooth_hypersurface
    [CharZero K] [IsAlgClosed K] [IsIntegral Y]
    [Smooth (Y ↘ Spec (CommRingCat.of K))]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (d : ℕ) (hdim : topologicalKrullDim Y = d) (hd : 0 < d)
    (x : Y) (hx : IsClosed {x}) {ι : Type u} [Fintype ι]
    (b : Module.Basis ι K (polynomialProjectiveVanishingForms 1 (e x))) :
    ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K, MvPolynomial.aeval t p ≠ 0 →
      let F := (∑ i, t i • b i).val
      Smooth (((projectiveHypersurfaceIdealSheaf F.val 1 F.property).comap e).subschemeι ≫
        (Y ↘ Spec (CommRingCat.of K))) := by
  classical
  obtain ⟨T, c, k, hcover, hsub⟩ := smoothProjective_exists_finite_etale_coordinate_atlas e he d hdim
  let Φ (j : T) : polynomialProjectiveVanishingForms 1 (e x) →ₗ[K] Γ(Y, (c j).U) :=
    (sectionOpenRestrictionAlgHom (hsub j)).toLinearMap.comp
      (projectivePointedChartEquationLinear e he x (k j))
  let v (j : T) (i : ι) := Φ j (b i)
  have hbase (j : T) : Ideal.span (Set.range (v j)) = ⊤ ∨
      ∃ β : Γ(Y, (c j).U) →ₐ[K] K, Ideal.span (Set.range (v j)) = RingHom.ker β.toRingHom :=
    projectivePointedBasis_restricted_pointed_or_free e he x hx b (k j)
      ⟨(c j).U, (c j).isAffine⟩ (hsub j)
  have hpoly (j : T) : ∃ p : MvPolynomial ι K, p ≠ 0 ∧ ∀ t : ι → K,
      MvPolynomial.aeval t p ≠ 0 → Algebra.Smooth K
        (Γ(Y, (c j).U) ⧸ Ideal.span ({OAI.MaximalSeshadri.LinearBertini.specializedSection (v j) t} :
          Set Γ(Y, (c j).U))) := by
    have := etaleChart_smooth (c j)
    rcases hbase j with hunit | ⟨β, hspan⟩
    · exact etaleChart_bertini_smooth_of_span_eq_top (c j) (v j) hunit
    · obtain ⟨p, hp, hs⟩ := etale_pointed_bertini_regular_equations (c j).coords
        (c j).formallyEtale ⟨0, hd⟩ β (v j) hspan
      exact ⟨p, hp, fun t ht => (hs t ht).2.2⟩
  choose p hp hs using hpoly
  refine ⟨∏ j, p j, Finset.prod_ne_zero_iff.mpr (fun j _ => hp j), fun t ht => ?_⟩
  have htj (j : T) : MvPolynomial.aeval t (p j) ≠ 0 := by
    rw [map_prod] at ht
    exact Finset.prod_ne_zero_iff.mp ht j (Finset.mem_univ j)
  let F : MvPolynomial.homogeneousSubmodule (Fin n) K 1 := (∑ i, t i • b i).val
  let I := (projectiveHypersurfaceIdealSheaf F.val 1 F.property).comap e
  have hI (j : T) : I.ideal ⟨(c j).U, (c j).isAffine⟩ =
      Ideal.span ({OAI.MaximalSeshadri.LinearBertini.specializedSection (v j) t} :
        Set Γ(Y, (c j).U)) := by
    let U : Y.affineOpens := ⟨projectivePullbackCoordinateOpen e (k j),
      projectivePullbackCoordinateOpen_isAffineOpen e (k j)⟩
    have hnon : Nonempty (projectivePullbackCoordinateOpen e (k j)) := by
      obtain ⟨z, hz⟩ := Set.nonempty_coe_sort.mp (c j).nonempty
      exact ⟨⟨z, hsub j hz⟩⟩
    let a : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} := ⟨k j, hnon⟩
    have hcoord := projectiveHypersurfacePullback_coordinate_ideal e 1 F.val F.property a
    change I.ideal U = Ideal.span (Set.singleton (projectivePointedChartEquation e x (k j)
      (∑ i, t i • b i)) : Set Γ(Y, U.1)) at hcoord
    rw [← I.map_ideal (U := ⟨(c j).U, (c j).isAffine⟩) (V := U) (hsub j),
      hcoord, Ideal.map_span]
    erw [Set.image_singleton]
    congr 2
    change Φ j (∑ i, t i • b i) = ∑ i, t i • Φ j (b i)
    simp only [map_sum, map_smul]
  have hQ (j : T) : Algebra.Smooth K (Γ(Y, (c j).U) ⧸ I.ideal ⟨(c j).U, (c j).isAffine⟩) := by
    rw [hI]
    exact hs j t (htj j)
  let : ∀ j : T, Algebra.Smooth K
      (Γ(Y, (c j).U) ⧸ I.ideal ⟨(c j).U, (c j).isAffine⟩) := hQ
  exact smooth_subscheme_of_affine_quotients Y (Y ↘ Spec (CommRingCat.of K))
    (fun j : T => ⟨(c j).U, (c j).isAffine⟩) hcover
    (fun j => affineOpen_fromSpec_comp_over (K := K) ⟨(c j).U, (c j).isAffine⟩) I

end MixedFujita
