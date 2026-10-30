/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperIntegralSmoothComponent
public import MixedFujita.ProjectivePointedSmoothAvoidance
public import MixedFujita.ProjectivePointedSmoothCut
public import MixedFujita.GeometricSmoothTaylor

/-! The whole effective Cartier hyperplane cut and finite avoidance are retained. The chosen clopen component is proper, smooth and integral of dimension d-1, with a point mapping to the prescribed source point. The whole cut is not asserted integral. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomialProjective_pointed_proper_integral_smooth_component
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (d : ℕ) (hdim : topologicalKrullDim Y = d) (hd : 0 < d)
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (F : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
      (hgeneric : F.val ∉ (e (genericPoint Y)).asHomogeneousIdeal),
      let I := projectivePullbackCartierIdealSheaf e 1 F.val F.property Nat.zero_lt_one hgeneric
      Nonempty (InvertibleIdealPresentation I) ∧
        (∀ y ∈ Z, y ∉ Set.range I.subschemeι) ∧
        Smooth (I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K))) ∧
        ∃ (T : Scheme.{u}) (j : T ⟶ I.subscheme),
          IsOpenImmersion j ∧ IsClosedImmersion j ∧ IsIntegral T ∧
          Smooth (j ≫ I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K))) ∧
          IsProper (j ≫ I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K))) ∧
          topologicalKrullDim T = (d - 1 : ℕ) ∧
          ∃ t : T, (j ≫ I.subschemeι) t = x := by
  obtain ⟨F, hgeneric, hpres, hxI, havoid, hsmooth⟩ :=
    polynomialProjective_pointed_global_smooth_cartierCut e he d hdim hd x hx Z hZ hxZ
  let I := projectivePullbackCartierIdealSheaf e 1 F.val F.property Nat.zero_lt_one hgeneric
  let g := I.subschemeι ≫ (Y ↘ Spec (CommRingCat.of K))
  have := polynomialProjective_closedImmersion_isProper_over_field e he
  have : Smooth g := hsmooth
  have : IsProper g := inferInstance
  obtain ⟨z, hzx⟩ := hxI
  obtain ⟨T, j, hj, hjc, hT, hTs, hTp, t, ht⟩ :=
    smoothProperScheme_exists_integral_component g z
  let := hj
  let := hjc
  let := hT
  let := hTs
  have htx : (j ≫ I.subschemeι) t = x := by
    simpa only [Scheme.Hom.comp_apply, ht] using hzx
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e (I.subschemeι z))
  let : Nonempty (projectivePullbackCoordinateOpen e k) := ⟨⟨I.subschemeι z, hk⟩⟩
  have := isRegularLocalRing_stalk (Y ↘ Spec (CommRingCat.of K)) (I.subschemeι z)
  have hI := projectivePullbackCartierIdealSheaf_stalk_eq_span e 1 F.val F.property
    Nat.zero_lt_one hgeneric k (I.subschemeι z) hk
  have hreg := projectivePullbackHomogeneousEquation_germ_regular e k 1 F.val F.property
    Nat.zero_lt_one hgeneric (I.subschemeι z) hk
  have hdrop := subscheme_stalk_dimension_drop_of_regular_equation I z _ hI hreg
  have heq := ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap t)).commRingCatIsoToRingEquiv
  rw [ht] at heq
  have hst : ringKrullDim (T.presheaf.stalk t) + 1 = (d : WithBot ℕ∞) := by
    rw [← heq, hdrop, hzx, geometricSmoothScheme_closedPoint_stalk_dimension (K := K) d hdim x hx]
  have hst' : ringKrullDim (T.presheaf.stalk t) = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    apply ENat.WithBot.add_one_cancel.mp
    rw [hst]
    norm_cast
    omega
  have hclosed : IsClosed ({t} : Set T) := by
    have hinj : Function.Injective (j ≫ I.subschemeι) :=
      I.subschemeι.isClosedEmbedding.injective.comp j.isOpenEmbedding.injective
    have hpre : (j ≫ I.subschemeι) ⁻¹' {x} = {t} := by
      ext s
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun hs => hinj (hs.trans htx.symm), fun hs => hs ▸ htx⟩
    rw [← hpre]
    exact hx.preimage (j ≫ I.subschemeι).continuous
  have hTD : topologicalKrullDim T = (d - 1 : ℕ) :=
    (TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
      (j ≫ g) hclosed).symm.trans hst'
  exact ⟨F, hgeneric, hpres, havoid, hsmooth, T, j, hj, hjc, hT, hTs, hTp, hTD, t, htx⟩

end MixedFujita
