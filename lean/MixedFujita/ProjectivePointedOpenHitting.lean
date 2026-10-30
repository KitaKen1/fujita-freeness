/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointedProperComponent
public import MixedFujita.FiniteAvoidanceOpenHitting

/-! Combine actual pointed hyperplane cuts with the finite generic-point avoidance criterion. Both the original finite avoidance and the component image hitting the specified nonempty open are proved. -/
@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra
theorem polynomialProjective_pointed_proper_integral_smooth_component_hits_open
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
    [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]
    {n : ℕ} (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K))
    (d : ℕ) (hdim : topologicalKrullDim Y = d) (hd : 2 ≤ d)
    (x : Y) (hx : IsClosed {x}) (U : Y.Opens) (hU : Nonempty U)
    (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
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
          (∃ t : T, (j ≫ I.subschemeι) t = x) ∧
          ∃ t : T, (j ≫ I.subschemeι) t ∈ U := by
  have := polynomialProjective_closedImmersion_isProper_over_field e he
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (CommRingCat.of K))
  have : CompactSpace Y := (quasiCompact_iff_compactSpace
    (Y ↘ Spec (CommRingCat.of K))).mp inferInstance
  have : IsNoetherian Y := {}
  obtain ⟨B, hB, hxB, hhit⟩ := exists_finite_avoidance_for_positive_dimensional_hypersurfaces
    d hdim hd x hx U hU
  have hxZB : x ∉ Z ∪ B := by simpa only [Set.mem_union, not_or] using And.intro hxZ hxB
  obtain ⟨F, hgeneric, hpres, havoid, hsmooth, T, j, hj, hjc, hT, hTs, hTp, hdimT, htx⟩ :=
    polynomialProjective_pointed_proper_integral_smooth_component e he d hdim
      (by omega) x hx (Z ∪ B) (hZ.union hB) hxZB
  let I := projectivePullbackCartierIdealSheaf e 1 F.val F.property Nat.zero_lt_one hgeneric
  let := hjc
  have hji : IsClosedImmersion (j ≫ I.subschemeι) := inferInstance
  have hBavoid : ∀ y ∈ B, y ∉ Set.range (j ≫ I.subschemeι) := by
    intro y hy
    rintro ⟨t, rfl⟩
    exact havoid _ (Or.inr hy) ⟨j t, rfl⟩
  exact ⟨F, hgeneric, hpres, fun y hy => havoid y (Or.inl hy), hsmooth,
    T, j, hj, hjc, hT, hTs, hTp, hdimT, htx,
    hhit T hT (j ≫ I.subschemeι) hji hdimT hBavoid⟩

end MixedFujita
