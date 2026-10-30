/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProjectivePointedFirstOrder

/-!
The actual second-order bad forms are a proper subspace inside the forms
through the prescribed point. Finite subspace avoidance simultaneously
preserves first order and avoids a finite set. The resulting actual effective
Cartier cut is nonsingular to first order at the prescribed point; global
smoothness and integrality of its scheme are not asserted.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n K)

noncomputable def projectivePullbackHomogeneousStalkMap (k : Fin n)
    (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k) :
    MvPolynomial (Fin n) K →+* Y.presheaf.stalk x :=
  (Y.presheaf.germ _ x hxk).hom.comp
    ((projectivePullbackAffinePolynomialMap e k).comp (projectiveDehomogenize K k))

theorem projectivePullbackHomogeneousStalkMap_apply (k : Fin n)
    (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k) (d : ℕ)
    (f : MvPolynomial (Fin n) K) (hf : f.IsHomogeneous d) :
    projectivePullbackHomogeneousStalkMap e k x hxk f =
      Y.presheaf.germ _ x hxk (projectivePullbackHomogeneousEquation e k d f hf) := by
  change Y.presheaf.germ _ x hxk
    (projectivePullbackAffinePolynomialMap e k (projectiveDehomogenize K k f)) = _
  rw [projectivePullbackAffinePolynomialMap_dehomogenize e k d f hf]

variable [IsAlgClosed K] [IsClosedImmersion e] [IsIntegral Y]

theorem polynomialProjective_pointed_order_one_finite_avoidance
    (k : Fin n) (x : Y) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
    (hx : IsClosed {x})
    (f0 : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
    (h0 : localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
      (projectivePullbackHomogeneousEquation e k 1 f0.val f0.property)) = 1)
    (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K 1,
      f.val ∈ (e x).asHomogeneousIdeal ∧
        f.val ∉ (e (genericPoint Y)).asHomogeneousIdeal ∧
        (∀ y ∈ Z, f.val ∉ (e y).asHomogeneousIdeal) ∧
        localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
          (projectivePullbackHomogeneousEquation e k 1 f.val f.property)) = 1 := by
  let := hZ.to_subtype
  let p := polynomialProjectiveVanishingForms 1 (e x)
  let I := (IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ 2).comap
    (projectivePullbackHomogeneousStalkMap e k x hxk)
  let bad : Submodule K p := (I.restrictScalars K).comap
    ((MvPolynomial.homogeneousSubmodule (Fin n) K 1).subtype.comp p.subtype)
  let q : Option Z → Submodule K p := fun i ↦ match i with
    | none => bad
    | some y => (polynomialProjectiveVanishingForms 1 (e y.val)).comap p.subtype
  have hproper : ∀ i, q i ≠ ⊤ := by
    intro i
    cases i with
    | none =>
      let f0' : p := ⟨f0, (projectivePullback_order_one_mem_point e k f0 x hxk h0).1⟩
      intro h
      have hm : f0' ∈ q none := h.symm ▸ Submodule.mem_top
      change projectivePullbackHomogeneousStalkMap e k x hxk f0.val ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ 2 at hm
      rw [projectivePullbackHomogeneousStalkMap_apply e k x hxk 1 f0.val f0.property] at hm
      exact ((localAdicOrder_eq_nat_iff _ 1).mp h0).2 hm
    | some y =>
      have hex : IsClosed {e x} := by
        simpa only [Set.image_singleton] using e.isClosedEmbedding.isClosedMap {x} hx
      have hne : e y.val ≠ e x := fun h ↦ hxZ ((e.isClosedEmbedding.injective h) ▸ y.property)
      obtain ⟨g, hgx, hgy⟩ :=
        polynomialProjective_closedPoint_linearForm_separates_of_isAlgClosed (e x) hex (e y.val) hne
      let g' : p := ⟨g, hgx⟩
      intro h
      have hm : g' ∈ q (some y) := h.symm ▸ Submodule.mem_top
      exact hgy hm
  obtain ⟨f, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (ι := Option Z) (K := K) (M := p) q hproper
  have hnot : Y.presheaf.germ _ x hxk
      (projectivePullbackHomogeneousEquation e k 1 f.val.val f.val.property) ∉
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ 2 := by
    have h := hf none
    change projectivePullbackHomogeneousStalkMap e k x hxk f.val.val ∉
      IsLocalRing.maximalIdeal (Y.presheaf.stalk x) ^ 2 at h
    rwa [projectivePullbackHomogeneousStalkMap_apply e k x hxk 1 f.val.val f.val.property] at h
  have hm : Y.presheaf.germ _ x hxk
      (projectivePullbackHomogeneousEquation e k 1 f.val.val f.val.property) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    intro hu
    have hb := (Y.mem_basicOpen _ x hxk).mpr hu
    rw [projectivePullbackHomogeneousEquation_basicOpen e k 1 f.val.val f.val.property
      Nat.zero_lt_one] at hb
    exact hb.2 f.property
  have ho : localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
      (projectivePullbackHomogeneousEquation e k 1 f.val.val f.val.property)) = 1 :=
    (localAdicOrder_eq_nat_iff _ 1).mpr ⟨by simpa only [pow_one] using hm, hnot⟩
  exact ⟨f.val, f.property, (projectivePullback_order_one_mem_point e k f.val x hxk ho).2,
    fun y hy ↦ hf (some ⟨y, hy⟩), ho⟩

variable [Y.Over (Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem polynomialProjective_smooth_positive_dimension_pointed_order_one_finite_avoidance
    (hdim : 0 < topologicalKrullDim Y) (x : Y) (hx : IsClosed {x})
    (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (k : Fin n) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
      (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1),
      f.val ∈ (e x).asHomogeneousIdeal ∧
        f.val ∉ (e (genericPoint Y)).asHomogeneousIdeal ∧
        (∀ y ∈ Z, f.val ∉ (e y).asHomogeneousIdeal) ∧
        localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
          (projectivePullbackHomogeneousEquation e k 1 f.val f.property)) = 1 := by
  obtain ⟨k, hk, f0, _, _, h0⟩ :=
    polynomialProjective_smooth_positive_dimension_exists_pointed_order_one_form e hdim x hx
  obtain ⟨f, hfx, hgeneric, havoid, horder⟩ :=
    polynomialProjective_pointed_order_one_finite_avoidance e k x hk hx f0 h0 Z hZ hxZ
  exact ⟨k, hk, f, hfx, hgeneric, havoid, horder⟩

theorem polynomialProjective_smooth_positive_dimension_pointed_order_one_effectiveCartierCut
    (hdim : 0 < topologicalKrullDim Y) (x : Y) (hx : IsClosed {x})
    (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ (k : Fin n) (hxk : x ∈ projectivePullbackCoordinateOpen e k)
      (f : MvPolynomial.homogeneousSubmodule (Fin n) K 1)
      (hgeneric : f.val ∉ (e (genericPoint Y)).asHomogeneousIdeal),
      let I := projectivePullbackCartierIdealSheaf e 1 f.val f.property Nat.zero_lt_one hgeneric
      Nonempty (InvertibleIdealPresentation I) ∧
        x ∈ Set.range I.subschemeι ∧ (∀ y ∈ Z, y ∉ Set.range I.subschemeι) ∧
        localAdicOrder (Y.presheaf.stalk x) (Y.presheaf.germ _ x hxk
          (projectivePullbackHomogeneousEquation e k 1 f.val f.property)) = 1 := by
  obtain ⟨k, hk, f, hfx, hgeneric, havoid, horder⟩ :=
    polynomialProjective_smooth_positive_dimension_pointed_order_one_finite_avoidance e hdim x hx Z hZ hxZ
  refine ⟨k, hk, f, hgeneric,
    ⟨projectivePullbackCartierIdealPresentation e 1 f.val f.property Nat.zero_lt_one hgeneric⟩,
    ?_, ?_, horder⟩
  · rw [Scheme.IdealSheafData.range_subschemeι]
    exact (projectivePullbackCartierIdealSheaf_mem_support_iff e 1 f.val f.property
      Nat.zero_lt_one hgeneric x).mpr hfx
  · intro y hy
    rw [Scheme.IdealSheafData.range_subschemeι]
    intro hs
    exact havoid y hy ((projectivePullbackCartierIdealSheaf_mem_support_iff e 1 f.val f.property
      Nat.zero_lt_one hgeneric y).mp hs)

end MixedFujita
