/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalDivisor
public import MixedFujita.VeryGeneralClosedPoint
public import MixedFujita.SmoothSchemeCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
Smooth closed points with étale charts on singular varieties (step 4). Over a perfect field the
smooth locus of a reduced scheme locally of finite type is a dense open subset (generic
smoothness), and on a Jacobson scheme every nonempty locally closed subset contains a closed point.
Hence every nonempty open subset contains a closed point at which the scheme is smooth, and over an
uncountable algebraically closed field such a point can be taken outside countably many proper
closed subsets: a very general smooth point. At a smooth point there is an étale chart: the
sections over an affine neighbourhood are smooth over K, standard smooth on a smaller basic open,
and a standard smooth algebra is étale over a polynomial ring. On an integral scheme every chart
gives a basis of Ω[K(W)/K], so all charts have the same number of coordinates.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {W : Scheme.{u}} [W.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseOpenAlgebra

/-- Generic smoothness: a nonempty open subset of a reduced scheme locally of finite type over a
perfect field contains a closed point of the smooth locus. -/
theorem exists_closedPoint_mem_open_smoothLocus [PerfectField K] [IsReduced W] (O : Set W)
    (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y : W, IsClosed {y} ∧ y ∈ O ∧ y ∈ (W ↘ Spec (CommRingCat.of K)).smoothLocus := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (W ↘ Spec (CommRingCat.of K))
  have hd := (W ↘ Spec (CommRingCat.of K)).dense_smoothLocus_of_perfectField
  obtain ⟨y, ⟨hyO, hys⟩, hyc⟩ := nonempty_inter_closedPoints (hd.inter_open_nonempty O hO hne)
    (hO.inter (W ↘ Spec (CommRingCat.of K)).smoothLocus.2).isLocallyClosed
  exact ⟨y, mem_closedPoints_iff.mp hyc, hyO, hys⟩

include K in
/-- A very general smooth closed point: in a nonempty open subset of an integral scheme of finite
type over an uncountable algebraically closed field, outside countably many proper closed
subsets. -/
theorem exists_smooth_closedPoint_mem_open_notMem_of_countable [IsAlgClosed K] [Uncountable K]
    [IsIntegral W] {ι : Type*} [Countable ι] (O : Set W) (hO : IsOpen O) (hne : O.Nonempty)
    (Z : ι → Set W) (hZ : ∀ k, IsClosed (Z k)) (hZne : ∀ k, Z k ≠ Set.univ) :
    ∃ y : W, IsClosed {y} ∧ y ∈ O ∧ y ∈ (W ↘ Spec (CommRingCat.of K)).smoothLocus ∧
      ∀ k, y ∉ Z k := by
  have hd := (W ↘ Spec (CommRingCat.of K)).dense_smoothLocus_of_perfectField
  obtain ⟨y, hyc, ⟨hyO, hys⟩, hyZ⟩ := exists_closedPoint_mem_open_notMem_of_countable (K := K)
    (O ∩ ((W ↘ Spec (CommRingCat.of K)).smoothLocus : Set W))
    (hO.inter (W ↘ Spec (CommRingCat.of K)).smoothLocus.2) (hd.inter_open_nonempty O hO hne)
    Z hZ hZne
  exact ⟨y, hyc, hyO, hys, hyZ⟩

/-- At a point of the smooth locus there is an étale chart. -/
theorem exists_etaleChart_of_mem_smoothLocus {y : W}
    (hy : y ∈ (W ↘ Spec (CommRingCat.of K)).smoothLocus) :
    ∃ (m : ℕ) (c : EtaleChart K W m), y ∈ c.U := by
  obtain ⟨U, -, V, hV, hVU, hyV, hs⟩ :=
    exists_smooth_of_formallySmooth_stalk (W ↘ Spec (CommRingCat.of K)) y hy
  have hUtop : U = ⊤ := by
    apply top_unique
    intro z _
    have hz : z = (W ↘ Spec (CommRingCat.of K)) y := Subsingleton.elim _ _
    rw [hz]
    exact hVU hyV
  subst hUtop
  -- the sections over V are smooth over K
  have hsm : Algebra.Smooth K Γ(W, V) := by
    apply RingHom.smooth_algebraMap.mp
    change (((W.baseRingToStructurePresheaf K).app (op V)).hom).Smooth
    rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE]
    exact RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)) hs
  -- standard smooth on a basic open around y
  obtain ⟨f, hfy, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  have hyD : y ∈ W.basicOpen f := by
    rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hfy
  have htower : IsScalarTower K Γ(W, V) Γ(W, W.basicOpen f) := by
    apply IsScalarTower.of_algebraMap_eq
    intro k
    change ((W.baseRingToStructurePresheaf K).app (op (W.basicOpen f))).hom k =
      (W.presheaf.map (homOfLE (W.basicOpen_le f) : W.basicOpen f ⟶ V).op).hom
        (((W.baseRingToStructurePresheaf K).app (op V)).hom k)
    rw [← CommRingCat.comp_apply, ← (W.baseRingToStructurePresheaf K).naturality]
    rfl
  have := hV.isLocalization_basicOpen f
  let e : Localization.Away f ≃ₐ[K] Γ(W, W.basicOpen f) :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
      Γ(W, W.basicOpen f)).restrictScalars K
  have : Algebra.IsStandardSmooth K Γ(W, W.basicOpen f) := Algebra.IsStandardSmooth.of_algEquiv e
  -- étale coordinates
  obtain ⟨m, g, hgK, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    ((RingHom.isStandardSmooth_algebraMap).mpr inferInstance :
      (algebraMap K Γ(W, W.basicOpen f)).IsStandardSmooth)
  let g' : MvPolynomial (Fin m) K →ₐ[K] Γ(W, W.basicOpen f) :=
    { g with commutes' := fun k => congrArg (fun φ : K →+* Γ(W, W.basicOpen f) => φ k) hgK }
  have hfe : g'.toRingHom.FormallyEtale := by
    let _ := g.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin m) K) Γ(W, W.basicOpen f) := hg
    exact Algebra.Etale.formallyEtale
  exact ⟨m, ⟨W.basicOpen f, hV.basicOpen f, ⟨⟨y, hyD⟩⟩, g', hfe⟩, hyD⟩

/-- A nonempty open subset of a reduced scheme locally of finite type over a perfect field contains
a closed point with an étale chart. -/
theorem exists_closedPoint_etaleChart [PerfectField K] [IsReduced W] (O : Set W) (hO : IsOpen O)
    (hne : O.Nonempty) :
    ∃ y : W, IsClosed {y} ∧ y ∈ O ∧ ∃ (m : ℕ) (c : EtaleChart K W m), y ∈ c.U := by
  obtain ⟨y, hyc, hyO, hys⟩ := exists_closedPoint_mem_open_smoothLocus (K := K) O hO hne
  exact ⟨y, hyc, hyO, exists_etaleChart_of_mem_smoothLocus hys⟩

section Integral

attribute [local instance] functionFieldBaseAlgebra

variable [IsIntegral W]

omit [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))] in
/-- The number of coordinates of an étale chart is the rank of Ω[K(W)/K]. -/
theorem etaleChart_dim_eq_finrank {m : ℕ} (c : EtaleChart K W m) :
    m = Module.finrank W.functionField Ω[W.functionField⁄K] := by
  rw [Module.finrank_eq_card_basis (etaleChartBasis c), Fintype.card_fin]

omit [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))] in
/-- All étale charts of an integral scheme have the same number of coordinates. -/
theorem etaleChart_dim_eq {m m' : ℕ} (c : EtaleChart K W m) (c' : EtaleChart K W m') : m = m' :=
  (etaleChart_dim_eq_finrank c).trans (etaleChart_dim_eq_finrank c').symm

end Integral

end MixedFujita
