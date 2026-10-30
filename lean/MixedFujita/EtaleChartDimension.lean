/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.GenericSmoothCharts
public import MixedFujita.EtaleChartTaylorCoordinates
public import TauCeti.RingTheory.Smooth.KrullDimension
public import TauCeti.AlgebraicGeometry.Scheme.KrullDimension

/-!
The number of coordinates of an étale chart is the dimension (step 4). If K[X_1, …, X_m] → S is
étale and S is of finite type over K, every maximal ideal of S has height m: étale maps are flat
and quasi-finite, so heights are preserved, a maximal ideal contracts to a maximal ideal of the
polynomial ring (Zariski's lemma), and these have height m. The stalk at a closed point of a chart
is the localization at a maximal ideal, so it has Krull dimension m, and on an irreducible scheme
locally of finite type over K this is the dimension of the scheme. Hence every étale chart of an
irreducible variety W has exactly dim W coordinates, and every nonempty open subset of an integral
variety over a perfect field contains a closed point with an étale chart of dim W coordinates,
also outside countably many proper closed subsets over an uncountable algebraically closed field:
smooth points with coordinates of a singular W.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false

namespace MixedFujita

section Algebra

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S] [Algebra.FiniteType K S] {m : ℕ}

/-- Every maximal ideal of an algebra of finite type étale over K[X_1, …, X_m] has height m. -/
theorem height_eq_of_etale_mvPolynomial (g : MvPolynomial (Fin m) K →ₐ[K] S) (hg : g.Etale)
    (q : Ideal S) [q.IsMaximal] : q.height = m := by
  let P := MvPolynomial (Fin m) K
  let _ := g.toRingHom.toAlgebra
  have : Algebra.Etale P S := hg
  have : IsScalarTower K P S := .of_algebraMap_eq fun r ↦ (g.commutes r).symm
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  have := q.isMaximal_under_of_finiteType K (A := P)
  rw [Ideal.height_eq_height_under_of_quasiFinite (R := P) q,
    MvPolynomial.height_eq_natCard_of_isMaximal (q.under P), Nat.card_fin]

end Algebra

section Scheme

universe u

variable {K : Type u} [Field K] {W : Scheme.{u}} [W.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K))]

attribute [local instance] cartierBaseOpenAlgebra

/-- The sections over an affine open are of finite type over K. -/
theorem sectionsBaseOpen_finiteType {U : W.Opens} (hU : IsAffineOpen U) :
    Algebra.FiniteType K Γ(W, U) := by
  apply RingHom.finiteType_algebraMap.mp
  change ((W.baseRingToStructurePresheaf K).app (op U)).hom.FiniteType
  rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, CommRingCat.hom_comp]
  have h1 : ((W ↘ Spec (CommRingCat.of K)).appLE ⊤ U le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType (W ↘ Spec (CommRingCat.of K)) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

/-- The stalk at a closed point of an étale chart has dimension the number of coordinates. -/
theorem etaleChart_ringKrullDim_stalk {m : ℕ} (c : EtaleChart K W m) (y : W) (hy : y ∈ c.U)
    (hyc : IsClosed {y}) : ringKrullDim (W.presheaf.stalk y) = m := by
  let _ := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨y, hy⟩ : c.U)
  have := c.isAffine.isLocalization_stalk (⟨y, hy⟩ : c.U)
  have : (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal :=
    c.isAffine.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩ hyc
  have := sectionsBaseOpen_finiteType (K := K) c.isAffine
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (c.isAffine.primeIdealOf ⟨y, hy⟩).asIdeal
    (W.presheaf.stalk y), height_eq_of_etale_mvPolynomial c.coords (etaleChart_coords_etale c)]
  rfl

/-- Every étale chart of an irreducible scheme locally of finite type over K has exactly dim W
coordinates. -/
theorem etaleChart_topologicalKrullDim [IrreducibleSpace W] {m : ℕ} (c : EtaleChart K W m) :
    topologicalKrullDim W = m := by
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (W ↘ Spec (CommRingCat.of K))
  obtain ⟨⟨y, hy⟩⟩ := c.nonempty
  obtain ⟨z, hzU, hzc⟩ := nonempty_inter_closedPoints ⟨y, hy⟩ c.U.isOpen.isLocallyClosed
  rw [← TauCeti.AlgebraicGeometry.ringKrullDim_stalk_eq_topologicalKrullDim_of_isClosed
    (W ↘ Spec (CommRingCat.of K)) (mem_closedPoints_iff.mp hzc)]
  exact etaleChart_ringKrullDim_stalk c z hzU (mem_closedPoints_iff.mp hzc)

/-- A nonempty open subset of an integral variety of dimension d over a perfect field contains a
closed point with an étale chart of d coordinates. -/
theorem exists_closedPoint_etaleChart_dim [PerfectField K] [IsIntegral W] {d : ℕ}
    (hd : topologicalKrullDim W = d) (O : Set W) (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ y : W, IsClosed {y} ∧ y ∈ O ∧ ∃ c : EtaleChart K W d, y ∈ c.U := by
  obtain ⟨y, hyc, hyO, m, c, hyU⟩ := exists_closedPoint_etaleChart (K := K) O hO hne
  have hm : ((m : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) :=
    (etaleChart_topologicalKrullDim c).symm.trans hd
  have hmd : m = d := by exact_mod_cast hm
  subst hmd
  exact ⟨y, hyc, hyO, c, hyU⟩

include K in
/-- A very general closed point with an étale chart of d = dim W coordinates: in a nonempty open
subset of an integral variety over an uncountable algebraically closed field, outside countably
many proper closed subsets. -/
theorem exists_veryGeneral_closedPoint_etaleChart_dim [IsAlgClosed K] [Uncountable K]
    [IsIntegral W] {d : ℕ} (hd : topologicalKrullDim W = d) {ι : Type*} [Countable ι]
    (O : Set W) (hO : IsOpen O) (hne : O.Nonempty) (Z : ι → Set W) (hZ : ∀ k, IsClosed (Z k))
    (hZne : ∀ k, Z k ≠ Set.univ) :
    ∃ y : W, IsClosed {y} ∧ y ∈ O ∧ (∀ k, y ∉ Z k) ∧ ∃ c : EtaleChart K W d, y ∈ c.U := by
  obtain ⟨y, hyc, hyO, hys, hyZ⟩ :=
    exists_smooth_closedPoint_mem_open_notMem_of_countable (K := K) O hO hne Z hZ hZne
  obtain ⟨m, c, hyU⟩ := exists_etaleChart_of_mem_smoothLocus (K := K) hys
  have hm : ((m : ℕ∞) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞) :=
    (etaleChart_topologicalKrullDim c).symm.trans hd
  have hmd : m = d := by exact_mod_cast hm
  subst hmd
  exact ⟨y, hyc, hyO, hyZ, c, hyU⟩

end Scheme

end MixedFujita
