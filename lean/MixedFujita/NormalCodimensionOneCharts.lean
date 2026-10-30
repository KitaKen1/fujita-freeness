/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.NormalBirationalPrimeLifts
public import MixedFujita.EtaleChartDimension
public import MixedFujita.SmoothStalkNormality
public import MixedFujita.KltPairs
public import Hironaka.Algebra.RegularSmooth.RegularSmoothEquiv

/-!
Normality supplies the actual codimension-one charts required by the geometric F2 interfaces.
On a locally noetherian integral scheme a normal codimension-one stalk is a DVR, hence regular.
Over a perfect field the existing Hironaka regular/smooth comparison puts this point in the
actual smooth locus. The existing chart construction and dimension comparison then give a
chart with exactly dim X coordinates containing the original point, not a replacement closed
point. Conversely an actual etale chart supplies a normal stalk. Thus the current chart-cover
predicate is precisely normality in codimension one (R1) in this geometric setting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- A normal codimension-one stalk is regular, via the existing actual DVR construction. -/
theorem normal_codimensionOne_stalk_regular {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (x : CodimensionOnePoint X)
    [IsIntegrallyClosed (X.presheaf.stalk (x : X))] :
    IsRegularLocalRing (X.presheaf.stalk (x : X)) := by
  have := normal_codimensionOne_stalk_DVR x
  infer_instance

variable {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- Every actual regular point has a chart with the exact geometric dimension of X. -/
theorem regularPoint_exists_etaleChart_dim {n : ℕ} (hdim : topologicalKrullDim X = n)
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)] :
    ∃ c : EtaleChart K X n, x ∈ c.U := by
  have hxreg : X.IsRegularAt x := (inferInstance : IsRegularLocalRing (X.presheaf.stalk x))
  have hx : x ∈ (X ↘ Spec (CommRingCat.of K)).smoothLocus :=
    (Scheme.mem_smoothLocus_iff_isRegularAt (X ↘ Spec (CommRingCat.of K)) x).mpr hxreg
  obtain ⟨m, c, hc⟩ := exists_etaleChart_of_mem_smoothLocus (K := K) hx
  have hmn : m = n := by exact_mod_cast (etaleChart_topologicalKrullDim c).symm.trans hdim
  subst m
  exact ⟨c, hc⟩

/-- The original normal prime, including a nonclosed point, lies in the constructed chart. -/
theorem normal_codimensionOne_exists_etaleChart_dim {n : ℕ}
    (hdim : topologicalKrullDim X = n) (x : CodimensionOnePoint X)
    [IsIntegrallyClosed (X.presheaf.stalk (x : X))] :
    ∃ c : EtaleChart K X n, (x : X) ∈ c.U := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of K))
  have := normal_codimensionOne_stalk_regular x
  exact regularPoint_exists_etaleChart_dim hdim (x : X)

/-- The current codimension-one chart predicate is exactly normality at those stalks. -/
theorem codimOneChartCovered_iff_normal_codimensionOne {n : ℕ}
    (hdim : topologicalKrullDim X = n) :
    CodimOneChartCovered n K X ↔
      ∀ x : X, Order.coheight x = 1 → IsIntegrallyClosed (X.presheaf.stalk x) := by
  constructor
  · intro h x hx
    obtain ⟨c, hc⟩ := h x hx
    exact etaleChart_stalk_isIntegrallyClosed c x hc
  · intro h x hx
    have := h x hx
    exact normal_codimensionOne_exists_etaleChart_dim (K := K) hdim ⟨x, hx⟩

/-- Ordinary normality internally supplies all codimension-one charts over a perfect field. -/
theorem normal_codimOneChartCovered {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) :
    CodimOneChartCovered n K X :=
  (codimOneChartCovered_iff_normal_codimensionOne hdim).mpr (fun x _ => hnorm x)

end MixedFujita
