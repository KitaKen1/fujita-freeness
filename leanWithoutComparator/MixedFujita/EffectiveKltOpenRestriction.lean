/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.BirationalBoundaryEffectivity

/-!
Actual open restriction preserves codimension-one charts and effectivity of
the crepant boundary, with the pulled rational top form. Together with the
nonproper test comparison, construct a reference chart for an actual restricted
effective klt pair without an additional chart or restriction certificate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {K : Type u} [Field K] {n : ℕ} {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]

include j

/-- The original codimension-one chart condition restricts to the actual open scheme. -/
theorem codimOneChartCovered_open_immersion (hcov : CodimOneChartCovered n K X) :
    CodimOneChartCovered n K Z := by
  intro z hz
  have hb : Function.Bijective (j.stalkMap z) := ConcreteCategory.bijective_of_isIso _
  have hx : Order.coheight (j z) = 1 := (coheight_eq_of_stalkMap_bijective j z hb).symm.trans hz
  obtain ⟨c, hc⟩ := hcov (j z) hx
  exact exists_etaleChart_mem_on_open_immersion j z c hc

/-- Effectivity of the original boundary is preserved with the actual pulled form. -/
theorem logPairBoundaryEffective_open_crepant_pullback
    (hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j))
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (heff : LogPairBoundaryEffective c f d D) (cZ : EtaleChart K Z n) :
    LogPairBoundaryEffective cZ (crepantPullbackFormUnit j hj c f cZ) d
      (cartierPullback j D) := by
  intro c' z hz hcoh
  let t : CodimensionOnePoint Z := ⟨z, hcoh⟩
  have hb : Function.Bijective (j.stalkMap z) := ConcreteCategory.bijective_of_isIso _
  have hx : Order.coheight (j z) = 1 :=
    (coheight_eq_of_stalkMap_bijective j z hb).symm.trans hcoh
  letI := hnorm (j z)
  letI := normal_codimensionOne_stalk_DVR (⟨j z, hx⟩ : CodimensionOnePoint X)
  letI : IsDiscreteValuationRing (Z.presheaf.stalk z) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective (j.stalkMap z).hom hb)
  obtain ⟨cX, hcX⟩ := hcov (j z) hx
  rw [crepantPullbackFormUnit_order_of_stalkMap_bijective j hj c f cZ t hx hb cX hcX _ hz,
    cartierCoefficient_pullback_of_stalkMap_bijective j t hx hb D]
  exact heff cX (j z) hcX hx

/-- Construct the actual reference chart and both conditions for the restricted effective klt pair. -/
theorem exists_effective_klt_crepant_open_pullback [CharZero K]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
    [IsSeparated (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective c f d D)
    (hklt : LogPairIsKlt c f d D) :
    ∃ cZ : EtaleChart K Z n,
      LogPairBoundaryEffective cZ (crepantPullbackFormUnit j
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion j) c f cZ) d (cartierPullback j D) ∧
      LogPairIsKlt cZ (crepantPullbackFormUnit j
        (dominantFunctionFieldMap_bijective_of_isOpenImmersion j) c f cZ) d (cartierPullback j D) := by
  obtain ⟨cZ⟩ := exists_etaleChart_on_integral_open_immersion j c
  have hj : Function.Bijective (dominantFunctionFieldAlgHom (K := K) j) :=
    dominantFunctionFieldMap_bijective_of_isOpenImmersion j
  exact ⟨cZ, logPairBoundaryEffective_open_crepant_pullback j hj hnorm hcov c f d D heff cZ,
    logPairIsKlt_crepant_pullback_without_properness j hj c f d hd D hklt cZ⟩

end MixedFujita
