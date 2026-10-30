/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence

/-!
Klt descends along an actual proper birational crepant morphism. Resolve the
intermediate pair, compare its discrepancy with that over the original scheme,
and use the actual SNC-model criterion. Neither smoothness of the intermediate
scheme nor a common resolution supplied by the caller is required.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Tower

variable {K : Type u} [Field K] {n : ℕ} {Y X T : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X] [IsIntegral T]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [T.Over (Spec (CommRingCat.of K))]
  (f : X ⟶ Y) (π : T ⟶ X) [IsDominant f] [IsDominant π]
  [f.IsOver (Spec (CommRingCat.of K))] [π.IsOver (Spec (CommRingCat.of K))]
  (hf : Function.Bijective (dominantFunctionFieldAlgHom (K := K) f))
  (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))

/-- Crepant boundaries on a smooth final model agree in a birational tower,
even when the intermediate scheme is singular. -/
theorem crepantBoundaryCartier_comp (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D : CartierDivisor Y) (cX : EtaleChart K X n) (cT : EtaleChart K T n)
    (hT : iSup (fun c : EtaleChart K T n => c.U) = ⊤) :
    crepantBoundaryCartier (π ≫ f)
      (dominantFunctionFieldAlgHom_comp_bijective f π hf hπ) cY fY d D cT hT =
    crepantBoundaryCartier π hπ cX (crepantPullbackFormUnit f hf cY fY cX) d
      (cartierPullback f D) cT hT := by
  rw [crepantBoundaryCartier_eq_neg_discrepancy,
    crepantBoundaryCartier_eq_neg_discrepancy,
    logDiscrepancyDivisor_comp f π hf hπ cY fY d D cX cT hT]

end Tower

section Descent

variable {K : Type u} [Field K] [CharZero K] {n : ℕ} {Y X : Scheme.{u}}
  [IsIntegral Y] [IsIntegral X]
  [Y.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))]
  [IsSeparated (X ↘ Spec (CommRingCat.of K))]
  (f : X ⟶ Y) [IsDominant f] [f.IsOver (Spec (CommRingCat.of K))] [IsProper f]
  (hf : Function.Bijective (dominantFunctionFieldAlgHom (K := K) f))

/-- All-model klt of the actual crepant pullback implies all-model klt downstairs.
The needed SNC model of the possibly singular source is constructed internally. -/
theorem logPairIsKlt_of_crepant_pullback (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (cX : EtaleChart K X n)
    (hklt : LogPairIsKlt cX (crepantPullbackFormUnit f hf cY fY cX) d
      (cartierPullback f D)) : LogPairIsKlt cY fY d D := by
  obtain ⟨T, hTi, hTo, hTN, hTs, π, hdom, hover, hprop, hπ, cT, r, ξ,
    hinj, hcoh, hsnc, hsupp⟩ :=
    exists_proper_snc_model cX (crepantPullbackFormUnit f hf cY fY cX) d
      (cartierPullback f D)
  letI := hTi
  letI := hTo
  letI := hTN
  letI := hTs
  letI := hdom
  letI := hover
  letI := hprop
  apply logPairIsKlt_of_crepant_snc_model (π ≫ f)
    (dominantFunctionFieldAlgHom_comp_bijective f π hf hπ) cY fY d hd D cT
    ξ hinj hcoh hsnc
  · simpa only [crepantBoundaryCartier_comp f π hf hπ cY fY d D cX cT] using hsupp
  · intro i
    rw [crepantBoundaryCartier_comp f π hf hπ cY fY d D cX cT]
    exact logPairIsKlt_crepantBoundary_coefficient_lt π hπ cX
      (crepantPullbackFormUnit f hf cY fY cX) d (cartierPullback f D) hklt cT
      ⟨ξ i, hcoh i⟩

/-- Klt is invariant under an actual proper birational crepant pullback. -/
theorem logPairIsKlt_crepant_pullback_iff (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d) (D : CartierDivisor Y)
    (cX : EtaleChart K X n) :
    LogPairIsKlt cX (crepantPullbackFormUnit f hf cY fY cX) d (cartierPullback f D) ↔
      LogPairIsKlt cY fY d D :=
  ⟨logPairIsKlt_of_crepant_pullback f hf cY fY d hd D cX,
    fun h => logPairIsKlt_crepant_pullback f hf cY fY d D h cX⟩

end Descent

end MixedFujita
