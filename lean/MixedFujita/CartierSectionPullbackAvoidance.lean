/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CrepantBertiniPerturbationDescent

/-!
Nonvanishing of actual pulled Cartier sections is detected by the source stalk.
Consequently their zero loci are actual inverse images and their pulled zero
divisors have zero prime coefficient over every avoided source point. This also
preserves actual discrepancy coefficients there. Proper dominance supplies
finite representatives of any finite set of source points.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X T : Scheme.{u}} [IsIntegral X] [IsIntegral T]
  (ρ : T ⟶ X) [IsDominant ρ]

/-- Nonvanishing of the actual pulled section is equivalent to nonvanishing at the image. -/
theorem cartierDominantPullbackSection_nonvanishing_iff (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) (t : T) :
    t ∈ cartierSectionNonvanishingOpen (cartierPullback ρ D)
      (cartierDominantPullbackSection ρ D s) ↔
        ρ t ∈ cartierSectionNonvanishingOpen D s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (ρ t)
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ t
      (Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom f)
      (cartierPullback_isLocalEquationAt ρ D t hf),
    mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (ρ t) f hf,
    cartierDominantPullbackSection_localCoefficient ρ D s t f hf]
  exact isUnit_map_iff (ρ.stalkMap t).hom _

/-- The actual zero locus of the pulled section is the inverse image of its source zero locus. -/
theorem cartierDominantPullbackSection_zeroLocus (D : CartierDivisor X)
    (s : Γ(D.sheaf, ⊤)) :
    cartierSectionZeroLocus (cartierPullback ρ D) (cartierDominantPullbackSection ρ D s) =
      ρ ⁻¹' cartierSectionZeroLocus D s := by
  ext t
  exact not_congr (cartierDominantPullbackSection_nonvanishing_iff ρ D s t)

variable [IsLocallyNoetherian T]

/-- Every actual test prime above an avoided point has zero pulled zero-divisor coefficient. -/
theorem cartierPullback_sectionZeroDivisor_coefficient_zero_of_avoided
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (hs : s ≠ 0)
    (t : CodimensionOnePoint T) (ht : ρ (t : T) ∉ cartierSectionZeroLocus D s) :
    cartierCoefficient (cartierPullback ρ (cartierSectionZeroDivisor D s hs)) (t : T) = 0 := by
  rw [← cartierDominantPullbackSection_zeroDivisor ρ D s hs]
  apply cartierSectionZeroDivisor_coefficient_zero_of_notMem
  rwa [cartierDominantPullbackSection_zeroLocus]

omit [IsLocallyNoetherian T] in
/-- Finite source points have finite actual representatives under a proper dominant map. -/
theorem proper_dominant_exists_finite_point_lifts [IsProper ρ]
    (Z : Set X) (hZ : Z.Finite) :
    ∃ W : Set T, W.Finite ∧ ∀ x ∈ Z, ∃ t ∈ W, ρ t = x := by
  classical
  letI : Fintype Z := hZ.fintype
  choose a ha using fun x : Z => surjective_of_isProper_of_isDominant ρ (x : X)
  exact ⟨Set.range a, Set.finite_range a, fun x hx =>
    ⟨a ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ha ⟨x, hx⟩⟩⟩

variable {K : Type u} [Field K] {n : ℕ}
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [ρ.IsOver (Spec (CommRingCat.of K))]
  (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))

omit [IsLocallyNoetherian T] in
/-- Actual discrepancy changes by the negative of the pulled added source Cartier divisor. -/
theorem logDiscrepancyDivisor_add_source (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (d : ℕ) (D E : CartierDivisor X) (cT : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤) :
    logDiscrepancyDivisor n ρ hρ c f d (D + E) cT hT =
      logDiscrepancyDivisor n ρ hρ c f d D cT hT - cartierPullback ρ E := by
  unfold logDiscrepancyDivisor
  rw [cartierPullback_add]
  abel

/-- At every prime centered at an avoided point, the actual discrepancy coefficient is unchanged. -/
theorem logDiscrepancyDivisor_section_perturbation_coefficient_eq_of_avoided
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d k : ℕ) (D H : CartierDivisor X)
    (s : Γ(H.sheaf, ⊤)) (hs : s ≠ 0) (cT : EtaleChart K T n)
    (hT : iSup (fun e : EtaleChart K T n => e.U) = ⊤)
    (t : CodimensionOnePoint T) (ht : ρ (t : T) ∉ cartierSectionZeroLocus H s) :
    cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d
      (D + k • cartierSectionZeroDivisor H s hs) cT hT) (t : T) =
        cartierCoefficient (logDiscrepancyDivisor n ρ hρ c f d D cT hT) (t : T) := by
  rw [logDiscrepancyDivisor_add_source, cartierPullback_nsmul,
    cartierCoefficient_sub, cartierCoefficient_nsmul,
    cartierPullback_sectionZeroDivisor_coefficient_zero_of_avoided ρ H s hs t ht,
    mul_zero, sub_zero]

end MixedFujita
