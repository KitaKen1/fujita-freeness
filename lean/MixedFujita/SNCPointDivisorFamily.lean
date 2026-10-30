/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.EtaleChartStalkParameterExtension
public import MixedFujita.SNCStrataGenericSmoothness
public import Hironaka.Scheme.IdealSheaf.StalkIdeal

/-!
Turn the actual pointwise etale-chart SNC boundary used by the original pair
into the actual finite family of reduced closed component ideals. At every
point, including nonclosed points, coordinate germs give the regular parameters
required by Hironaka's divisor-family definition. No comparison certificate is input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- The actual reduced closed components attached to a finite family of points. -/
@[reducible]
noncomputable def sncDivisorFamilyOfPoints {X : Scheme.{u}} {r : ℕ} (ξ : Fin r → X) :
    Scheme.DivisorFamily X where
  ι := ULift.{u} (Fin r)
  component i := Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ξ i.down} : Set X), isClosed_closure⟩ : Closeds X)

variable {K : Type u} [Field K] {n r : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]

/-- The actual closed component ideal has precisely the chart coordinate as its stalk generator. -/
theorem sncDivisorFamilyOfPoints_stalk_on_chart
    (c : EtaleChart K X n) (ξ : Fin r → X) (σ : Fin r → Option (Fin n))
    (hc : IsSNCChart c ξ σ) (x : X) (hx : x ∈ c.U) (i : Fin r) :
    ((sncDivisorFamilyOfPoints ξ).component (ULift.up i)).stalkIdeal x =
      Ideal.span (Set.singleton (X.presheaf.germ c.U x hx
        ((σ i).elim (1 : Γ(X, c.U)) (fun a => c.coords (MvPolynomial.X a))))) := by
  change (Scheme.IdealSheafData.vanishingIdeal
    (⟨closure ({ξ i} : Set X), isClosed_closure⟩ : Closeds X)).stalkIdeal x = _
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ _ ⟨c.U, c.isAffine⟩ hx,
    vanishingIdeal_closure_ideal_sncChart c ξ σ hc i, Ideal.map_span, Set.image_singleton]
  rfl

/-- The etale SNC family supplies actual stalkwise SNC parameters without a rational-point assumption. -/
theorem sncDivisorFamilyOfPoints_isSncAt
    (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ) (x : X) :
    ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x),
      (sncDivisorFamilyOfPoints ξ).IsSncAt x z := by
  classical
  obtain ⟨c, σ, hx, hc⟩ := hsnc x
  obtain ⟨m, z, hz, τ, hτ, hτz⟩ := etaleChart_exists_stalk_regular_parameters c x hx
  have hcoord (i : {i : ULift.{u} (Fin r) // x ∈ ((sncDivisorFamilyOfPoints ξ).component i).support}) :
      ∃ a : Fin n, σ i.1.down = some a ∧
        c.coords (MvPolynomial.X a) ∈ (c.isAffine.primeIdealOf ⟨x, hx⟩).asIdeal := by
    have hcl : x ∈ closure ({ξ i.1.down} : Set X) := by
      have h := i.2
      change x ∈ ((Scheme.IdealSheafData.vanishingIdeal
        (⟨closure ({ξ i.1.down} : Set X), isClosed_closure⟩ : Closeds X)).support : Set X) at h
      rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
    cases hi : σ i.1.down with
    | none =>
      have hset := hc.2 i.1.down
      rw [hi, Option.elim_none] at hset
      have hempty : x ∈ (∅ : Set X) := hset ▸ ⟨hcl, hx⟩
      exact hempty.elim
    | some a =>
      refine ⟨a, rfl, ?_⟩
      rw [c.isAffine.primeIdealOf_eq_map_closedPoint ⟨x, hx⟩]
      change X.presheaf.germ c.U x hx (c.coords (MvPolynomial.X a)) ∈ maximalIdeal _
      apply (Scheme.IdealSheafData.mem_support_iff_stalkIdeal_le_maximalIdeal _ x).mp i.2
      rw [sncDivisorFamilyOfPoints_stalk_on_chart c ξ σ hc x hx i.1.down, hi, Option.elim_some]
      exact Ideal.subset_span (Set.mem_singleton _)
  choose a ha hmem using hcoord
  refine ⟨m, z, hz, fun i => τ ⟨a i, hmem i⟩, ?_, ?_⟩
  · intro i j hij
    have hab : a i = a j := congrArg Subtype.val (hτ hij)
    apply Subtype.ext
    apply ULift.ext
    exact hc.1 i.1.down j.1.down (a i) (ha i) (by simpa only [hab] using ha j)
  · intro i
    rw [sncDivisorFamilyOfPoints_stalk_on_chart c ξ σ hc x hx i.1.down,
      ha i, Option.elim_some, ← hτz ⟨a i, hmem i⟩]
    rfl

/-- The actual reduced closed-component family is SNC in Hironaka's sense. -/
theorem sncDivisorFamilyOfPoints_isSnc [Smooth (X ↘ Spec (CommRingCat.of K))]
    (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ) : (sncDivisorFamilyOfPoints ξ).IsSnc := by
  refine ⟨?_, sncDivisorFamilyOfPoints_isSncAt ξ hsnc⟩
  intro i
  apply isRegular_subscheme_of_isRegularLocalRing_quotient ((sncDivisorFamilyOfPoints ξ).component i)
  intro x hx
  letI := isRegularLocalRing_stalk (X ↘ Spec (CommRingCat.of K)) x
  obtain ⟨m, z, hz, c, hcinj, hc⟩ := sncDivisorFamilyOfPoints_isSncAt ξ hsnc x
  exact isRegularLocalRing_quotient_stalkIdeal_of_eq_span
    (s := {c ⟨i, hx⟩}) hz (by simpa only [Finset.coe_singleton, Set.image_singleton] using hc ⟨i, hx⟩)

/-- A pointwise SNC family has an internally constructed common smooth-strata base open. -/
theorem proper_snc_point_family_exists_common_smooth_base_open
    [CharZero K] [Smooth (X ↘ Spec (CommRingCat.of K))]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [Y.Over (Spec (CommRingCat.of K))]
    (g : X ⟶ Y) [IsProper g] (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ) :
    ∃ V : Y.Opens, genericPoint Y ∈ V ∧ ∀ s : Finset (ULift.{u} (Fin r)),
      Smooth (((sncStratumIdeal (sncDivisorFamilyOfPoints ξ) s).subschemeι ≫ g) ∣_ V) := by
  exact proper_snc_strata_exists_common_smooth_base_open K g
    (sncDivisorFamilyOfPoints ξ) (sncDivisorFamilyOfPoints_isSnc ξ hsnc)

end MixedFujita
