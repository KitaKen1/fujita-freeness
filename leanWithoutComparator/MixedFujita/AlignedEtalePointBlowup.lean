/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PrescribedEtalePointCoordinates
public import MixedFujita.PointBlowupMatchedStalkCoordinates
public import MixedFujita.PointBlowupGermRestriction
public import Hironaka.Scheme.BlowUp.InvertibleSheaf

/-! Actual formally etale coordinates on the point blow-up with exactly
the prescribed source parameters. The same coordinate map gives the
exceptional ideal and the strict-transform restriction for every germ.
Aligning the source parameters then gives the previously supplied
completion leading forms in these actual etale blow-up coordinates. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

/-- The actual stalk map at an identified source point, as a K-algebra map. -/
noncomputable def stalkMapAtEqAlgHom (ρ : Y ⟶ X) [ρ.IsOver (Spec (.of K))]
    (q : Y) (x : X) (hq : ρ q = x) : X.presheaf.stalk x →ₐ[K] Y.presheaf.stalk q := by
  subst x
  exact schemeStalkMapAlgHom (K := K) ρ q

theorem stalkMapAtEqAlgHom_toRingHom (ρ : Y ⟶ X) [ρ.IsOver (Spec (.of K))]
    (q : Y) (x : X) (hq : ρ q = x) :
    (stalkMapAtEqAlgHom (K := K) ρ q x hq).toRingHom = stalkMapAtEq ρ q x hq := by
  subst x
  rfl

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem prescribed_parameters_pointBlowup_etale_restriction
    (x : X) (hxc : IsClosed ({x} : Set X))
    (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
    (T : X.presheaf.stalk x →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder (X.presheaf.stalk x) r)
    (hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)))
    (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n (pointClosureIdeal x) x)
    (hE : ∀ i, X.presheaf.germ E.U.1 x E.mem (E.v i) = ψ (MvPolynomial.X i))
    (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x) :
    let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
      ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
    ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk q),
      τ.toRingHom.FormallyEtale ∧
      ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
        Ideal.span {τ (MvPolynomial.X k)} ∧
      τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
      (∀ g, stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (ψ g) =
        τ (polynomialPointBlowupMap k g)) ∧
      ∀ (r : X.presheaf.stalk x) (m : ℕ), (m : ℕ∞) ≤ (T r).order →
        ∃! z : (pointClosureIdeal x).blowUp.presheaf.stalk q,
          stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq r = τ (MvPolynomial.X k) ^ m * z ∧
          Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) z =
            pointBlowupExceptionalEvaluation τ.toRingHom k
              (projectiveDehomogenize K k (homogeneousTaylorForm m (T r))) := by
  let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
    ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
  let I := pointClosureIdeal x
  let : I.blowUpπ.IsOver (Spec (.of K)) := ⟨rfl⟩
  have hxZ : x ∈ I.support := by
    change x ∈ ((pointClosureIdeal x).support : Set X)
    rw [pointClosureIdeal_support_closedPoint x hxc]
    exact rfl
  obtain ⟨k, τ, hτ, _, hcoord⟩ := etalePointBlowup_matched_stalk_coordinates E hxZ q hq
  let β := stalkMapAtEqAlgHom (K := K) I.blowUpπ q x hq
  have hβhom : β.toRingHom = stalkMapAtEq I.blowUpπ q x hq :=
    stalkMapAtEqAlgHom_toRingHom I.blowUpπ q x hq
  have hβX (i : Fin n) : β (ψ (MvPolynomial.X i)) =
      if i = k then τ (MvPolynomial.X k) else τ (MvPolynomial.X i) * τ (MvPolynomial.X k) := by
    change β.toRingHom (ψ (MvPolynomial.X i)) = _
    rw [hβhom, ← hE i, stalkMapAtEq_germ]
    exact hcoord i
  have hcomp : β.comp ψ = τ.comp (polynomialPointBlowupMap k) := by
    ext i
    change β (ψ (MvPolynomial.X i)) = τ (polynomialPointBlowupMap k (MvPolynomial.X i))
    rw [hβX]
    by_cases hi : i = k
    · subst i
      rw [ite_eq_left rfl, polynomialPointBlowupMap_X_self]
    · rw [ite_eq_right hi, polynomialPointBlowupMap_X_other k i hi, map_mul]
  have hIβ : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map β.toRingHom =
      Ideal.span {τ (MvPolynomial.X k)} := by
    rw [hmax, Ideal.map_span, ← Set.range_comp]
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change β (ψ (MvPolynomial.X i)) ∈ _
      rw [hβX]
      split_ifs
      · exact Ideal.subset_span rfl
      · exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have hk : β (ψ (MvPolynomial.X k)) = τ (MvPolynomial.X k) := by rw [hβX, ite_eq_left rfl]
      rw [← hk]
      exact Ideal.subset_span ⟨k, rfl⟩
  rw [hβhom] at hIβ
  have hI : (I.comap I.blowUpπ).stalkIdeal q = Ideal.span {τ (MvPolynomial.X k)} := by
    rw [stalkMapAtEq_comap_stalkIdeal I I.blowUpπ q x hq, pointClosureIdeal_stalkIdeal_self]
    exact hIβ
  have hInv := Scheme.IdealSheafData.blowUp.isInvertible_comap_π I
  obtain ⟨a, ha, hgen⟩ := hInv.exists_mem_nonZeroDivisors_stalkIdeal_eq_span q
  have hreg : τ (MvPolynomial.X k) ∈ nonZeroDivisors _ :=
    mem_nonZeroDivisors_of_span_eq_span ha (hI.symm.trans hgen)
  have hpoly (g) : stalkMapAtEq I.blowUpπ q x hq (ψ g) = τ (polynomialPointBlowupMap k g) := by
    rw [← hβhom]
    exact congrArg (fun F : MvPolynomial (Fin n) K →ₐ[K] I.blowUp.presheaf.stalk q => F g) hcomp
  exact ⟨k, τ, hτ, hI, hreg, hpoly, fun r m hr =>
    leadingJet_unique_exceptional ψ T hX hord (stalkMapAtEq I.blowUpπ q x hq) τ.toRingHom
      k hIβ hpoly hreg r m hr⟩

set_option maxHeartbeats 1000000 in
theorem suppliedCompletion_pointBlowup_exists_etale_restriction [PerfectField K]
    [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (hxc : IsClosed ({x} : Set X))
    (α : X.presheaf.stalk x →ₐ[K] K)
    (e : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K) :
    ∃ (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
      (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n (pointClosureIdeal x) x),
      (∀ i, X.presheaf.germ E.U.1 x E.mem (E.v i) = ψ (MvPolynomial.X i)) ∧
      ∀ (q : (pointClosureIdeal x).blowUp) (hq : (pointClosureIdeal x).blowUpπ q = x),
        let : (pointClosureIdeal x).blowUp.Over (Spec (.of K)) :=
          ⟨(pointClosureIdeal x).blowUpπ ≫ (X ↘ Spec (.of K))⟩
        ∃ (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] (pointClosureIdeal x).blowUp.presheaf.stalk q),
          τ.toRingHom.FormallyEtale ∧
          ((pointClosureIdeal x).comap (pointClosureIdeal x).blowUpπ).stalkIdeal q =
            Ideal.span {τ (MvPolynomial.X k)} ∧
          τ (MvPolynomial.X k) ∈ nonZeroDivisors ((pointClosureIdeal x).blowUp.presheaf.stalk q) ∧
          (∀ g, stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq (ψ g) =
            τ (polynomialPointBlowupMap k g)) ∧
          ∀ (r : X.presheaf.stalk x) (m : ℕ), (m : ℕ∞) ≤ localAdicOrder (X.presheaf.stalk x) r →
            ∃! z : (pointClosureIdeal x).blowUp.presheaf.stalk q,
              stalkMapAtEq (pointClosureIdeal x).blowUpπ q x hq r = τ (MvPolynomial.X k) ^ m * z ∧
              Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) z =
                pointBlowupExceptionalEvaluation τ.toRingHom k
                  (projectiveDehomogenize K k (homogeneousTaylorForm m (stalkTaylorExpansion x e r))) := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of K))
  obtain ⟨e', ψ, E, hmax, hE, hX, hforms⟩ :=
    exists_suppliedCompletion_adapted_point_coordinates c x hx hxc α e
  have hord (r : X.presheaf.stalk x) : (stalkTaylorExpansion x e' r).order =
      localAdicOrder (X.presheaf.stalk x) r := completionCoordinates_order_eq_localAdicOrder e'.toRingEquiv r
  refine ⟨ψ, E, hE, ?_⟩
  intro q hq
  obtain ⟨k, τ, hτ, hI, hreg, hcomp, hall⟩ := prescribed_parameters_pointBlowup_etale_restriction
    x hxc ψ (stalkTaylorExpansion x e') hX hord hmax E hE q hq
  refine ⟨k, τ, hτ, hI, hreg, hcomp, ?_⟩
  intro r m hr
  have h := hall r m (by rwa [hord])
  rwa [hforms r m hr] at h

end MixedFujita
