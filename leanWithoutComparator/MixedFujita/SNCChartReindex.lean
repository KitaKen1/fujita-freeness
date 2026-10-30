/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCCompletedDivisorOrders
public import MixedFujita.EtalePolynomialDifferentials

/-! Reindex an actual SNC chart without changing its open subset or its
divisors. At a closed point on a marked member, a centered chart and a
compatible completion can be chosen with any prescribed normal index.
This aligns the SNC normal coordinate with the point-blow-up chart. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

/-- Relabel the polynomial coordinates on the same actual affine chart. -/
noncomputable def etaleChartReindex (c : EtaleChart K X n) (e : Fin n ≃ Fin n) :
    EtaleChart K X n where
  U := c.U
  isAffine := c.isAffine
  nonempty := c.nonempty
  coords := c.coords.comp (MvPolynomial.renameEquiv K e).toAlgHom
  formallyEtale := formallyEtale_comp _ c.formallyEtale _
    (ringHom_formallyEtale_of_etale _
      (RingHom.Etale.of_bijective (MvPolynomial.renameEquiv K e).bijective))

theorem etaleChartReindex_U (c : EtaleChart K X n) (e : Fin n ≃ Fin n) :
    (etaleChartReindex c e).U = c.U := rfl

theorem etaleChartReindex_variable (c : EtaleChart K X n) (e : Fin n ≃ Fin n) (i : Fin n) :
    (etaleChartReindex c e).coords (MvPolynomial.X i) = c.coords (MvPolynomial.X (e i)) := by
  change c.coords (MvPolynomial.rename e (MvPolynomial.X i)) = _
  rw [MvPolynomial.rename_X]

theorem etaleChartReindex_stalk_variable (c : EtaleChart K X n) (e : Fin n ≃ Fin n)
    (x : X) (hx : x ∈ c.U) (i : Fin n) :
    etaleChartStalkCoords (etaleChartReindex c e) x hx (MvPolynomial.X i) =
      etaleChartStalkCoords c x hx (MvPolynomial.X (e i)) := by
  change X.presheaf.germ c.U x hx ((etaleChartReindex c e).coords (MvPolynomial.X i)) = _
  rw [etaleChartReindex_variable]
  rfl

theorem isSNCChart_reindex (c : EtaleChart K X n) {r : ℕ} (ξ : Fin r → X)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (e : Fin n ≃ Fin n) :
    IsSNCChart (etaleChartReindex c e) ξ (fun i => (σ i).map e.symm) := by
  classical
  refine ⟨?_, fun i => ?_⟩
  · intro i j a hi hj
    have hi' : σ i = some (e a) := by
      cases h : σ i with
      | none => simp [h] at hi
      | some b => simpa only [h, Option.map_some, Option.some.injEq,
          Equiv.symm_apply_eq] using hi
    have hj' : σ j = some (e a) := by
      cases h : σ j with
      | none => simp [h] at hj
      | some b => simpa only [h, Option.map_some, Option.some.injEq,
          Equiv.symm_apply_eq] using hj
    exact hc.1 i j (e a) hi' hj'
  · have hi := hc.2 i
    cases h : σ i with
    | none => simpa only [h, Option.map_none, Option.elim_none, etaleChartReindex_U] using hi
    | some a =>
      simp only [h, Option.map_some, Option.elim_some]
      rw [etaleChartReindex_variable, Equiv.apply_symm_apply]
      simpa only [etaleChartReindex, h, Option.elim_some] using hi

variable [IsIntegral X] [IsLocallyNoetherian X]
  [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]

/-- Center the actual SNC chart at a closed point and place the marked
member at the prescribed normal index, preserving all other members. -/
theorem exists_centered_snc_completion_with_marked_index [IsAlgClosed K]
    {r : ℕ} (ξ : Fin r → X) (hsnc : IsSNCFamily K n ξ)
    (x : X) (hx : IsClosed ({x} : Set X)) (e : Fin r)
    (he : x ∈ closure ({ξ e} : Set X)) (k : Fin n) :
    ∃ (c : EtaleChart K X n) (σ : Fin r → Option (Fin n)) (hxc : x ∈ c.U),
      IsSNCChart c ξ σ ∧ σ e = some k ∧
      (∀ i, x ∈ closure ({ξ i} : Set X) ↔ ∃ j, σ i = some j) ∧
      ∃ completion : AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) ≃ₐ[K] MvPowerSeries (Fin n) K,
        (∀ j, stalkTaylorExpansion x completion
          (etaleChartStalkCoords c x hxc (MvPolynomial.X j)) = MvPowerSeries.X j) ∧
        ∀ a, (stalkTaylorExpansion x completion a).order =
          localAdicOrder (X.presheaf.stalk x) a := by
  classical
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨β⟩ := smoothScheme_closedPoint_has_localEvaluation (K := K) x hx
  obtain ⟨c, σ, hxc, hc, hnu, hsome, hmem⟩ := exists_centered_snc_chart ξ hsnc x β
  obtain ⟨a, ha⟩ := hmem e he
  let p := Equiv.swap a k
  let c' := etaleChartReindex c p
  let σ' : Fin r → Option (Fin n) := fun i => (σ i).map p.symm
  have hc' : IsSNCChart c' ξ σ' := isSNCChart_reindex c ξ σ hc p
  have he' : σ' e = some k := by simp [σ', ha, p]
  have hmem' (i : Fin r) : x ∈ closure ({ξ i} : Set X) ↔ ∃ j, σ' i = some j := by
    constructor
    · intro hi
      obtain ⟨b, hb⟩ := hmem i hi
      exact ⟨p.symm b, by simp only [σ', hb, Option.map_some]⟩
    · rintro ⟨b, hb⟩
      cases hσ : σ i with
      | none => simp [σ', hσ] at hb
      | some d => exact hsome i d hσ
  have hxc' : x ∈ c'.U := hxc
  obtain ⟨completion, hcompletion, hord⟩ := etaleChart_exists_taylorCoordinates c' x hxc' β
  refine ⟨c', σ', hxc', hc', he', hmem', completion, ?_, hord⟩
  intro j
  have hj := hcompletion j
  rw [etaleChartCenteredStalkCoords_variable] at hj
  have hβ0 : rationalAffineGermPoint x hxc' β (c'.coords (MvPolynomial.X j)) = 0 := by
    change β (etaleChartStalkCoords c' x hxc' (MvPolynomial.X j)) = 0
    rw [etaleChartReindex_stalk_variable]
    exact not_not.mp ((rationalLocalPoint_isUnit_iff β _).not.mp (hnu (p j)))
  rwa [hβ0, map_zero, sub_zero] at hj

end MixedFujita
