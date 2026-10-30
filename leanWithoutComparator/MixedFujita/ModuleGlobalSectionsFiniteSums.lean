/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.GlobalSectionsOfPushforwardIso
public import MixedFujita.ActualCartierSerreVanishing

/-! 実基礎体線形な有限直和の切断次元評価。 See reports/check-216-proper-fixed-twist-integration.json for the verified scope. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual module morphisms induce base-ring-linear maps on global sections. -/
noncomputable def moduleHomGlobalSectionsBaseLinearMap
    (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of R))]
    {M N : X.Modules} (a : M ⟶ N) : Γ(M, ⊤) →ₗ[R] Γ(N, ⊤) where
  toFun := a.app ⊤
  map_add' := map_add _
  map_smul' r x := by
    simp only [Scheme.Modules.base_smul_globalSections]
    exact Scheme.Modules.Hom.app_smul a _ _


/-- Finite sums of actual module sheaves have no more global sections than the
product of their section spaces, over the actual base field. -/
theorem moduleBiproduct_globalSections_finite_and_finrank_le
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    {k : ℕ} (G : Fin k → X.Modules)
    (hfin : ∀ i, FiniteDimensional K Γ(G i, ⊤)) :
    FiniteDimensional K Γ(⨁ G, ⊤) ∧
      Module.finrank K Γ(⨁ G, ⊤) ≤ ∑ i, Module.finrank K Γ(G i, ⊤) := by
  letI := hfin
  let F : (∀ i, Γ(G i, ⊤)) →ₗ[K] Γ(⨁ G, ⊤) :=
    ∑ i, (moduleHomGlobalSectionsBaseLinearMap K (biproduct.ι G i)).comp
      (LinearMap.proj i)
  have hs : Function.Surjective F := by
    intro s
    refine ⟨fun i => (biproduct.π G i).app ⊤ s, ?_⟩
    let ev : (⨁ G ⟶ ⨁ G) →+ Γ(⨁ G, ⊤) :=
      { toFun := fun a => a.app ⊤ s, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have h := congrArg ev (biproduct.total (f := G))
    rw [map_sum] at h
    exact (LinearMap.sum_apply _ _ _).trans (Eq.trans (by rfl) h)
  have hfinite := FiniteDimensional.of_surjective F hs
  exact ⟨hfinite, by simpa only [Module.finrank_pi_fintype] using
    LinearMap.finrank_le_finrank_of_surjective hs⟩


/-- The specified finite free twist has an actual finite section space with
rank bounded by the number of summands times the line-bundle section rank. -/
theorem sgaTwistUnitBiproduct_globalSections_finite_and_finrank_le
    {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    (L : X.LineBundle) (k : ℕ) (n : ℤ)
    (hfin : FiniteDimensional K Γ(L.toModules n, ⊤)) :
    FiniteDimensional K Γ(L.twist (CohomologyAux.unitBiproduct X k) n, ⊤) ∧
      Module.finrank K Γ(L.twist (CohomologyAux.unitBiproduct X k) n, ⊤) ≤
        k * Module.finrank K Γ(L.toModules n, ⊤) := by
  let e := L.twistBiproductIso n (fun _ : Fin k => CohomologyAux.unitModule X) ≪≫
    biproduct.mapIso (fun _ : Fin k => eqToIso (L.twist_unit_eq n))
  let a := moduleIsoGlobalSectionsBaseLinearEquiv K e
  have h := moduleBiproduct_globalSections_finite_and_finrank_le
    (fun _ : Fin k => L.toModules n) (fun _ => hfin)
  letI := h.1
  have hfinite := FiniteDimensional.of_injective a.toLinearMap a.injective
  refine ⟨hfinite, ?_⟩
  rw [a.finrank_eq]
  simpa using h.2

end MixedFujita
