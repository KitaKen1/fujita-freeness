/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CechRankTransfer
public import MixedFujita.CechHomologyComparison
public import MixedFujita.CechStructureBaseChange
public import MixedFujita.SGACohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
The dimension of the global functions of the fibres of a flat proper scheme (step 10, R4-3).

Let `X` be flat and proper over a noetherian domain `A`, with a finite affine cover. There are
`f ≠ 0` and `r` such that `dim_k Γ(X_k, O) = r` for every field `k` over `A` in which `f` is a
unit and every base change `X_k = X ×_A k` (`exists_ne_zero_finrank_globalSections_fibre`).

The Čech complex of `O_X` is a complex of flat `A`-modules (`flat_sections_of_flat`), exact on
top after any `N ⊗ -` (check 495), with finitely generated cohomology (SGA's finiteness for proper
schemes, check 500) and finitely generated `ker d⁰ = Γ(X, O)`; check 514 applies. The kernel of
`k ⊗ d⁰` is the Čech `H⁰` of the base change (check 498), that is `Γ(X_k, O)` (check 500).

For the closure `T_A` this gives `dim_κ Γ(T_κ, O) = dim_K Γ(T, O) = 1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

attribute [local instance] sectionsRingModule

section Flat

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))]

/-- The functions on an affine open of a scheme flat over `A` are flat over `A`. -/
theorem flat_sections_of_flat [Flat (X ↘ Spec (CommRingCat.of A))] {V : X.Opens}
    (hV : IsAffineOpen V) :
    Module.Flat A ((CohomologyAux.unitModule X).presheaf.obj (op V)) := by
  have h := HasRingHomProperty.appLE @Flat (X ↘ Spec (CommRingCat.of A)) inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have h2 : RingHom.Flat (((X ↘ Spec (CommRingCat.of A)).appLE ⊤ V le_top).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) :=
    (RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv _).2 h
  let _ := structureSectionsAlgebra A X V
  have h3 : RingHom.Flat (algebraMap A Γ(X, V)) := by
    have := structureSections_algebraMap A X V
    rw [← CommRingCat.hom_ofHom (algebraMap A Γ(X, V)), this]
    exact h2
  exact h3

end Flat

section Rank

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))]

/-- **The global functions of the fibres of a flat proper scheme have constant dimension away
from one element.** -/
theorem exists_ne_zero_finrank_globalSections_fibre [IsLocallyNoetherian X]
    [IsProper (X ↘ Spec (CommRingCat.of A))] [Flat (X ↘ Spec (CommRingCat.of A))]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) :
    ∃ f : A, f ≠ 0 ∧ ∃ r : ℕ, ∀ (k : Type u) [Field k] [Algebra A k],
      IsUnit (algebraMap A k f) →
      ∀ (Y : Scheme.{u}) [Y.Over (Spec (CommRingCat.of k))] (g : Y ⟶ X),
        IsPullback g (Y ↘ Spec (CommRingCat.of k)) (X ↘ Spec (CommRingCat.of A))
          (Spec.map (CommRingCat.ofHom (algebraMap A k))) →
        Module.finrank k ((CohomologyAux.unitModule Y).presheaf.obj (op ⊤)) = r := by
  classical
  let M := CohomologyAux.unitModule X
  have hUc : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x) :=
    Scheme.Modules.isAffineOpen_cechOpen hU
  have hflat : ∀ q, Module.Flat A (TopCat.Presheaf.CechCochain U M.presheaf q) := by
    intro q
    have : ∀ x : Fin (q + 1) → Fin n,
        Module.Flat A (M.presheaf.obj (op (TopCat.Presheaf.cechOpen U x))) :=
      fun x => flat_sections_of_flat (hUc x)
    exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A)
      (M := fun x : Fin (q + 1) → Fin n =>
        M.presheaf.obj (op (TopCat.Presheaf.cechOpen U x)))).symm
  have hfg : ∀ i, Module.Finite A (homologyAt
      (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul A M) U)
      (cechDₗ_comp_eq_zero M.presheaf (presheaf_map_homOfLE_ring_smul A M) U) i) := by
    intro i
    have := proper_coherent_cohomology_finite A M (i + 1)
    exact finite_cechHomologyAt A M U hU hcov i
  have hker : Module.Finite A (LinearMap.ker
      (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul A M) U 0)) := by
    have := proper_coherent_cohomology_finite A M 0
    have e1 := Scheme.Modules.cohomologyZeroBaseLinearEquiv A X M
    have e2 := LinearEquiv.ofBijective (cechAugmentationLinear A M U)
      (cechAugmentationLinear_bijective A M U hcov)
    have hring : (X.baseRingToStructurePresheaf A).app (op ⊤) =
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (X ↘ Spec (CommRingCat.of A)).appTop := by
      rw [Scheme.baseRingToStructurePresheaf_app_eq_appLE, Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE]
      rfl
    have hinst : Scheme.Modules.globalSectionsBaseModule A X M = sectionsRingModule A M ⊤ := by
      refine Module.ext' _ _ fun r s => ?_
      change Scheme.Modules.baseRingToGlobalSections A X r • s =
        ((X.baseRingToStructurePresheaf A).app (op ⊤)).hom r • s
      rw [Scheme.Modules.baseRingToGlobalSections_apply, hring]
      rfl
    have hfin : @Module.Finite A Γ(M, ⊤) _ _ (Scheme.Modules.globalSectionsBaseModule A X M) := by
      let _ : Module A Γ(M, ⊤) := Scheme.Modules.globalSectionsBaseModule A X M
      exact Module.Finite.equiv e1
    have hfin' : @Module.Finite A Γ(M, ⊤) _ _ (sectionsRingModule A M ⊤) := hinst ▸ hfin
    exact Module.Finite.equiv e2
  obtain ⟨f, hf, r, hr⟩ := exists_ne_zero_finrank_ker_baseChange_eq
    (TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul A M) U)
    (cechDₗ_comp_eq_zero M.presheaf (presheaf_map_homOfLE_ring_smul A M) U) n
    (fun N _ _ i hi => exact_lTensor_cechDₗ_modules_of_card_le A M U N i (by omega)) hfg
  refine ⟨f, hf, r, fun k _ _ hk Y _ g H => ?_⟩
  have hcovY : ⨆ i, g ⁻¹ᵁ U i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hcov, Scheme.Hom.preimage_top]
  have e3 := LinearEquiv.ofBijective
    (cechAugmentationLinear k (CohomologyAux.unitModule Y) (fun i => g ⁻¹ᵁ U i))
    (cechAugmentationLinear_bijective k (CohomologyAux.unitModule Y) _ hcovY)
  have e4 := kerCechStructureBaseChangeEquiv H U hUc
  rw [e3.finrank_eq, ← e4.finrank_eq]
  exact hr k hk

end Rank

end MixedFujita
