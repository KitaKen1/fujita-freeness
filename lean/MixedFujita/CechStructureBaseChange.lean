/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineSectionsBaseChange
public import SGA.Foundations.Cohomology.QuasiCoherentLocal
public import SGA.Foundations.Cohomology.Pushforward

/-!
Base change of the Čech complex of functions (step 10, R4).

For a scheme `X` over `Spec A`, an `A`-algebra `L`, the pullback `Y = X ×_A L` and finitely many
opens of `X` with affine Čech intersections, the Čech cochains of `𝒪_Y` for the inverse images
are `L ⊗_A` the Čech cochains of `𝒪_X`, `L`-linearly and compatibly with the Čech differentials
(`cechStructureBaseChangeEquiv`, `cechStructureBaseChangeEquiv_cechD`), by the affine base change
of check 497 on every intersection. Hence `L ⊗ C(X)` is exact where `C(Y)` is
(`exact_lTensor_cechStructure_iff`), and the kernels in degree zero agree
(`kerCechStructureBaseChangeEquiv`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule

/-- Restricting back and forth between equal opens is the identity. -/
theorem structure_map_map_self (X : Scheme.{u}) {V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ W)
    (a : Γ(X, V)) : X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op a) = a := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  have : (homOfLE h₁).op ≫ (homOfLE h₂).op = 𝟙 (op V) := rfl
  rw [this, CategoryTheory.Functor.map_id]
  rfl

/-- Two composites of restrictions between the same opens agree. -/
theorem structure_map_map_eq (Y : Scheme.{u}) {V₁ V₂ V₂' V₃ : Y.Opens} (h₁ : V₂ ≤ V₁)
    (h₂ : V₃ ≤ V₂) (h₁' : V₂' ≤ V₁) (h₂' : V₃ ≤ V₂') (s : Γ(Y, V₁)) :
    Y.presheaf.map (homOfLE h₂).op (Y.presheaf.map (homOfLE h₁).op s) =
      Y.presheaf.map (homOfLE h₂').op (Y.presheaf.map (homOfLE h₁').op s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  rfl

/-- **Functions over equal opens**, as an algebra isomorphism over the base. -/
noncomputable def structureSectionsEqAlgEquiv (A : Type u) [CommRing A] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of A))] {V W : X.Opens} (h : V = W) : Γ(X, V) ≃ₐ[A] Γ(X, W) :=
  AlgEquiv.ofAlgHom (structureRestrictAlgHom A X h.ge) (structureRestrictAlgHom A X h.le)
    (AlgHom.ext fun a => structure_map_map_self X h.le h.ge a)
    (AlgHom.ext fun a => structure_map_map_self X h.ge h.le a)

theorem structureSectionsEqAlgEquiv_apply (A : Type u) [CommRing A] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of A))] {V W : X.Opens} (h : V = W) (a : Γ(X, V)) :
    structureSectionsEqAlgEquiv A X h a = X.presheaf.map (homOfLE h.ge).op a :=
  rfl

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of L))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A L))))
  {n : ℕ} (U : Fin n → X.Opens)
  (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x))

/-- Base change of a restricted pure tensor. -/
theorem sectionsBaseChangeEquiv_tmul_restrict {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : W ≤ V) (l : L) (a : Γ(X, V)) :
    sectionsBaseChangeEquiv H hW (l ⊗ₜ X.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE ((Opens.map g.base).monotone h)).op
        (sectionsBaseChangeEquiv H hV (l ⊗ₜ a)) :=
  sectionsBaseChangeEquiv_restrict H hV hW h (l ⊗ₜ a)

/-- Base change of a restricted pure tensor, for sections of the unit module. -/
theorem sectionsBaseChangeEquiv_tmul_restrict_unit {V W : X.Opens} (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : W ≤ V) (l : L) (a : Γ(CohomologyAux.unitModule X, V)) :
    sectionsBaseChangeEquiv H hW (l ⊗ₜ (CohomologyAux.unitModule X).presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE ((Opens.map g.base).monotone h)).op
        (sectionsBaseChangeEquiv H hV (l ⊗ₜ a)) :=
  sectionsBaseChangeEquiv_restrict H hV hW h (l ⊗ₜ a)

include H hU in
/-- **Base change of Čech cochains of functions**, `L`-linearly. -/
noncomputable def cechStructureBaseChangeEquiv (q : ℕ) :
    L ⊗[A] TopCat.Presheaf.CechCochain U (CohomologyAux.unitModule X).presheaf q ≃ₗ[L]
      TopCat.Presheaf.CechCochain (fun i => g ⁻¹ᵁ U i) (CohomologyAux.unitModule Y).presheaf q :=
  (TensorProduct.piRight A L L
      (fun x : Fin (q + 1) → Fin n => Γ(X, TopCat.Presheaf.cechOpen U x))).trans
    (LinearEquiv.piCongrRight fun x =>
      ((sectionsBaseChangeEquiv H (hU x)).trans
        (structureSectionsEqAlgEquiv L Y (CohomologyAux.cechOpen_preimage g U x).symm)).toLinearEquiv)

theorem cechStructureBaseChangeEquiv_tmul (q : ℕ) (l : L)
    (c : TopCat.Presheaf.CechCochain U (CohomologyAux.unitModule X).presheaf q)
    (x : Fin (q + 1) → Fin n) :
    cechStructureBaseChangeEquiv H U hU q (l ⊗ₜ c) x =
      Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op
        (sectionsBaseChangeEquiv H (hU x) (l ⊗ₜ c x)) :=
  rfl

include H hU in
/-- **Base change commutes with the Čech differentials.** -/
theorem cechStructureBaseChangeEquiv_cechD (q : ℕ)
    (t : L ⊗[A] TopCat.Presheaf.CechCochain U (CohomologyAux.unitModule X).presheaf q) :
    cechStructureBaseChangeEquiv H U hU (q + 1)
        ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
          (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U q).lTensor L t) =
      TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule Y).presheaf
        (presheaf_map_homOfLE_ring_smul L (CohomologyAux.unitModule Y)) (fun i => g ⁻¹ᵁ U i) q
        (cechStructureBaseChangeEquiv H U hU q t) := by
  induction t using TensorProduct.inductionOn with
  | tmul l c =>
    funext x
    rw [LinearMap.lTensor_tmul, cechStructureBaseChangeEquiv_tmul, TopCat.Presheaf.cechDₗ_apply,
      TopCat.Presheaf.cechDₗ_apply, TopCat.Presheaf.cechD_apply, TopCat.Presheaf.cechD_apply,
      TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_zsmul, map_zsmul, cechStructureBaseChangeEquiv_tmul]
    congr 1
    rw [sectionsBaseChangeEquiv_tmul_restrict_unit H (hU (x ∘ Fin.succAbove k)) (hU x)
      (TopCat.Presheaf.cechOpen_le_comp U x (Fin.succAbove k)) l (c (x ∘ Fin.succAbove k))]
    exact structure_map_map_eq Y _ _ _ _ _
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

include H hU in
/-- **Exactness of the base change of the Čech complex is exactness of the Čech complex of the
fibre.** -/
theorem exact_lTensor_cechStructure_iff (q : ℕ) :
    Function.Exact
        ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
          (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U q).lTensor L)
        ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
          (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U (q + 1)).lTensor L) ↔
      Function.Exact
        (TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule Y).presheaf
          (presheaf_map_homOfLE_ring_smul L (CohomologyAux.unitModule Y)) (fun i => g ⁻¹ᵁ U i) q)
        (TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule Y).presheaf
          (presheaf_map_homOfLE_ring_smul L (CohomologyAux.unitModule Y)) (fun i => g ⁻¹ᵁ U i)
          (q + 1)) :=
  (Function.Exact.iff_of_ladder_addEquiv (cechStructureBaseChangeEquiv H U hU q).toAddEquiv
    (cechStructureBaseChangeEquiv H U hU (q + 1)).toAddEquiv
    (cechStructureBaseChangeEquiv H U hU (q + 1 + 1)).toAddEquiv
    (f₁₂ := ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
      (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U q).lTensor L).toAddMonoidHom)
    (f₂₃ := ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
      (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U
        (q + 1)).lTensor L).toAddMonoidHom)
    (g₁₂ := (TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule Y).presheaf
      (presheaf_map_homOfLE_ring_smul L (CohomologyAux.unitModule Y)) (fun i => g ⁻¹ᵁ U i)
        q).toAddMonoidHom)
    (g₂₃ := (TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule Y).presheaf
      (presheaf_map_homOfLE_ring_smul L (CohomologyAux.unitModule Y)) (fun i => g ⁻¹ᵁ U i)
        (q + 1)).toAddMonoidHom)
    (AddMonoidHom.ext fun t => (cechStructureBaseChangeEquiv_cechD H U hU q t).symm)
    (AddMonoidHom.ext fun t => (cechStructureBaseChangeEquiv_cechD H U hU (q + 1) t).symm)).symm

include H hU in
/-- **The kernels in degree zero agree**: the base change of the Čech `H⁰` of the model computes the
Čech `H⁰` of the fibre, through the base change of the differential. -/
noncomputable def kerCechStructureBaseChangeEquiv :
    LinearMap.ker ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
      (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U 0).baseChange L) ≃ₗ[L]
    LinearMap.ker (TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule Y).presheaf
      (presheaf_map_homOfLE_ring_smul L (CohomologyAux.unitModule Y)) (fun i => g ⁻¹ᵁ U i) 0) :=
  (cechStructureBaseChangeEquiv H U hU 0).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker]
    have hcomm := cechStructureBaseChangeEquiv_cechD H U hU 0
      ((cechStructureBaseChangeEquiv H U hU 0).symm y)
    rw [LinearEquiv.apply_symm_apply] at hcomm
    constructor
    · intro h
      rw [← hcomm]
      change (cechStructureBaseChangeEquiv H U hU (0 + 1))
        ((TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
          (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U 0).lTensor L
            ((cechStructureBaseChangeEquiv H U hU 0).symm y)) = 0
      rw [show (TopCat.Presheaf.cechDₗ (CohomologyAux.unitModule X).presheaf
          (presheaf_map_homOfLE_ring_smul A (CohomologyAux.unitModule X)) U 0).lTensor L
            ((cechStructureBaseChangeEquiv H U hU 0).symm y) = 0 from h, map_zero]
    · intro h
      apply (cechStructureBaseChangeEquiv H U hU (0 + 1)).injective
      rw [map_zero]
      exact hcomm.trans h)

end MixedFujita
