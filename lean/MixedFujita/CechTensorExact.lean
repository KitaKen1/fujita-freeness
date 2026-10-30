/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FlatComplexKernelBaseChange
public import SGA.Foundations.Cohomology.CechVanishing
public import SGA.Foundations.Cohomology.CechLocalization
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections

/-!
Exactness of tensored Čech complexes above the number of opens (step 10, R4).

Let `P` be a presheaf of abelian groups whose sections are `R`-modules with `R`-linear
restrictions, and `U₀, …, U_{n-1}` finitely many opens. For an `R`-module `N`, the presheaf
`V ↦ N ⊗ P(V)` (`tensorPresheaf`) has as Čech cochains `N ⊗` the Čech cochains of `P`, compatibly
with the differentials (`cechCochainTensorEquiv_cechD`), since the products are finite. SGA's
vanishing above the number of opens then gives exactness of `N ⊗ C` in degrees `≥ n` for the
`R`-linear Čech complex `C` of `P`, for every `N` (`exact_lTensor_cechDₗ_of_card_le`). This is
the hypothesis on the top degrees in the transfer of vanishing (checks 492–494).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct

namespace MixedFujita

universe w v u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{v} X) {R : Type*} [CommRing R]
  [∀ V : Opens X, Module R (P.obj (op V))]
  (hlin : ∀ ⦃V W : Opens X⦄ (h : W ≤ V) (r : R) (s : P.obj (op V)),
    P.map (homOfLE h).op (r • s) = r • P.map (homOfLE h).op s)

/-- The restriction to the same open is the identity. -/
theorem resₗ_self (V : Opens X) (h : V ≤ V) :
    TopCat.Presheaf.resₗ P hlin h = LinearMap.id := by
  ext s
  rw [TopCat.Presheaf.resₗ_apply, LinearMap.id_apply]
  have : (homOfLE h).op = 𝟙 (op V) := rfl
  rw [this, P.map_id]
  rfl

/-- Restrictions compose. -/
theorem resₗ_comp {V₁ V₂ V₃ : Opens X} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) :
    (TopCat.Presheaf.resₗ P hlin h₂).comp (TopCat.Presheaf.resₗ P hlin h₁) =
      TopCat.Presheaf.resₗ P hlin (h₂.trans h₁) := by
  ext s
  rw [LinearMap.comp_apply, TopCat.Presheaf.resₗ_apply, TopCat.Presheaf.resₗ_apply,
    TopCat.Presheaf.resₗ_apply, TopCat.Presheaf.map_map_apply]

/-- **The presheaf `V ↦ N ⊗ P(V)`.** -/
noncomputable def tensorPresheaf (N : Type w) [AddCommGroup N] [Module R N] :
    TopCat.Presheaf AddCommGrpCat.{max w v} X where
  obj V := AddCommGrpCat.of (N ⊗[R] P.obj (op V.unop))
  map {V W} f := AddCommGrpCat.ofHom
    ((TopCat.Presheaf.resₗ P hlin (leOfHom f.unop)).lTensor N).toAddMonoidHom
  map_id V := by
    ext x
    change ((TopCat.Presheaf.resₗ P hlin _).lTensor N) x = x
    rw [resₗ_self, LinearMap.lTensor_id, LinearMap.id_apply]
  map_comp f g := by
    ext x
    change ((TopCat.Presheaf.resₗ P hlin _).lTensor N) x =
      ((TopCat.Presheaf.resₗ P hlin _).lTensor N) (((TopCat.Presheaf.resₗ P hlin _).lTensor N) x)
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, resₗ_comp]

variable {n : ℕ} (U : Fin n → Opens X)

/-- **Tensored Čech cochains are the Čech cochains of the tensored presheaf.** -/
noncomputable def cechCochainTensorEquiv (N : Type w) [AddCommGroup N] [Module R N] (q : ℕ) :
    N ⊗[R] TopCat.Presheaf.CechCochain U P q ≃ₗ[R]
      (∀ x : Fin (q + 1) → Fin n, N ⊗[R] P.obj (op (TopCat.Presheaf.cechOpen U x))) :=
  TensorProduct.piRight R R N (fun x => P.obj (op (TopCat.Presheaf.cechOpen U x)))

/-- **Compatibility with the Čech differentials.** -/
theorem cechCochainTensorEquiv_cechD (N : Type w) [AddCommGroup N] [Module R N] (q : ℕ)
    (t : N ⊗[R] TopCat.Presheaf.CechCochain U P q) :
    cechCochainTensorEquiv P U N (q + 1) ((TopCat.Presheaf.cechDₗ P hlin U q).lTensor N t) =
      TopCat.Presheaf.cechD U (tensorPresheaf P hlin N) q (cechCochainTensorEquiv P U N q t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a c =>
    funext x
    rw [LinearMap.lTensor_tmul, TopCat.Presheaf.cechD_apply]
    simp only [cechCochainTensorEquiv, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul, TopCat.Presheaf.cechDₗ_apply, TopCat.Presheaf.cechD_apply,
      TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul]
    rfl
  | add t t' ht ht' => rw [map_add, map_add, ht, ht', map_add, map_add]

include hlin in
theorem cechDₗ_comp_eq_zero (q : ℕ) :
    (TopCat.Presheaf.cechDₗ P hlin U (q + 1)).comp (TopCat.Presheaf.cechDₗ P hlin U q) = 0 := by
  refine LinearMap.ext fun c => ?_
  exact TopCat.Presheaf.cechD_cechD U P q c

/-- **Exactness of `N ⊗ C` above the number of opens**, for every `R`-module `N`. -/
theorem exact_lTensor_cechDₗ_of_card_le (N : Type w) [AddCommGroup N] [Module R N] (q : ℕ)
    (hq : n ≤ q + 1) :
    Function.Exact ((TopCat.Presheaf.cechDₗ P hlin U q).lTensor N)
      ((TopCat.Presheaf.cechDₗ P hlin U (q + 1)).lTensor N) := by
  have hex := TopCat.Presheaf.cechComplex_exactAt_of_card_le (tensorPresheaf P hlin N) U
    (q := q + 1) hq (Nat.succ_pos q)
  rw [TopCat.Presheaf.cechComplex_exactAt_succ_iff] at hex
  intro y
  constructor
  · intro hy
    have h0 : TopCat.Presheaf.cechD U (tensorPresheaf P hlin N) (q + 1)
        (cechCochainTensorEquiv P U N (q + 1) y) = 0 := by
      rw [← cechCochainTensorEquiv_cechD, hy, map_zero]
    obtain ⟨b, hb⟩ := hex _ h0
    refine ⟨(cechCochainTensorEquiv P U N q).symm b, ?_⟩
    apply (cechCochainTensorEquiv P U N (q + 1)).injective
    rw [cechCochainTensorEquiv_cechD, LinearEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨b, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, cechDₗ_comp_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]

section Scheme

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of R))]

/-- The `R`-module structure on the sections of an `𝒪_X`-module over `Spec R`, through
`R → Γ(X, V)`. -/
noncomputable abbrev sectionsRingModule (M : X.Modules) (V : X.Opens) : Module R Γ(M, V) :=
  Module.compHom Γ(M, V) ((X.baseRingToStructurePresheaf R).app (op V)).hom

attribute [local instance] sectionsRingModule

theorem sectionsRing_smul_def (M : X.Modules) (V : X.Opens) (c : R) (s : Γ(M, V)) :
    c • s = ((X.baseRingToStructurePresheaf R).app (op V)).hom c • s := rfl

/-- **Restrictions of an `𝒪_X`-module are `R`-linear.** -/
theorem presheaf_map_homOfLE_ring_smul (M : X.Modules) ⦃U V : X.Opens⦄ (h : V ≤ U) (c : R)
    (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (c • s) = c • M.presheaf.map (homOfLE h).op s := by
  rw [sectionsRing_smul_def, sectionsRing_smul_def, Scheme.Modules.map_smul]
  congr 1
  have hnat := (X.baseRingToStructurePresheaf R).naturality (homOfLE h).op
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hnat
  rw [hnat]
  rfl

/-- **Exactness of `N ⊗ C` above the number of opens** for the `R`-linear Čech complex of an
`𝒪_X`-module on a scheme over `Spec R`. -/
theorem exact_lTensor_cechDₗ_modules_of_card_le (M : X.Modules) {n : ℕ} (U : Fin n → X.Opens)
    (N : Type w) [AddCommGroup N] [Module R N] (q : ℕ) (hq : n ≤ q + 1) :
    Function.Exact
      ((TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U q).lTensor N)
      ((TopCat.Presheaf.cechDₗ M.presheaf (presheaf_map_homOfLE_ring_smul R M) U
        (q + 1)).lTensor N) :=
  exact_lTensor_cechDₗ_of_card_le M.presheaf (presheaf_map_homOfLE_ring_smul R M) U N q hq

end Scheme

end MixedFujita
