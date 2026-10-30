/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CechStructureBaseChange

/-!
Base change of the Čech complex of `𝒪_X(D)` (step 10, R4).

Let `D` be a Cartier divisor on an integral scheme `X` over `Spec A` with local equations `g_i` on
the opens `U_i` of a finite cover. Trivializing a Čech cochain of `𝒪_X(D)` at the first vertex of
each intersection (check 496) identifies the Čech cochains of `𝒪_X(D)` with those of `𝒪_X`
(`cartierCechTrivialization`); in these trivializations the Čech differential multiplies the
face terms by the transition functions `u_{ij}` with `u_{ij} g_j = g_i`
(`cartierCechTrivialization_cechD`).

Over a pullback square `Y = X ×_A L` with local equations `g'_i` of a Cartier divisor `D'` on `Y`
whose transition functions are the images of the `u_{ij}`, combining with check 498 gives an
`L`-linear isomorphism `L ⊗_A Č(𝒪_X(D)) ≅ Č(𝒪_Y(D'))` compatible with the differentials
(`cartierCechBaseChangeEquiv`, `cartierCechBaseChangeEquiv_cechD`), so that exactness corresponds
(`exact_lTensor_cartierCech_iff`). On the closed fibre there is no pullback of Cartier divisors;
this comparison replaces it.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule

/-- A Čech intersection lies in the opens of its first vertex and of the first vertex of a
face. -/
theorem cechOpen_le_firstPair {X : Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens) {m : ℕ} (x : Fin (m + 2) → Fin n) (k : Fin (m + 2)) :
    TopCat.Presheaf.cechOpen U x ≤ U (x 0) ⊓ U (x (Fin.succAbove k 0)) :=
  le_inf (TopCat.Presheaf.cechOpen_le U x 0) (TopCat.Presheaf.cechOpen_le U x _)

section Trivialization

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of A))] (D : CartierDivisor X) {n : ℕ} (U : Fin n → X.Opens)
  (hne : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), Nonempty (TopCat.Presheaf.cechOpen U x))
  (gX : Fin n → X.functionFieldˣ) (hgX : ∀ i, ∀ y ∈ U i, D.IsLocalEquationAt y (gX i))

include hgX in
/-- The local equation of the first vertex holds on a Čech intersection. -/
theorem cechFirstVertex_isLocalEquationAt {m : ℕ} (x : Fin (m + 1) → Fin n) :
    ∀ y ∈ TopCat.Presheaf.cechOpen U x, D.IsLocalEquationAt y (gX (x 0)) :=
  fun y hy => hgX (x 0) y (TopCat.Presheaf.cechOpen_le U x 0 hy)

/-- **First-vertex trivialization of Čech cochains of `𝒪_X(D)`**, `A`-linearly. -/
noncomputable def cartierCechTrivialization (q : ℕ) :
    TopCat.Presheaf.CechCochain U D.sheaf.presheaf q ≃ₗ[A]
      TopCat.Presheaf.CechCochain U (CohomologyAux.unitModule X).presheaf q :=
  LinearEquiv.piCongrRight fun x =>
    letI := hne x
    (cartierSectionsTrivialization D (TopCat.Presheaf.cechOpen U x) (gX (x 0))
      (cechFirstVertex_isLocalEquationAt D U gX hgX x)).toLinearEquiv fun a s =>
        cartierSectionsTrivialization_smul D _ _ _
          (((X.baseRingToStructurePresheaf A).app (op _)).hom a) s

theorem cartierCechTrivialization_apply (q : ℕ)
    (s : TopCat.Presheaf.CechCochain U D.sheaf.presheaf q) (x : Fin (q + 1) → Fin n) :
    cartierCechTrivialization (A := A) D U hne gX hgX q s x =
      letI := hne x
      cartierSectionsTrivialization D (TopCat.Presheaf.cechOpen U x) (gX (x 0))
        (cechFirstVertex_isLocalEquationAt D U gX hgX x) (s x) :=
  rfl

variable (uX : ∀ i j, Γ(X, U i ⊓ U j))

include hne in
/-- **The Čech differential in first-vertex trivializations**: the face terms are multiplied by
the transition functions. -/
theorem cartierCechTrivialization_cechD
    (huX : ∀ i j, ∀ (_ : Nonempty (U i ⊓ U j : X.Opens)),
      X.germToFunctionField (U i ⊓ U j) (uX i j) * gX j = gX i)
    (q : ℕ) (s : TopCat.Presheaf.CechCochain U D.sheaf.presheaf q) (x : Fin (q + 2) → Fin n) :
    cartierCechTrivialization (A := A) D U hne gX hgX (q + 1) (TopCat.Presheaf.cechD U D.sheaf.presheaf q s) x =
      ∑ k : Fin (q + 2), (-1 : ℤ) ^ (k : ℕ) •
        (X.presheaf.map (homOfLE (cechOpen_le_firstPair U x k)).op
            (uX (x 0) (x (Fin.succAbove k 0))) *
          X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp U x (Fin.succAbove k))).op
            (cartierCechTrivialization (A := A) D U hne gX hgX q s (x ∘ Fin.succAbove k))) := by
  rw [cartierCechTrivialization_apply, TopCat.Presheaf.cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1
  have := hne x
  have := hne (x ∘ Fin.succAbove k)
  have hpair : Nonempty (U (x 0) ⊓ U (x (Fin.succAbove k 0)) : X.Opens) :=
    ⟨⟨(Classical.arbitrary (TopCat.Presheaf.cechOpen U x)).1,
      cechOpen_le_firstPair U x k (Classical.arbitrary (TopCat.Presheaf.cechOpen U x)).2⟩⟩
  have hu : X.germToFunctionField (TopCat.Presheaf.cechOpen U x)
      (X.presheaf.map (homOfLE (cechOpen_le_firstPair U x k)).op
        (uX (x 0) (x (Fin.succAbove k 0)))) * gX (x (Fin.succAbove k 0)) = gX (x 0) := by
    rw [germToFunctionField_restrict (X := X) (cechOpen_le_firstPair U x k)]
    exact huX _ _ hpair
  exact cartierSectionsTrivialization_restrict D
    (TopCat.Presheaf.cechOpen_le_comp U x (Fin.succAbove k)) (gX (x (Fin.succAbove k 0)))
    (gX (x 0)) (cechFirstVertex_isLocalEquationAt D U gX hgX (x ∘ Fin.succAbove k))
    (cechFirstVertex_isLocalEquationAt D U gX hgX x) _ hu (s (x ∘ Fin.succAbove k))

end Trivialization

section BaseChange

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {X Y : Scheme.{u}} [IsIntegral X]
  [IsIntegral Y] [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of L))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of L)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A L))))
  {n : ℕ} (U : Fin n → X.Opens)
  (hU : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), IsAffineOpen (TopCat.Presheaf.cechOpen U x))
  (DX : CartierDivisor X) (DY : CartierDivisor Y)
  (hneX : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n), Nonempty (TopCat.Presheaf.cechOpen U x))
  (hneY : ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x))
  (gX : Fin n → X.functionFieldˣ) (hgX : ∀ i, ∀ y ∈ U i, DX.IsLocalEquationAt y (gX i))
  (gY : Fin n → Y.functionFieldˣ) (hgY : ∀ i, ∀ y ∈ g ⁻¹ᵁ U i, DY.IsLocalEquationAt y (gY i))
  (uX : ∀ i j, Γ(X, U i ⊓ U j))

/-- The transition functions on the fibre: the images of those of the model. -/
noncomputable abbrev baseChangeTransition (i j : Fin n) : Γ(Y, g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j) :=
  g.appLE (U i ⊓ U j) (g ⁻¹ᵁ (U i ⊓ U j)) le_rfl (uX i j)

include H hU in
/-- **Base change of Čech cochains of `𝒪(D)`**, through first-vertex trivializations. -/
noncomputable def cartierCechBaseChangeEquiv (q : ℕ) :
    L ⊗[A] TopCat.Presheaf.CechCochain U DX.sheaf.presheaf q ≃ₗ[L]
      TopCat.Presheaf.CechCochain (fun i => g ⁻¹ᵁ U i) DY.sheaf.presheaf q :=
  ((cartierCechTrivialization (A := A) DX U hneX gX hgX q).baseChange A L _ _).trans
    ((cechStructureBaseChangeEquiv H U hU q).trans
      (cartierCechTrivialization (A := L) DY (fun i => g ⁻¹ᵁ U i) hneY gY hgY q).symm)

omit [IsIntegral X] [IsIntegral Y] in
/-- Base change of a product with a function: `l ⊗ a b ↦ a|_Y · (l ⊗ b)`. -/
theorem sectionsBaseChangeEquiv_tmul_mul {V : X.Opens} (hV : IsAffineOpen V) (l : L)
    (a b : Γ(X, V)) :
    sectionsBaseChangeEquiv H hV (l ⊗ₜ (a * b)) =
      g.appLE V (g ⁻¹ᵁ V) le_rfl a * sectionsBaseChangeEquiv H hV (l ⊗ₜ b) := by
  have h1 : (l ⊗ₜ[A] (a * b) : L ⊗[A] Γ(X, V)) = (1 ⊗ₜ a) * (l ⊗ₜ b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [h1, map_mul, sectionsBaseChangeEquiv_tmul, map_one, one_mul]

omit [IsIntegral X] [IsIntegral Y] in
/-- Restricting a pulled back function. -/
theorem appLE_restrict_apply {V : X.Opens} {W W' : Y.Opens} (e : W ≤ g ⁻¹ᵁ V) (h : W' ≤ W)
    (a : Γ(X, V)) :
    Y.presheaf.map (homOfLE h).op (g.appLE V W e a) = g.appLE V W' (h.trans e) a := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

omit [IsIntegral X] [IsIntegral Y] in
/-- Pulling back a restricted function. -/
theorem appLE_of_restrict_apply {V V' : X.Opens} {W : Y.Opens} (e : W ≤ g ⁻¹ᵁ V') (h : V' ≤ V)
    (a : Γ(X, V)) :
    g.appLE V' W e (X.presheaf.map (homOfLE h).op a) =
      g.appLE V W (e.trans ((Opens.map g.base).monotone h)) a := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

omit [IsIntegral X] [IsIntegral Y] in
/-- The images of a transition function restricted to a Čech intersection agree. -/
theorem baseChangeTransition_restrict {m : ℕ} (x : Fin (m + 2) → Fin n) (k : Fin (m + 2)) :
    Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op
        (g.appLE (TopCat.Presheaf.cechOpen U x) (g ⁻¹ᵁ TopCat.Presheaf.cechOpen U x) le_rfl
          (X.presheaf.map (homOfLE (cechOpen_le_firstPair U x k)).op
            (uX (x 0) (x (Fin.succAbove k 0))))) =
      Y.presheaf.map (homOfLE (cechOpen_le_firstPair (fun i => g ⁻¹ᵁ U i) x k)).op
        (baseChangeTransition U uX (x 0) (x (Fin.succAbove k 0))) := by
  rw [appLE_of_restrict_apply, appLE_restrict_apply]
  exact (appLE_restrict_apply (g := g) (le_rfl : g ⁻¹ᵁ (U (x 0) ⊓ U (x (Fin.succAbove k 0))) ≤ _)
    (cechOpen_le_firstPair (fun i => g ⁻¹ᵁ U i) x k) (uX (x 0) (x (Fin.succAbove k 0)))).symm

include H hU in
/-- **Base change of Čech cochains of `𝒪(D)` commutes with the Čech differentials.** -/
theorem cartierCechBaseChangeEquiv_cechD
    (huX : ∀ i j, ∀ (_ : Nonempty (U i ⊓ U j : X.Opens)),
      X.germToFunctionField (U i ⊓ U j) (uX i j) * gX j = gX i)
    (huY : ∀ i j, ∀ (_ : Nonempty (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j : Y.Opens)),
      Y.germToFunctionField (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j) (baseChangeTransition U uX i j) * gY j = gY i)
    (q : ℕ) (t : L ⊗[A] TopCat.Presheaf.CechCochain U DX.sheaf.presheaf q) :
    cartierCechBaseChangeEquiv H U hU DX DY hneX hneY gX hgX gY hgY (q + 1)
        ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
          q).lTensor L t) =
      TopCat.Presheaf.cechDₗ DY.sheaf.presheaf (presheaf_map_homOfLE_ring_smul L DY.sheaf)
        (fun i => g ⁻¹ᵁ U i) q (cartierCechBaseChangeEquiv H U hU DX DY hneX hneY gX hgX gY hgY q t) := by
  apply (cartierCechTrivialization (A := L) DY (fun i => g ⁻¹ᵁ U i) hneY gY hgY (q + 1)).injective
  induction t using TensorProduct.inductionOn with
  | tmul l s =>
    funext x
    simp only [cartierCechBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      LinearMap.lTensor_tmul, LinearEquiv.baseChange_tmul, TopCat.Presheaf.cechDₗ_apply]
    rw [cechStructureBaseChangeEquiv_tmul,
      cartierCechTrivialization_cechD (A := A) DX U hneX gX hgX uX huX,
      cartierCechTrivialization_cechD (A := L) DY (fun i => g ⁻¹ᵁ U i) hneY gY hgY
        (baseChangeTransition U uX) huY,
      TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, map_zsmul, map_zsmul, sectionsBaseChangeEquiv_tmul_mul,
      map_mul, LinearEquiv.apply_symm_apply, cechStructureBaseChangeEquiv_tmul,
      sectionsBaseChangeEquiv_tmul_restrict H (hU (x ∘ Fin.succAbove k)) (hU x),
      baseChangeTransition_restrict]
    congr 2
    exact structure_map_map_eq Y _ _ _ _ _
  | add t t' ht ht' => rw [map_add, map_add, map_add, ht, ht', map_add, map_add, map_add]

include H hU hneX hneY hgX hgY in
/-- **Exactness of the base change of the Čech complex of `𝒪(D)` is exactness of the Čech complex
of `𝒪(D)` on the fibre.** -/
theorem exact_lTensor_cartierCech_iff
    (huX : ∀ i j, ∀ (_ : Nonempty (U i ⊓ U j : X.Opens)),
      X.germToFunctionField (U i ⊓ U j) (uX i j) * gX j = gX i)
    (huY : ∀ i j, ∀ (_ : Nonempty (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j : Y.Opens)),
      Y.germToFunctionField (g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j) (baseChangeTransition U uX i j) * gY j = gY i)
    (q : ℕ) :
    Function.Exact
        ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
          q).lTensor L)
        ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
          (q + 1)).lTensor L) ↔
      Function.Exact
        (TopCat.Presheaf.cechDₗ DY.sheaf.presheaf (presheaf_map_homOfLE_ring_smul L DY.sheaf)
          (fun i => g ⁻¹ᵁ U i) q)
        (TopCat.Presheaf.cechDₗ DY.sheaf.presheaf (presheaf_map_homOfLE_ring_smul L DY.sheaf)
          (fun i => g ⁻¹ᵁ U i) (q + 1)) :=
  (Function.Exact.iff_of_ladder_addEquiv
    (cartierCechBaseChangeEquiv H U hU DX DY hneX hneY gX hgX gY hgY q).toAddEquiv
    (cartierCechBaseChangeEquiv H U hU DX DY hneX hneY gX hgX gY hgY (q + 1)).toAddEquiv
    (cartierCechBaseChangeEquiv H U hU DX DY hneX hneY gX hgX gY hgY (q + 1 + 1)).toAddEquiv
    (f₁₂ := ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
      q).lTensor L).toAddMonoidHom)
    (f₂₃ := ((TopCat.Presheaf.cechDₗ DX.sheaf.presheaf (presheaf_map_homOfLE_ring_smul A DX.sheaf) U
      (q + 1)).lTensor L).toAddMonoidHom)
    (g₁₂ := (TopCat.Presheaf.cechDₗ DY.sheaf.presheaf (presheaf_map_homOfLE_ring_smul L DY.sheaf)
      (fun i => g ⁻¹ᵁ U i) q).toAddMonoidHom)
    (g₂₃ := (TopCat.Presheaf.cechDₗ DY.sheaf.presheaf (presheaf_map_homOfLE_ring_smul L DY.sheaf)
      (fun i => g ⁻¹ᵁ U i) (q + 1)).toAddMonoidHom)
    (AddMonoidHom.ext fun t =>
      (cartierCechBaseChangeEquiv_cechD H U hU DX DY hneX hneY gX hgX gY hgY uX huX huY q t).symm)
    (AddMonoidHom.ext fun t =>
      (cartierCechBaseChangeEquiv_cechD H U hU DX DY hneX hneY gX hgX gY hgY uX huX huY (q + 1)
        t).symm)).symm

end BaseChange

end MixedFujita
