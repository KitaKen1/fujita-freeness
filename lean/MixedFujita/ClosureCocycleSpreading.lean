/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosureTransition
public import MixedFujita.CartierAtlasCocycle
public import MixedFujita.DominantCartierPullback
public import MixedFujita.ProjectiveClosureProperties

/-!
Spreading units and cocycles to the closure (step 10, R4-3).

Pulling back functions along a dominant morphism of integral schemes is injective
(`appLE_injective_of_isDominant`, through the map of function fields of check
`DominantCartierPullback`). The map `φ_A : T → T_A` to the closure is dominant
(`projectiveClosureMap_isDominant`) and `T_A` is integral, so identities among functions on `T_A`
can be checked on `T`, without flatness.

With the transition maps `ρ : T_A → T_B` of check 533, for a base `B` with `T = T_B ×_B K`:
* `exists_fg_forall_unit_closureTransition`: finitely many units on the preimage in `T` of an
  affine open `W ⊆ T_B` come from units on `ρ⁻¹W ⊆ T_A` for all large `A` (spread the units and
  their inverses; the product is `1` on `T_A` by injectivity);
* `exists_fg_forall_cocycle_closureTransition`: a cocycle of units on the preimages in `T` of a
  cover of `T_B` with affine double intersections spreads to a cocycle on `T_A` (check 529), the
  cocycle condition again by injectivity on the triple intersections.

This gives the divisor `Q_A` on `T_A` (check 529) from the transition units of `Q` (check 534).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- **Pulling back functions along a dominant morphism of integral schemes is injective.** -/
theorem appLE_injective_of_isDominant {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (φ : Y ⟶ X)
    [IsDominant φ] {V : X.Opens} {W : Y.Opens} [Nonempty V] [Nonempty W] (h : W ≤ φ ⁻¹ᵁ V) :
    Function.Injective (φ.appLE V W h) := by
  intro a b hab
  apply Scheme.germToFunctionField_injective X V
  apply (dominantFunctionFieldMap φ).hom.injective
  rw [dominantFunctionFieldMap_germ φ V W h, dominantFunctionFieldMap_germ φ V W h, hab]

variable {n : ℕ} {K : Type u} [Field K] {T : Scheme.{u}} (e : T ⟶ polynomialProjectiveScheme n K)

/-- The map to the closure is dominant. -/
theorem projectiveClosureMap_isDominant [IsClosedImmersion e] {A : Type u} [CommRing A]
    (c : A →+* K) : IsDominant (projectiveClosureMap c e) := by
  have := polynomialProjectiveCoefficientMap_isAffineHom (n := n) c
  infer_instance

/-- The closure of an integral closed subscheme is integral. -/
theorem projectiveClosure_isIntegral_of_isClosedImmersion [IsIntegral T] [IsClosedImmersion e]
    {A : Type u} [CommRing A] (c : A →+* K) : IsIntegral (projectiveClosure c e) := by
  have := polynomialProjectiveCoefficientMap_isAffineHom (n := n) c
  exact projectiveClosure_isIntegral c e

/-- **Units on the preimage of an affine open of a model closure come from units on every larger
closure.** -/
theorem exists_fg_forall_unit_closureTransition [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
    [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = T ↘ Spec (CommRingCat.of K)) (B : Subalgebra ℤ K)
    (HB : IsPullback (projectiveClosureMap (algebraMap B K) e) (T ↘ Spec (CommRingCat.of K))
      (projectiveClosureι (algebraMap B K) e ≫ polynomialProjectiveToBase n B)
      (Spec.map (CommRingCat.ofHom (algebraMap B K))))
    {W : (projectiveClosure (algebraMap B K) e).Opens} (hW : IsAffineOpen W)
    [Nonempty (projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W)]
    (S : Finset Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W)ˣ) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ (A : Subalgebra ℤ K) (hBA : B ≤ A), A₀ ≤ A → ∀ s ∈ S,
      ∃ t : Γ(projectiveClosure (algebraMap A K) e, closureTransitionOfLE e hBA ⁻¹ᵁ W)ˣ,
        (projectiveClosureMap (algebraMap A K) e).appLE _ _
          (projectiveClosureMap_preimage_closureTransitionOfLE e hBA W).ge
          (t : Γ(projectiveClosure (algebraMap A K) e, closureTransitionOfLE e hBA ⁻¹ᵁ W)) = s := by
  classical
  obtain ⟨A₀, hA₀, h⟩ := exists_fg_forall_mem_range_closureTransition_appLE e he B HB hW
    (S.image (fun s : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W)ˣ =>
        (s : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W))) ∪
      S.image (fun s : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W)ˣ =>
        ((s⁻¹ : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W)ˣ) :
          Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W))))
  refine ⟨A₀, hA₀, fun A hBA hA s hs => ?_⟩
  obtain ⟨t₁, ht₁⟩ := h A hBA hA _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs))
  obtain ⟨t₂, ht₂⟩ := h A hBA hA _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))
  have := projectiveClosure_isIntegral_of_isClosedImmersion e (algebraMap A K)
  have := projectiveClosureMap_isDominant e (algebraMap A K)
  have hne : Nonempty (closureTransitionOfLE e hBA ⁻¹ᵁ W) := by
    obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty (projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W))
    exact ⟨⟨projectiveClosureMap (algebraMap A K) e y,
      (projectiveClosureMap_preimage_closureTransitionOfLE e hBA W).ge hy⟩⟩
  have hinj := appLE_injective_of_isDominant (projectiveClosureMap (algebraMap A K) e)
    (projectiveClosureMap_preimage_closureTransitionOfLE e hBA W).ge
  have h12 : t₁ * t₂ = 1 := hinj (by rw [map_mul, ht₁, ht₂, map_one, Units.mul_inv])
  exact ⟨⟨t₁, t₂, h12, by rw [mul_comm]; exact h12⟩, ht₁⟩

/-- **A cocycle of units spreads to every larger closure.** -/
theorem exists_fg_forall_cocycle_closureTransition [IsIntegral T]
    [T.Over (Spec (CommRingCat.of K))] [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = T ↘ Spec (CommRingCat.of K)) (B : Subalgebra ℤ K)
    (HB : IsPullback (projectiveClosureMap (algebraMap B K) e) (T ↘ Spec (CommRingCat.of K))
      (projectiveClosureι (algebraMap B K) e ≫ polynomialProjectiveToBase n B)
      (Spec.map (CommRingCat.ofHom (algebraMap B K))))
    {N : ℕ} (U : Fin (N + 1) → (projectiveClosure (algebraMap B K) e).Opens)
    (hU : ∀ i j, IsAffineOpen (U i ⊓ U j))
    [hne : ∀ i, Nonempty (projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ U i)]
    (w : ∀ i j, Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ U i ⊓
      projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ U j)ˣ)
    (hw : IsCocycleZero (fun i => projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ U i) w) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ (A : Subalgebra ℤ K) (hBA : B ≤ A), A₀ ≤ A →
      ∃ wA : ∀ i j, Γ(projectiveClosure (algebraMap A K) e,
          closureTransitionOfLE e hBA ⁻¹ᵁ U i ⊓ closureTransitionOfLE e hBA ⁻¹ᵁ U j)ˣ,
        IsCocycleZero (fun i => closureTransitionOfLE e hBA ⁻¹ᵁ U i) wA ∧
          ∀ i j, (projectiveClosureMap (algebraMap A K) e).appLE _ _
            (projectiveClosureMap_preimage_closureTransitionOfLE e hBA (U i ⊓ U j)).ge
            (wA i j : Γ(projectiveClosure (algebraMap A K) e,
              closureTransitionOfLE e hBA ⁻¹ᵁ U i ⊓ closureTransitionOfLE e hBA ⁻¹ᵁ U j)) =
            (w i j : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ U i ⊓
              projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ U j)) := by
  classical
  let φB := projectiveClosureMap (algebraMap B K) e
  have hne2 : ∀ i j, Nonempty (φB ⁻¹ᵁ (U i ⊓ U j)) := fun i j =>
    integral_opens_inter_nonempty T (φB ⁻¹ᵁ U i) (φB ⁻¹ᵁ U j)
  -- spread each transition unit
  have hspread := fun p : Fin (N + 1) × Fin (N + 1) =>
    @exists_fg_forall_unit_closureTransition n K _ T e _ _ _ he B HB (U p.1 ⊓ U p.2) (hU p.1 p.2)
      (hne2 p.1 p.2) {w p.1 p.2}
  choose A₀ hA₀ hA₀' using hspread
  choose C hC using fun p => hA₀ p
  let D : Finset K := Finset.univ.biUnion C
  refine ⟨Algebra.adjoin ℤ (D : Set K), ⟨D, rfl⟩, fun A hBA hA => ?_⟩
  have hAp : ∀ p, A₀ p ≤ A := by
    intro p
    rw [← hC p, Algebra.adjoin_le_iff]
    intro z hz
    exact hA (Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_biUnion.2
      ⟨p, Finset.mem_univ _, Finset.mem_coe.1 hz⟩)))
  choose wA' hwA' using fun i j =>
    hA₀' (i, j) A hBA (hAp (i, j)) (w i j) (Finset.mem_singleton_self _)
  let φA := projectiveClosureMap (algebraMap A K) e
  let ρ := closureTransitionOfLE e hBA
  obtain ⟨wA, hwA⟩ : ∃ wA : ∀ i j, Γ(projectiveClosure (algebraMap A K) e,
      ρ ⁻¹ᵁ U i ⊓ ρ ⁻¹ᵁ U j)ˣ, ∀ i j, φA.appLE _ _
        (projectiveClosureMap_preimage_closureTransitionOfLE e hBA (U i ⊓ U j)).ge
        (wA i j : Γ(projectiveClosure (algebraMap A K) e, ρ ⁻¹ᵁ U i ⊓ ρ ⁻¹ᵁ U j)) =
        (w i j : Γ(T, φB ⁻¹ᵁ U i ⊓ φB ⁻¹ᵁ U j)) :=
    ⟨fun i j => wA' i j, fun i j => hwA' i j⟩
  refine ⟨wA, fun i j => ?_, hwA⟩
  -- the cocycle condition, checked on `T`
  have := projectiveClosure_isIntegral_of_isClosedImmersion e (algebraMap A K)
  have := projectiveClosureMap_isDominant e (algebraMap A K)
  have hpre : ∀ k, φB ⁻¹ᵁ U k ≤ φA ⁻¹ᵁ (ρ ⁻¹ᵁ U k) := fun k =>
    (projectiveClosureMap_preimage_closureTransitionOfLE e hBA (U k)).ge
  let _ := integral_opens_inter_nonempty T (φB ⁻¹ᵁ U i) (φB ⁻¹ᵁ U j)
  have hTne : Nonempty (φB ⁻¹ᵁ U i ⊓ φB ⁻¹ᵁ U j ⊓ φB ⁻¹ᵁ U 0 : T.Opens) :=
    integral_opens_inter_nonempty T _ _
  have hle : φB ⁻¹ᵁ U i ⊓ φB ⁻¹ᵁ U j ⊓ φB ⁻¹ᵁ U 0 ≤
      φA ⁻¹ᵁ (ρ ⁻¹ᵁ U i ⊓ ρ ⁻¹ᵁ U j ⊓ ρ ⁻¹ᵁ U 0) := fun y hy =>
    ⟨⟨hpre i hy.1.1, hpre j hy.1.2⟩, hpre 0 hy.2⟩
  have hAne : Nonempty (ρ ⁻¹ᵁ U i ⊓ ρ ⁻¹ᵁ U j ⊓ ρ ⁻¹ᵁ U 0 : _) := by
    obtain ⟨⟨y, hy⟩⟩ := hTne
    exact ⟨⟨φA y, hle hy⟩⟩
  apply appLE_injective_of_isDominant φA hle
  rw [map_mul, appLE_of_restrict_apply, appLE_of_restrict_apply, appLE_of_restrict_apply]
  have key : ∀ (k l : Fin (N + 1))
      (h' : φB ⁻¹ᵁ U i ⊓ φB ⁻¹ᵁ U j ⊓ φB ⁻¹ᵁ U 0 ≤ φB ⁻¹ᵁ U k ⊓ φB ⁻¹ᵁ U l)
      (e' : φB ⁻¹ᵁ U i ⊓ φB ⁻¹ᵁ U j ⊓ φB ⁻¹ᵁ U 0 ≤ φA ⁻¹ᵁ (ρ ⁻¹ᵁ U k ⊓ ρ ⁻¹ᵁ U l)),
      φA.appLE (ρ ⁻¹ᵁ U k ⊓ ρ ⁻¹ᵁ U l) _ e'
          (wA k l : Γ(projectiveClosure (algebraMap A K) e, ρ ⁻¹ᵁ U k ⊓ ρ ⁻¹ᵁ U l)) =
        T.presheaf.map (homOfLE h').op (w k l : Γ(T, φB ⁻¹ᵁ U k ⊓ φB ⁻¹ᵁ U l)) := by
    intro k l h' e'
    rw [← hwA k l]
    exact (appLE_restrict_apply (g := φA) _ h' _).symm
  rw [key i j inf_le_left, key j 0 (le_inf (inf_le_left.trans inf_le_right) inf_le_right),
    key i 0 (le_inf (inf_le_left.trans inf_le_left) inf_le_right)]
  exact hw i j

end MixedFujita
