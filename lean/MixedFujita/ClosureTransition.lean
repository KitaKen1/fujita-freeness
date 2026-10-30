/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ClosureChartSpreading
public import MixedFujita.ProjectiveClosureBaseChange
public import MixedFujita.AffineSectionsBaseChange

/-!
Transition maps between the closures over nested subrings (step 10, R4-3).

Let `e : T → ℙ_S` be a morphism and `c : B → S`, `c' : A → S`, `c₁ : B → A` ring maps with
`c' ∘ c₁ = c` (for subrings `B ⊆ A` of a field `K`). The coefficient maps of projective space
compose (`polynomialProjectiveCoefficientMap_comp`), so the closure `T_A` maps to the closure `T_B`
over `ℙ_A → ℙ_B` (`closureTransition`, Mathlib's `subschemeMap`). The map is compatible with the
maps from `T` (`projectiveClosureMap_comp_closureTransition`) and with the bases
(`closureTransition_toBase`), is affine (`closureTransition_isAffineHom`) and pulls the standard
charts back to the standard charts (`closureTransition_preimage_chart`).

Opens of one closure `T_B` thus give opens of every larger closure `T_A`, and functions on them
spread (`exists_fg_forall_mem_range_closureTransition_appLE`): when `T = T_B ×_B K`, a function on
the preimage in `T` of an affine open `W ⊆ T_B` is `Σ k_l · b_l` with `b_l` on `W` (check 497), so it
comes from `T_A` once `A` contains the `k_l`. This covers the functions on intersections of charts
lying in different standard charts, such as transition functions and units.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra structureSectionsAlgebra

universe u

variable {n : ℕ}

/-- The graded coefficient maps compose. -/
theorem polynomialScalarGradedMap_comp {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S']
    (c₁ : R →+* S) (c₂ : S →+* S') :
    polynomialScalarGradedMap (n := n) (c₂.comp c₁) =
      (polynomialScalarGradedMap c₂).comp (polynomialScalarGradedMap c₁) := by
  refine GradedRingHom.ext fun p => ?_
  change MvPolynomial.map (c₂.comp c₁) p = MvPolynomial.map c₂ (MvPolynomial.map c₁ p)
  rw [MvPolynomial.map_map]

/-- **The coefficient maps of projective space compose.** -/
theorem polynomialProjectiveCoefficientMap_comp {R S S' : Type u} [CommRing R] [CommRing S]
    [CommRing S'] (c₁ : R →+* S) (c₂ : S →+* S') :
    polynomialProjectiveCoefficientMap (n := n) (c₂.comp c₁) =
      polynomialProjectiveCoefficientMap c₂ ≫ polynomialProjectiveCoefficientMap c₁ := by
  unfold polynomialProjectiveCoefficientMap
  rw [← Proj.map_comp]
  congr 1
  exact polynomialScalarGradedMap_comp c₁ c₂

/-- Morphisms that are equal have equal `appLE`. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- **Pulling back a constant** along a morphism over a map of bases. -/
theorem appLE_algebraMap_of_comp {R L : Type u} [CommRing R] [CommRing L] [Algebra R L]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of R))] [Y.Over (Spec (CommRingCat.of L))]
    (g : Y ⟶ X) (hg : g ≫ (X ↘ Spec (CommRingCat.of R)) =
      (Y ↘ Spec (CommRingCat.of L)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R L)))
    {V : X.Opens} {W : Y.Opens} (h : W ≤ g ⁻¹ᵁ V) (a : R) :
    g.appLE V W h (algebraMap R Γ(X, V) a) = algebraMap L Γ(Y, W) (algebraMap R L a) := by
  have e1 := ConcreteCategory.congr_hom (structureSections_algebraMap R X V) a
  have e2 := ConcreteCategory.congr_hom (structureSections_algebraMap L Y W) (algebraMap R L a)
  simp only [CommRingCat.hom_ofHom] at e1 e2
  rw [e1, e2, ← ConcreteCategory.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom hg, Scheme.Hom.comp_appLE, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc, ConcreteCategory.comp_apply]
  rfl

section Transition

variable {B A S : Type u} [CommRing B] [CommRing A] [CommRing S] {Y : Scheme.{u}}
  (e : Y ⟶ polynomialProjectiveScheme n S) (c : B →+* S) (c' : A →+* S) (c₁ : B →+* A)

/-- The kernel condition for the transition map: the image of `T_A` in `ℙ_B` is `T_B`. -/
theorem closureTransition_le_map (hc : c'.comp c₁ = c) :
    (e ≫ polynomialProjectiveCoefficientMap c).ker ≤
      (e ≫ polynomialProjectiveCoefficientMap c').ker.map
        (polynomialProjectiveCoefficientMap c₁) := by
  rw [Scheme.IdealSheafData.map_ker, Category.assoc, ← polynomialProjectiveCoefficientMap_comp, hc]

/-- **The closure over `A` maps to the closure over `B`** over the coefficient map `ℙ_A → ℙ_B`. -/
noncomputable def closureTransition (hc : c'.comp c₁ = c) :
    projectiveClosure c' e ⟶ projectiveClosure c e :=
  Scheme.IdealSheafData.subschemeMap _ _ (polynomialProjectiveCoefficientMap c₁)
    (closureTransition_le_map e c c' c₁ hc)

theorem closureTransition_ι (hc : c'.comp c₁ = c) :
    closureTransition e c c' c₁ hc ≫ projectiveClosureι c e =
      projectiveClosureι c' e ≫ polynomialProjectiveCoefficientMap c₁ :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- The transition map is compatible with the maps from `Y`. -/
theorem projectiveClosureMap_comp_closureTransition (hc : c'.comp c₁ = c) :
    projectiveClosureMap c' e ≫ closureTransition e c c' c₁ hc = projectiveClosureMap c e := by
  rw [← cancel_mono (projectiveClosureι c e), Category.assoc, closureTransition_ι,
    ← Category.assoc, projectiveClosureMap_comp_ι, projectiveClosureMap_comp_ι, Category.assoc,
    ← polynomialProjectiveCoefficientMap_comp, hc]

/-- The transition map lies over `Spec A → Spec B`. -/
theorem closureTransition_toBase (hc : c'.comp c₁ = c) :
    closureTransition e c c' c₁ hc ≫ projectiveClosureι c e ≫ polynomialProjectiveToBase n B =
      (projectiveClosureι c' e ≫ polynomialProjectiveToBase n A) ≫
        Spec.map (CommRingCat.ofHom c₁) := by
  rw [← Category.assoc, closureTransition_ι, Category.assoc,
    polynomialProjectiveCoefficientMap_toBase, Category.assoc]

/-- The transition map is affine. -/
theorem closureTransition_isAffineHom (hc : c'.comp c₁ = c) :
    IsAffineHom (closureTransition e c c' c₁ hc) := by
  have := polynomialProjectiveCoefficientMap_isAffineHom (n := n) c₁
  have h : IsAffineHom (closureTransition e c c' c₁ hc ≫ projectiveClosureι c e) := by
    rw [closureTransition_ι]
    infer_instance
  exact IsAffineHom.comp_iff.1 h

/-- The transition map pulls the standard charts back to the standard charts. -/
theorem closureTransition_preimage_chart (hc : c'.comp c₁ = c) (k : Fin n) :
    closureTransition e c c' c₁ hc ⁻¹ᵁ
        projectivePullbackCoordinateOpen (projectiveClosureι c e) k =
      projectivePullbackCoordinateOpen (projectiveClosureι c' e) k := by
  rw [projectivePullbackCoordinateOpen, projectivePullbackCoordinateOpen,
    ← Scheme.Hom.comp_preimage, closureTransition_ι, Scheme.Hom.comp_preimage,
    polynomialProjectiveCoefficientMap_preimage_coordinate]

end Transition

section Spreading

variable {K : Type u} [Field K] {T : Scheme.{u}} (e : T ⟶ polynomialProjectiveScheme n K)

/-- The map from a closure to `Spec A` lies over `T → Spec K`. -/
theorem projectiveClosureMap_comp_toBase [T.Over (Spec (CommRingCat.of K))] {A : Type u}
    [CommRing A] (c : A →+* K)
    (he : e ≫ polynomialProjectiveToBase n K = T ↘ Spec (CommRingCat.of K)) :
    projectiveClosureMap c e ≫ projectiveClosureι c e ≫ polynomialProjectiveToBase n A =
      (T ↘ Spec (CommRingCat.of K)) ≫ Spec.map (CommRingCat.ofHom c) := by
  rw [← Category.assoc, projectiveClosureMap_comp_ι, Category.assoc,
    polynomialProjectiveCoefficientMap_toBase, ← Category.assoc, he]

/-- The transition map between the closures over subrings `B ≤ A` of `K`. -/
noncomputable def closureTransitionOfLE {B A : Subalgebra ℤ K} (h : B ≤ A) :
    projectiveClosure (algebraMap A K) e ⟶ projectiveClosure (algebraMap B K) e :=
  closureTransition e (algebraMap B K) (algebraMap A K) (Subalgebra.inclusion h).toRingHom
    (RingHom.ext fun _ => rfl)

theorem projectiveClosureMap_comp_closureTransitionOfLE {B A : Subalgebra ℤ K} (h : B ≤ A) :
    projectiveClosureMap (algebraMap A K) e ≫ closureTransitionOfLE e h =
      projectiveClosureMap (algebraMap B K) e :=
  projectiveClosureMap_comp_closureTransition e _ _ _ _

theorem projectiveClosureMap_preimage_closureTransitionOfLE {B A : Subalgebra ℤ K} (h : B ≤ A)
    (W : (projectiveClosure (algebraMap B K) e).Opens) :
    projectiveClosureMap (algebraMap A K) e ⁻¹ᵁ (closureTransitionOfLE e h ⁻¹ᵁ W) =
      projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W := by
  rw [← Scheme.Hom.comp_preimage, projectiveClosureMap_comp_closureTransitionOfLE]

/-- **Functions on the preimage of an affine open of a model closure come from every larger
closure** that contains finitely many more elements of `K`. -/
theorem exists_fg_forall_mem_range_closureTransition_appLE [T.Over (Spec (CommRingCat.of K))]
    (he : e ≫ polynomialProjectiveToBase n K = T ↘ Spec (CommRingCat.of K)) (B : Subalgebra ℤ K)
    (HB : IsPullback (projectiveClosureMap (algebraMap B K) e) (T ↘ Spec (CommRingCat.of K))
      (projectiveClosureι (algebraMap B K) e ≫ polynomialProjectiveToBase n B)
      (Spec.map (CommRingCat.ofHom (algebraMap B K))))
    {W : (projectiveClosure (algebraMap B K) e).Opens} (hW : IsAffineOpen W)
    (S : Finset Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W)) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ (A : Subalgebra ℤ K) (hBA : B ≤ A), A₀ ≤ A → ∀ s ∈ S,
      ∃ t : Γ(projectiveClosure (algebraMap A K) e, closureTransitionOfLE e hBA ⁻¹ᵁ W),
        (projectiveClosureMap (algebraMap A K) e).appLE _ _
          (projectiveClosureMap_preimage_closureTransitionOfLE e hBA W).ge t = s := by
  classical
  let _ : (projectiveClosure (algebraMap B K) e).Over (Spec (CommRingCat.of B)) :=
    ⟨projectiveClosureι (algebraMap B K) e ≫ polynomialProjectiveToBase n B⟩
  -- every element of `K ⊗_B Γ(T_B, W)` spreads
  have key : ∀ x : K ⊗[B] Γ(projectiveClosure (algebraMap B K) e, W), ∃ C : Finset K,
      ∀ (A : Subalgebra ℤ K) (hBA : B ≤ A), (C : Set K) ⊆ A →
        ∃ t : Γ(projectiveClosure (algebraMap A K) e, closureTransitionOfLE e hBA ⁻¹ᵁ W),
          (projectiveClosureMap (algebraMap A K) e).appLE _ _
            (projectiveClosureMap_preimage_closureTransitionOfLE e hBA W).ge t =
            sectionsBaseChangeEquiv HB hW x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul k b =>
      refine ⟨{k}, fun A hBA hC => ?_⟩
      have hk : k ∈ A := hC (Finset.mem_coe.2 (Finset.mem_singleton_self k))
      let _ : (projectiveClosure (algebraMap A K) e).Over (Spec (CommRingCat.of A)) :=
        ⟨projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase n A⟩
      refine ⟨algebraMap A _ ⟨k, hk⟩ * (closureTransitionOfLE e hBA).appLE W _ le_rfl b, ?_⟩
      rw [map_mul, sectionsBaseChangeEquiv_tmul]
      congr 1
      · exact appLE_algebraMap_of_comp _ (projectiveClosureMap_comp_toBase e (algebraMap A K) he)
          _ ⟨k, hk⟩
      · rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE,
          appLE_congr_hom (projectiveClosureMap_comp_closureTransitionOfLE e hBA)]
    | add x y hx hy =>
      obtain ⟨C₁, hC₁⟩ := hx
      obtain ⟨C₂, hC₂⟩ := hy
      refine ⟨C₁ ∪ C₂, fun A hBA hC => ?_⟩
      obtain ⟨t₁, ht₁⟩ := hC₁ A hBA fun z hz =>
        hC (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hz)))
      obtain ⟨t₂, ht₂⟩ := hC₂ A hBA fun z hz =>
        hC (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 hz)))
      exact ⟨t₁ + t₂, by rw [map_add, ht₁, ht₂, map_add]⟩
  choose x hx using fun s : Γ(T, projectiveClosureMap (algebraMap B K) e ⁻¹ᵁ W) =>
    (sectionsBaseChangeEquiv HB hW).surjective s
  choose C hC using fun s => key (x s)
  let D : Finset K := S.biUnion fun s => C s
  refine ⟨Algebra.adjoin ℤ (D : Set K), ⟨D, rfl⟩, fun A hBA hA s hs => ?_⟩
  obtain ⟨t, ht⟩ := hC s A hBA fun z hz =>
    hA (Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_coe.1 hz⟩)))
  exact ⟨t, ht.trans (hx s)⟩

end Spreading

end MixedFujita
