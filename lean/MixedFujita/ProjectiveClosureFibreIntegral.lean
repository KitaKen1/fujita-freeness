/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreGlobalSectionsRank
public import MixedFujita.ConnectedSmoothIntegral
public import MixedFujita.ProjectiveClosureBaseChange
public import MixedFujita.ProjectiveClosureProperties

/-!
The fibres of the closure of a smooth projective variety are integral (step 10, R4-3).

* `finite_globalSections_of_isProper`: the global functions of a scheme proper over a noetherian
  ring are a finite module (SGA's finiteness in degree zero).
* `finrank_globalSections_eq_one_of_isAlgClosed`: a proper integral scheme over an algebraically
  closed field `K` has `Γ(X, O) = K` (a finite-dimensional domain over `K`).
* `exists_fg_forall_exists_ne_zero_isIntegral_fibre`: let `T` be a smooth integral closed subscheme
  of projective space over an algebraically closed field `K`. There is a finitely generated
  subring `A₀ ⊆ K` such that for every finitely generated `A ⊇ A₀` there is `f ≠ 0` in `A` with:
  every fibre of the closure `T_A` over a field in which `f` is a unit is integral. By check 516,
  `dim Γ(T_κ, O) = dim Γ(T, O) = 1` (using `T = T_A ×_A K`, check 510); so `T_κ` is connected,
  and it is smooth over `κ`, hence integral (check 515).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] sectionsRingModule

section GlobalSections

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))]

/-- The global functions of a scheme proper over a noetherian ring are a finite module. -/
theorem finite_globalSections_of_isProper [IsLocallyNoetherian X]
    [IsProper (X ↘ Spec (CommRingCat.of A))] :
    Module.Finite A ((CohomologyAux.unitModule X).presheaf.obj (op ⊤)) := by
  let M := CohomologyAux.unitModule X
  have := proper_coherent_cohomology_finite A M 0
  have e1 := Scheme.Modules.cohomologyZeroBaseLinearEquiv A X M
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
  exact hinst ▸ hfin

end GlobalSections

section AlgClosed

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of K))]

/-- **A proper integral scheme over an algebraically closed field has only constant global
functions.** -/
theorem finrank_globalSections_eq_one_of_isAlgClosed [IsIntegral X] [IsLocallyNoetherian X]
    [IsProper (X ↘ Spec (CommRingCat.of K))] :
    Module.finrank K ((CohomologyAux.unitModule X).presheaf.obj (op ⊤)) = 1 := by
  have hfin := finite_globalSections_of_isProper (A := K) (X := X)
  let _ := structureSectionsAlgebra K X ⊤
  have : Module.Finite K Γ(X, ⊤) := hfin
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := Γ(X, ⊤))
  change Module.finrank K Γ(X, ⊤) = 1
  rw [← (LinearEquiv.ofBijective (Algebra.linearMap K Γ(X, ⊤)) hbij).finrank_eq,
    Module.finrank_self]

end AlgClosed

section Fibre

variable {n : ℕ} {K : Type u} [Field K] [IsAlgClosed K] {T : Scheme.{u}} [IsIntegral T]
  (π : T ⟶ Spec (CommRingCat.of K)) (d : ℕ) (e : T ⟶ polynomialProjectiveScheme n K)

/-- **The fibres of the closure of a smooth integral projective variety are integral.** -/
theorem exists_fg_forall_exists_ne_zero_isIntegral_fibre [SmoothOfRelativeDimension d π]
    [IsClosedImmersion e] (he : e ≫ polynomialProjectiveToBase n K = π) :
    ∃ A₀ : Subalgebra ℤ K, A₀.FG ∧ ∀ A : Subalgebra ℤ K, A₀ ≤ A → A.FG →
      ∃ f : A, f ≠ 0 ∧ ∀ (κ : Type u) [Field κ] [Algebra A κ], IsUnit (algebraMap A κ f) →
        IsIntegral (pullback
          (projectiveClosureι (algebraMap A K) e ≫ polynomialProjectiveToBase n A)
          (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) := by
  classical
  obtain ⟨A₁, ⟨s₁, hs₁⟩, h₁⟩ := exists_fg_forall_smoothOfRelativeDimension_projectiveClosure π d e he
  obtain ⟨A₂, ⟨s₂, hs₂⟩, h₂⟩ := exists_fg_forall_isPullback_projectiveClosure π e he
  refine ⟨Algebra.adjoin ℤ ((s₁ ∪ s₂ : Finset K) : Set K), ⟨_, rfl⟩, fun A hA hAfg => ?_⟩
  have hA₁ : A₁ ≤ A := by
    rw [← hs₁]
    exact (Algebra.adjoin_mono (by simp)).trans hA
  have hA₂ : A₂ ≤ A := by
    rw [← hs₂]
    exact (Algebra.adjoin_mono (by simp)).trans hA
  have : Algebra.FiniteType ℤ A := (Subalgebra.fg_iff_finiteType A).1 hAfg
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let c := algebraMap A K
  let ι := projectiveClosureι c e
  let q := ι ≫ polynomialProjectiveToBase n A
  have hsm : SmoothOfRelativeDimension d q := h₁ A hA₁
  have : IsProper q := projectiveClosure_toBase_isProper c e
  have := projectiveClosure_isAffineHom_diagonal c e
  let _ : (projectiveClosure c e).Over (Spec (CommRingCat.of A)) := ⟨q⟩
  have : Smooth (projectiveClosure c e ↘ Spec (CommRingCat.of A)) :=
    SmoothOfRelativeDimension.smooth d q
  have : IsProper (projectiveClosure c e ↘ Spec (CommRingCat.of A)) :=
    projectiveClosure_toBase_isProper c e
  have : IsLocallyNoetherian (projectiveClosure c e) := LocallyOfFiniteType.isLocallyNoetherian q
  obtain ⟨f, hf, r, hr⟩ := exists_ne_zero_finrank_globalSections_fibre (A := A)
    (X := projectiveClosure c e) (fun k => projectivePullbackCoordinateOpen ι k)
    (fun k => projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion ι k)
    (iSup_projectivePullbackCoordinateOpen ι)
  -- the rank is one, by the generic fibre
  have hr1 : r = 1 := by
    let _ : T.Over (Spec (CommRingCat.of K)) := ⟨π⟩
    have : IsProper π := by
      rw [← he]
      have := polynomialProjectiveToBase_isProper n K
      infer_instance
    have : IsProper (T ↘ Spec (CommRingCat.of K)) := this
    have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian π
    have hK : IsUnit (algebraMap A K f) :=
      isUnit_iff_ne_zero.2 fun h => hf (Subtype.val_injective h)
    rw [← hr K hK T (projectiveClosureMap c e) (h₂ A hA₂)]
    exact finrank_globalSections_eq_one_of_isAlgClosed
  refine ⟨f, hf, fun κ _ _ hκ => ?_⟩
  let Y := pullback q (Spec.map (CommRingCat.ofHom (algebraMap A κ)))
  let _ : Y.Over (Spec (CommRingCat.of κ)) := ⟨pullback.snd _ _⟩
  have hY := hr κ hκ Y (pullback.fst _ _) (IsPullback.of_hasPullback _ _)
  rw [hr1] at hY
  let _ := structureSectionsAlgebra κ Y ⊤
  have hY' : Module.finrank κ Γ(Y, ⊤) = 1 := hY
  have : Nonempty Y := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : Subsingleton Γ(Y, ⊤) := by
      refine ⟨fun a b => ?_⟩
      exact Y.sheaf.eq_of_locally_eq' (U := (Empty.elim : Empty → Y.Opens)) ⊤
        (fun i => i.elim) (fun x _ => (IsEmpty.false x).elim) a b (fun i => i.elim)
    rw [Module.finrank_zero_of_subsingleton] at hY'
    exact zero_ne_one hY'
  have : ConnectedSpace Y :=
    connectedSpace_of_idempotent (idempotent_eq_zero_or_one_of_finrank_eq_one hY')
  have : Smooth (Y ↘ Spec (CommRingCat.of κ)) := by
    have : SmoothOfRelativeDimension d (pullback.snd q
        (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) := inferInstance
    exact SmoothOfRelativeDimension.smooth d
      (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
  have : IsLocallyNoetherian Y := inferInstance
  have : CompactSpace Y := inferInstance
  have : IsNoetherian Y := {}
  exact isIntegral_of_smooth_of_connectedSpace (Y ↘ Spec (CommRingCat.of κ))

end Fibre

end MixedFujita
