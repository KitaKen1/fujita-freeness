/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveClosureBaseChange
public import MixedFujita.AffineSectionsBaseChange
public import MixedFujita.TensorEtaleCoordinates
public import MixedFujita.ConnectedSmoothIntegral
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
Étale charts of the fibres of a scheme over a ring (step 10, R4-3).

* `exists_ne_zero_forall_nonempty_preimage_fibre`: let `X` be flat and locally of finite
  presentation over a ring `A`, and `V` a nonempty affine open. There is `f ≠ 0` in `A` such
  that the preimage of `V` in the fibre `X ×_A κ` is nonempty for every field `κ` over `A` in which
  `f` is a unit. The image of `Spec Γ(X, V) → Spec A` is open (Chevalley, for flat maps of finite
  presentation; Mathlib's `isOpenMap_comap_of_hasGoingDown_of_finitePresentation`), so it contains
  a nonempty basic open `D(f)`; the point of `Spec κ` lies over `D(f)`, and a point of a fibre
  product exists over any pair of points with the same image.
* `fibreEtaleChart`: étale coordinates `y : A[Y] → Γ(X, V)` on an affine open give an étale chart
  of the fibre `Y = X ×_A κ` on the preimage of `V`, with the coordinates
  `κ[Y] → κ ⊗_A Γ(X, V) ≅ Γ(Y, g⁻¹V)` (checks 497 and 521). Its coordinates are the pullbacks of
  those of `V` (`fibreEtaleChart_coords_X`).

For the closure `T_A` this turns the spread-out coordinates of check 512 into the charts of the
fibre `T_κ` on which the lift data of check 491 live.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- A ring isomorphism is formally étale. -/
theorem formallyEtale_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    (e : R →+* S).FormallyEtale := by
  algebraize [(e : R →+* S)]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

section Nonempty

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of A))

/-- **Nonempty fibres of an affine open away from a nonzero element**: for `X` flat and locally of
finite presentation over `A` and a nonempty affine open `V`, the preimage of `V` in every fibre
over a field in which a certain `f ≠ 0` is a unit is nonempty. -/
theorem exists_ne_zero_forall_nonempty_preimage_fibre [Flat q] [LocallyOfFinitePresentation q]
    {V : X.Opens} (hV : IsAffineOpen V) (x₀ : X) (hx₀ : x₀ ∈ V) :
    ∃ f : A, f ≠ 0 ∧ ∀ (κ : Type u) [Field κ] [Algebra A κ], IsUnit (algebraMap A κ f) →
      Nonempty ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A κ)))) ⁻¹ᵁ V) := by
  classical
  let φ : A →+* Γ(X, V) :=
    (q.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hflat : φ.Flat := by
    have h := HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    exact (RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv _).2 h
  have hfp : φ.FinitePresentation := by
    have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation q inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    exact (RingHom.finitePresentation_respectsIso.cancel_left_isIso
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv _).2 h
  algebraize [φ]
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A Γ(X, V)))) := by
    have := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A) (S := Γ(X, V))
    simpa [Set.image_univ] using this _ isOpen_univ
  have : Nontrivial Γ(X, V) := nontrivial_of_ne 1 0 (one_ne_zero_of_nonempty_open V x₀ hx₀)
  obtain ⟨P⟩ : Nonempty (PrimeSpectrum Γ(X, V)) := inferInstance
  obtain ⟨_, ⟨f, rfl⟩, hPf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self P) hopen
  refine ⟨f, ?_, fun κ _ _ hf => ?_⟩
  · rintro rfl
    simp at hPf
  · let s₀ : PrimeSpectrum κ := ⟨⊥, Ideal.isPrime_bot⟩
    let s : Spec (CommRingCat.of κ) := s₀
    have hs : PrimeSpectrum.comap (algebraMap A κ) s₀ ∈
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) := by
      rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
        Ideal.mem_comap]
      exact fun h => hf.ne_zero ((Ideal.mem_bot).1 h)
    obtain ⟨Q, hQ⟩ := hsub hs
    let x : X := hV.fromSpec Q
    have hxV : x ∈ V := by
      have h := hV.range_fromSpec
      rw [Set.ext_iff] at h
      exact (h x).1 ⟨Q, rfl⟩
    have hxq : q x = Spec.map (CommRingCat.ofHom (algebraMap A κ)) s := by
      change (hV.fromSpec ≫ q) Q = _
      rw [fromSpec_comp_eq_SpecMap q hV, Spec.map_apply, Spec.map_apply,
        CommRingCat.hom_ofHom]
      exact hQ
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x s hxq
    exact ⟨⟨z, by
      change pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap A κ))) z ∈ V
      rw [hz]
      exact hxV⟩⟩

end Nonempty

section FibreChart

attribute [local instance] structureSectionsAlgebra

variable {A κ : Type u} [CommRing A] [Field κ] [Algebra A κ] {X Y : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))] {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
  {n : ℕ} {V : X.Opens} (hV : IsAffineOpen V)
  (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))

/-- The coordinates of the fibre: `κ[Y] → κ ⊗_A Γ(X, V) ≅ Γ(Y, g⁻¹V)`. -/
noncomputable def fibreChartCoords : MvPolynomial (Fin n) κ →ₐ[κ] Γ(Y, g ⁻¹ᵁ V) :=
  letI : Algebra (MvPolynomial (Fin n) A) Γ(X, V) := y.toRingHom.toAlgebra
  haveI : IsScalarTower A (MvPolynomial (Fin n) A) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (y.commutes a).symm
  (sectionsBaseChangeEquiv H hV).toAlgHom.comp (tensorCoordinates A κ Γ(X, V) n)

/-- The coordinates of the fibre are the pullbacks of the coordinates. -/
theorem fibreChartCoords_X (j : Fin n) :
    fibreChartCoords H hV y (MvPolynomial.X j) = g.appLE V (g ⁻¹ᵁ V) le_rfl (y (MvPolynomial.X j)) := by
  let _ : Algebra (MvPolynomial (Fin n) A) Γ(X, V) := y.toRingHom.toAlgebra
  have _ : IsScalarTower A (MvPolynomial (Fin n) A) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (y.commutes a).symm
  change sectionsBaseChangeEquiv H hV (tensorCoordinates A κ Γ(X, V) n (MvPolynomial.X j)) = _
  rw [tensorCoordinates_X, sectionsBaseChangeEquiv_tmul, map_one, one_mul]
  rfl

include y in
/-- The coordinates of the fibre are formally étale if those of `V` are. -/
theorem fibreChartCoords_formallyEtale (hy : y.toRingHom.FormallyEtale) :
    (fibreChartCoords H hV y).toRingHom.FormallyEtale := by
  let _ : Algebra (MvPolynomial (Fin n) A) Γ(X, V) := y.toRingHom.toAlgebra
  have _ : IsScalarTower A (MvPolynomial (Fin n) A) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (y.commutes a).symm
  have _ : Algebra.FormallyEtale (MvPolynomial (Fin n) A) Γ(X, V) := hy
  have h1 : (tensorCoordinates A κ Γ(X, V) n).toRingHom.FormallyEtale :=
    formallyEtale_tensorCoordinates (A := A) (W := κ) (B := Γ(X, V)) (n := n)
  exact RingHom.FormallyEtale.comp h1
    (formallyEtale_of_ringEquiv (sectionsBaseChangeEquiv H hV).toRingEquiv)

/-- **The étale chart of the fibre** on the preimage of an affine open with étale coordinates. -/
noncomputable def fibreEtaleChart [IsAffineHom g] (hy : y.toRingHom.FormallyEtale)
    (hne : Nonempty (g ⁻¹ᵁ V)) : EtaleChart κ Y n where
  U := g ⁻¹ᵁ V
  isAffine := hV.preimage g
  nonempty := hne
  coords := fibreChartCoords H hV y
  formallyEtale := fibreChartCoords_formallyEtale H hV y hy

theorem fibreEtaleChart_U [IsAffineHom g] (hy : y.toRingHom.FormallyEtale)
    (hne : Nonempty (g ⁻¹ᵁ V)) : (fibreEtaleChart H hV y hy hne).U = g ⁻¹ᵁ V :=
  rfl

/-- The coordinates of the fibre chart are the pullbacks of the coordinates. -/
theorem fibreEtaleChart_coords_X [IsAffineHom g] (hy : y.toRingHom.FormallyEtale)
    (hne : Nonempty (g ⁻¹ᵁ V)) (j : Fin n) :
    (fibreEtaleChart H hV y hy hne).coords (MvPolynomial.X j) =
      g.appLE V (g ⁻¹ᵁ V) le_rfl (y (MvPolynomial.X j)) :=
  fibreChartCoords_X H hV y j

end FibreChart

end MixedFujita
