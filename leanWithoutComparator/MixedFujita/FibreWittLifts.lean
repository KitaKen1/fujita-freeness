/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.WittTwoLift
public import MixedFujita.CoordinateFrobeniusLift
public import MixedFujita.TensorEtaleCoordinates
public import MixedFujita.FibreChartGerms
public import MixedFujita.ClosureSectionsInjective

/-!
Lifts mod `p²` of the functions on a fibre (step 10, R4-6).

Let `X` be flat over `A`, `κ` a perfect field of characteristic `p` with a lift `A → W₂(κ)` of
`A → κ` (check 519), and `Y = X ×_A κ` with `g : Y → X`. For an affine open `V` of `X`:
* `fibreWittπ : W₂(κ) ⊗_A Γ(X, V) → Γ(Y, g⁻¹V)` is the reduction followed by the base change
  isomorphism of check 497. It is surjective with kernel `p (W₂(κ) ⊗_A Γ(X, V))`, `p z = 0` only
  in the kernel (flatness), `p² = 0`, and the Teichmüller lifts map to the constants (check 519):
  the lift data `π, hker, hann, hp2, hK` of check 491.
* `fibreWittRestrict` restricts the lifts to a smaller affine open, compatibly with `π`.
* `fibreWittFrobenius`: for étale coordinates `y` on `V` with `g⁻¹V` nonempty, the coordinate
  Frobenius lift of check 521: it lifts the `p`-th power map, is the Frobenius on `W₂(κ)` and fixes
  the coordinates up to `p`-th powers.
* `fibreWittFrobenius_restrict`: restriction commutes with the coordinate Frobenius lifts of the
  restricted coordinates, by the uniqueness of check 520 (`W₂(κ) ⊗_A Γ(X, V)` is formally étale over
  `W₂(κ)[Y]`, check 521). This is the hypothesis `hRF` of check 491.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule

universe u

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A : Type u} [CommRing A] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))

section Lift

/-- **The reduction of lifts to the functions on the fibre.** -/
noncomputable def fibreWittπ {V : X.Opens} (hV : IsAffineOpen V) :
    WittTwo p κ ⊗[A] Γ(X, V) →+* Γ(Y, g ⁻¹ᵁ V) :=
  (sectionsBaseChangeEquiv H hV).toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V))).toRingHom

omit [PerfectRing κ p] in
theorem fibreWittπ_tmul {V : X.Opens} (hV : IsAffineOpen V) (w : WittTwo p κ) (a : Γ(X, V)) :
    fibreWittπ p κ h H hV (w ⊗ₜ[A] a) =
      algebraMap κ Γ(Y, g ⁻¹ᵁ V) (wittTwoReduction p κ w) * g.appLE V (g ⁻¹ᵁ V) le_rfl a := by
  change sectionsBaseChangeEquiv H hV (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h)
    (AlgHom.id A Γ(X, V)) (w ⊗ₜ[A] a)) = _
  rw [Algebra.TensorProduct.map_tmul, sectionsBaseChangeEquiv_tmul]
  rfl

omit [PerfectRing κ p] in
theorem fibreWittπ_surjective {V : X.Opens} (hV : IsAffineOpen V) :
    Function.Surjective (fibreWittπ p κ h H hV) :=
  (sectionsBaseChangeEquiv H hV).surjective.comp (wittTwo_tensor_surjective p κ h)

/-- **The kernel of the reduction is `p` times the lifts** (`hker`). -/
theorem fibreWittπ_exists_eq_p_mul {V : X.Opens} (hV : IsAffineOpen V)
    (z : WittTwo p κ ⊗[A] Γ(X, V)) (hz : fibreWittπ p κ h H hV z = 0) :
    ∃ y, z = (p : WittTwo p κ ⊗[A] Γ(X, V)) * y := by
  apply wittTwo_tensor_exists_eq_p_mul p κ h z
  apply (sectionsBaseChangeEquiv H hV).injective
  rw [map_zero]
  exact hz

omit [PerfectRing κ p] in
/-- **`p` kills only elements of the kernel**, for `X` flat over `A` (`hann`). -/
theorem fibreWittπ_eq_zero_of_p_mul_eq_zero [Flat (X ↘ Spec (CommRingCat.of A))] {V : X.Opens}
    (hV : IsAffineOpen V) (z : WittTwo p κ ⊗[A] Γ(X, V))
    (hz : (p : WittTwo p κ ⊗[A] Γ(X, V)) * z = 0) : fibreWittπ p κ h H hV z = 0 := by
  have hflat : Module.Flat A ((CohomologyAux.unitModule X).presheaf.obj (op V)) :=
    flat_sections_of_flat hV
  have : Module.Flat A Γ(X, V) := hflat
  have h0 : Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V)) z = 0 :=
    wittTwo_tensor_eq_zero_of_p_mul_eq_zero p κ h z hz
  change sectionsBaseChangeEquiv H hV
    (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V)) z) = 0
  rw [h0, map_zero]

omit [PerfectRing κ p] in
/-- The Teichmüller lifts map to the constants. -/
theorem fibreWittπ_teichmuller {V : X.Opens} (hV : IsAffineOpen V) (k : κ) :
    fibreWittπ p κ h H hV (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, V))) =
      algebraMap κ Γ(Y, g ⁻¹ᵁ V) k := by
  rw [fibreWittπ_tmul, wittTwoReduction_teichmuller, map_one, mul_one]

/-- The restriction of lifts to a smaller open. -/
noncomputable def fibreWittRestrict {V V' : X.Opens} (hle : V' ≤ V) :
    WittTwo p κ ⊗[A] Γ(X, V) →+* WittTwo p κ ⊗[A] Γ(X, V') :=
  (Algebra.TensorProduct.map (AlgHom.id A (WittTwo p κ)) (structureRestrictAlgHom A X hle)).toRingHom

omit [CharP κ p] [PerfectRing κ p] [Algebra A κ] in
theorem fibreWittRestrict_tmul {V V' : X.Opens} (hle : V' ≤ V) (w : WittTwo p κ) (a : Γ(X, V)) :
    fibreWittRestrict p κ hle (w ⊗ₜ[A] a) = w ⊗ₜ[A] X.presheaf.map (homOfLE hle).op a :=
  rfl

omit [PerfectRing κ p] in
/-- **The reduction commutes with restriction** (`hR`). -/
theorem fibreWittπ_restrict {V V' : X.Opens} (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hle : V' ≤ V) (z : WittTwo p κ ⊗[A] Γ(X, V)) :
    fibreWittπ p κ h H hV' (fibreWittRestrict p κ hle z) =
      Y.presheaf.map (homOfLE ((Opens.map g.base).monotone hle)).op (fibreWittπ p κ h H hV z) := by
  induction z using TensorProduct.inductionOn with
  | tmul w a =>
    rw [fibreWittRestrict_tmul, fibreWittπ_tmul, fibreWittπ_tmul, map_mul]
    congr 1
    · exact (AlgHom.commutes (structureRestrictAlgHom κ Y ((Opens.map g.base).monotone hle))
        (wittTwoReduction p κ w)).symm
    · rw [appLE_of_restrict_apply, appLE_restrict_apply]
  | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]

omit [CharP κ p] [PerfectRing κ p] [Algebra A κ] in
/-- `p² = 0` in the lifts (`hp2`). -/
theorem fibreWitt_p_mul_p {V : X.Opens} :
    (p : WittTwo p κ ⊗[A] Γ(X, V)) * p = 0 :=
  wittTwo_tensor_p_mul_p p κ

end Lift

section Frobenius

attribute [local instance] tensorCoordinatesAlgebra tensorCoordinates_isScalarTower_coeff

variable {n : ℕ}

/-- The functions on `V` over the coordinates. -/
@[instance_reducible]
noncomputable def coordinatesAlgebra {V : X.Opens} (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) :
    Algebra (MvPolynomial (Fin n) A) Γ(X, V) :=
  y.toRingHom.toAlgebra

theorem coordinatesAlgebra_isScalarTower {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) :
    letI := coordinatesAlgebra y
    IsScalarTower A (MvPolynomial (Fin n) A) Γ(X, V) :=
  letI := coordinatesAlgebra y
  IsScalarTower.of_algebraMap_eq fun a => (y.commutes a).symm

include H in
/-- The fibre functions are nonzero over a nonempty preimage. -/
theorem nontrivial_fibreWitt_tensor {V : X.Opens} (hV : IsAffineOpen V)
    (hne : Nonempty (g ⁻¹ᵁ V)) : Nontrivial (κ ⊗[A] Γ(X, V)) :=
  (sectionsBaseChangeEquiv H hV).toRingEquiv.symm.injective.nontrivial

theorem exists_fibreWittFrobenius {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] :
    ∃ F : WittTwo p κ ⊗[A] Γ(X, V) →+* WittTwo p κ ⊗[A] Γ(X, V),
      (∀ x, Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V)) (F x) =
        Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V)) x ^ p) ∧
      (∀ w, F (w ⊗ₜ[A] (1 : Γ(X, V))) = wittTwoFrobenius p κ w ⊗ₜ[A] (1 : Γ(X, V))) ∧
      (∀ j, F ((1 : WittTwo p κ) ⊗ₜ[A] y (MvPolynomial.X j)) =
        ((1 : WittTwo p κ) ⊗ₜ[A] y (MvPolynomial.X j)) ^ p) := by
  let _ := coordinatesAlgebra y
  have := coordinatesAlgebra_isScalarTower y
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) A) Γ(X, V) := hy
  obtain ⟨F, hF, hW, hX, -⟩ := exists_wittTwo_coordinateFrobeniusLift p κ h (B := Γ(X, V)) (n := n)
  exact ⟨F, hF, hW, hX⟩

/-- **The coordinate Frobenius lift on the lifts of the functions on `V`.** -/
noncomputable def fibreWittFrobenius {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] : WittTwo p κ ⊗[A] Γ(X, V) →+* WittTwo p κ ⊗[A] Γ(X, V) :=
  Classical.choose (exists_fibreWittFrobenius p κ h y hy)

theorem fibreWittFrobenius_reduction {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] (x : WittTwo p κ ⊗[A] Γ(X, V)) :
    Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V))
        (fibreWittFrobenius p κ h y hy x) =
      Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V)) x ^ p :=
  (Classical.choose_spec (exists_fibreWittFrobenius p κ h y hy)).1 x

/-- The coordinate Frobenius lifts the `p`-th power map of the fibre (`hF`). -/
theorem fibreWittπ_frobenius {V : X.Opens} (hV : IsAffineOpen V)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] (x : WittTwo p κ ⊗[A] Γ(X, V)) :
    fibreWittπ p κ h H hV (fibreWittFrobenius p κ h y hy x) =
      fibreWittπ p κ h H hV x ^ p := by
  change sectionsBaseChangeEquiv H hV (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h)
      (AlgHom.id A Γ(X, V)) (fibreWittFrobenius p κ h y hy x)) =
    sectionsBaseChangeEquiv H hV (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h)
      (AlgHom.id A Γ(X, V)) x) ^ p
  rw [fibreWittFrobenius_reduction, map_pow]

theorem fibreWittFrobenius_tmul_one {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] (w : WittTwo p κ) :
    fibreWittFrobenius p κ h y hy (w ⊗ₜ[A] (1 : Γ(X, V))) =
      wittTwoFrobenius p κ w ⊗ₜ[A] (1 : Γ(X, V)) :=
  (Classical.choose_spec (exists_fibreWittFrobenius p κ h y hy)).2.1 w

theorem fibreWittFrobenius_coordinate {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] (j : Fin n) :
    fibreWittFrobenius p κ h y hy ((1 : WittTwo p κ) ⊗ₜ[A] y (MvPolynomial.X j)) =
      ((1 : WittTwo p κ) ⊗ₜ[A] y (MvPolynomial.X j)) ^ p :=
  (Classical.choose_spec (exists_fibreWittFrobenius p κ h y hy)).2.2 j

/-- The Teichmüller lifts are fixed up to `p`-th powers (`hK`). -/
theorem fibreWittFrobenius_teichmuller {V : X.Opens}
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (hy : y.toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] (k : κ) :
    fibreWittFrobenius p κ h y hy (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, V))) =
      (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, V))) ^ p := by
  rw [fibreWittFrobenius_tmul_one, wittTwoFrobenius_teichmuller, Algebra.TensorProduct.tmul_pow,
    one_pow]

/-- **Restriction commutes with the coordinate Frobenius lifts** (`hRF`, uniqueness of check 520). -/
theorem fibreWittFrobenius_restrict {V V' : X.Opens} (hle : V' ≤ V)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V))
    (hy : y.toRingHom.FormallyEtale) (hy' : (restrictCoordinates hle y).toRingHom.FormallyEtale)
    [Nontrivial (κ ⊗[A] Γ(X, V))] [Nontrivial (κ ⊗[A] Γ(X, V'))] :
    (fibreWittRestrict p κ hle).comp (fibreWittFrobenius p κ h y hy) =
      (fibreWittFrobenius p κ h (restrictCoordinates hle y) hy').comp
        (fibreWittRestrict p κ hle) := by
  let _ := coordinatesAlgebra y
  have := coordinatesAlgebra_isScalarTower y
  have : Algebra.FormallyEtale (MvPolynomial (Fin n) A) Γ(X, V) := hy
  have := formallyEtale_tensorCoordinates (A := A) (W := WittTwo p κ) (B := Γ(X, V)) (n := n)
  have : Algebra.FormallyUnramified (MvPolynomial (Fin n) (WittTwo p κ))
      (WittTwo p κ ⊗[A] Γ(X, V)) := inferInstance
  let red' := (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h)
    (AlgHom.id A Γ(X, V'))).toRingHom
  -- the reduction commutes with restriction
  have hred : ∀ z : WittTwo p κ ⊗[A] Γ(X, V), red' (fibreWittRestrict p κ hle z) =
      Algebra.TensorProduct.map (AlgHom.id A κ) (structureRestrictAlgHom A X hle)
        (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V)) z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul w a => rfl
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add, map_add]
  apply ringHom_eq_of_formallyUnramified (A := MvPolynomial (Fin n) (WittTwo p κ)) red'
    (fun x y hx hy => wittTwo_tensor_mul_eq_zero p κ h x y hx hy)
  · -- agreement on `W₂(κ)[Y]`
    intro q
    have hq : ((fibreWittRestrict p κ hle).comp (fibreWittFrobenius p κ h y hy)).comp
        (algebraMap (MvPolynomial (Fin n) (WittTwo p κ)) (WittTwo p κ ⊗[A] Γ(X, V))) =
        ((fibreWittFrobenius p κ h (restrictCoordinates hle y) hy').comp
          (fibreWittRestrict p κ hle)).comp
          (algebraMap (MvPolynomial (Fin n) (WittTwo p κ)) (WittTwo p κ ⊗[A] Γ(X, V))) := by
      apply MvPolynomial.ringHom_ext
      · intro w
        change fibreWittRestrict p κ hle (fibreWittFrobenius p κ h y hy
            (tensorCoordinates A (WittTwo p κ) Γ(X, V) n (MvPolynomial.C w))) =
          fibreWittFrobenius p κ h (restrictCoordinates hle y) hy'
            (fibreWittRestrict p κ hle (tensorCoordinates A (WittTwo p κ) Γ(X, V) n
              (MvPolynomial.C w)))
        rw [tensorCoordinates_C, fibreWittFrobenius_tmul_one, fibreWittRestrict_tmul,
          fibreWittRestrict_tmul, map_one, fibreWittFrobenius_tmul_one]
      · intro j
        change fibreWittRestrict p κ hle (fibreWittFrobenius p κ h y hy
            (tensorCoordinates A (WittTwo p κ) Γ(X, V) n (MvPolynomial.X j))) =
          fibreWittFrobenius p κ h (restrictCoordinates hle y) hy'
            (fibreWittRestrict p κ hle (tensorCoordinates A (WittTwo p κ) Γ(X, V) n
              (MvPolynomial.X j)))
        rw [tensorCoordinates_X]
        change fibreWittRestrict p κ hle (fibreWittFrobenius p κ h y hy
            ((1 : WittTwo p κ) ⊗ₜ[A] y (MvPolynomial.X j))) =
          fibreWittFrobenius p κ h (restrictCoordinates hle y) hy'
            (fibreWittRestrict p κ hle ((1 : WittTwo p κ) ⊗ₜ[A] y (MvPolynomial.X j)))
        rw [fibreWittFrobenius_coordinate, map_pow, fibreWittRestrict_tmul]
        exact (fibreWittFrobenius_coordinate p κ h (restrictCoordinates hle y) hy' j).symm
    exact RingHom.congr_fun hq q
  · -- agreement modulo `p`
    intro x
    change red' (fibreWittRestrict p κ hle (fibreWittFrobenius p κ h y hy x)) =
      red' (fibreWittFrobenius p κ h (restrictCoordinates hle y) hy'
        (fibreWittRestrict p κ hle x))
    rw [hred, fibreWittFrobenius_reduction, map_pow]
    change _ = Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A Γ(X, V'))
      (fibreWittFrobenius p κ h (restrictCoordinates hle y) hy'
        (fibreWittRestrict p κ hle x))
    rw [fibreWittFrobenius_reduction]
    change _ = (red' (fibreWittRestrict p κ hle x)) ^ p
    rw [hred]

end Frobenius

end MixedFujita
