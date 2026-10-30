/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
The critical-incidence construction adapts the existing pinned OpenAI Bertini
argument to point-ideal generators; the new algebraic-independence contradiction
handles the base point. No vendored source is modified.
-/
module
public import MixedFujita.EtaleRelativeJacobian
public import OAI.AlgebraicGeometry.Seshadri.Bertini.DifferentialFrames

@[expose] public section
namespace MixedFujita
open KaehlerDifferential
open OAI.MaximalSeshadri.FrameBertini (DifferentialFrame)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A derivation detecting a point-ideal element detects at least one set of ideal generators. -/
theorem pointIdealGenerators_nonzero_derivative
    {K R ι : Type*} [Field K] [CommRing R] [Algebra K R]
    (β : R →ₐ[K] K) (δ : Derivation K R R) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom)
    (y : R) (hy : β y = 0) (hdy : β (δ y) ≠ 0) :
    ∃ i, β (δ (v i)) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hmem : y ∈ Ideal.span (Set.range v) := by
    rw [hspan]
    exact hy
  have hzero (r : R) (hr : r ∈ Ideal.span (Set.range v)) : β (δ r) = 0 := by
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨i, rfl⟩ := hr
      exact hall i
    | zero => simp
    | add r s _ _ hr hs => simp only [map_add, hr, hs, add_zero]
    | smul a r hr hδr =>
      have hβr : β r = 0 := by
        have hm : r ∈ RingHom.ker β.toRingHom := hspan ▸ hr
        exact hm
      change β (δ (a * r)) = 0
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
        hβr, hδr, mul_zero, zero_mul, add_zero]
  exact hdy (hzero y hmem)

/-- A genuine Kaehler basis supplies the frame expected by the general Bertini proof. -/
noncomputable def differentialFrameOfBasis
    {K R κ : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype κ]
    (b : Module.Basis κ R Ω[R⁄K]) : DifferentialFrame K R κ where
  coord := {
    toFun := fun w i => b.repr w i
    map_add' := by intro x y; ext i; simp
    map_smul' := by intro r x; ext i; simp }
  vector := b
  sum_coord w := b.sum_repr w

theorem differentialFrameOfBasis_coord
    {K R κ : Type*} [CommRing K] [CommRing R] [Algebra K R] [Fintype κ]
    (b : Module.Basis κ R Ω[R⁄K]) (w : Ω[R⁄K]) (i : κ) :
    (differentialFrameOfBasis b).coord w i = b.repr w i := rfl

/-- Nonempty etale coordinates force the pointed system to have a nonzero first jet. -/
theorem etale_pointIdealGenerators_nonzero_frame_coefficient
    {K R ι : Type*} [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    (σ : MvPolynomial (Fin n) K →ₐ[K] R) (hσ : σ.toRingHom.FormallyEtale)
    (j : Fin n) (β : R →ₐ[K] K) (v : ι → R)
    (hspan : Ideal.span (Set.range v) = RingHom.ker β.toRingHom) :
    ∃ i k, β ((differentialFrameOfBasis (etaleCoordinateBasis σ hσ)).coord
      (D K R (v i)) k) ≠ 0 := by
  let δ := etaleCoordinateDerivation σ hσ j
  let y := σ (MvPolynomial.X j) - algebraMap K R (β (σ (MvPolynomial.X j)))
  have hy : β y = 0 := by simp [y]
  have hdy : β (δ y) ≠ 0 := by
    dsimp [y, δ]
    rw [Derivation.map_sub, Derivation.map_algebraMap,
      etaleCoordinateDerivation_coordinate, ite_eq_left rfl, sub_zero, map_one]
    exact one_ne_zero
  obtain ⟨i, hi⟩ := pointIdealGenerators_nonzero_derivative β δ v hspan y hy hdy
  exact ⟨i, j, hi⟩

end MixedFujita