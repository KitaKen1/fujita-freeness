/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveRationalSectionExtension
public import MixedFujita.TwistedSectionFamily

/-!
On a compact integral scheme affine over polynomial projective space, every actual regular
function on a nonempty coordinate open is a ratio of global sections of N times the actual
hyperplane Cartier divisor, for every sufficiently large N. The denominator is the N-th power
of the coordinate section. Zeros of the regular function are permitted.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (e : X ⟶ polynomialProjectiveScheme n K) (g : MvPolynomial (Fin n) K)
  (hg : g.IsHomogeneous 1) (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def projectiveCoordinateCartierSection (j : Fin n) :
    Γ((projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
  cartierSectionCast (one_nsmul _)
    (projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))

theorem projectiveCoordinateCartierSection_rational (j : Fin n) :
    cartierSectionRational _ (projectiveCoordinateCartierSection e g hg hggen j₀ j) =
      projectiveFormRatio e g hg hggen j₀ 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) := by
  rw [projectiveCoordinateCartierSection, cartierSectionCast_rational, projectiveFormSection_rational]

theorem projectiveCoordinateCartierSection_nonvanishing (j : Fin n) :
    cartierSectionNonvanishingOpen _ (projectiveCoordinateCartierSection e g hg hggen j₀ j) =
      projectivePullbackCoordinateOpen e j := by
  rw [projectiveCoordinateCartierSection, cartierSectionNonvanishingOpen_cast,
    projectiveFormSection_nonvanishingOpen e g hg hggen j₀ one_pos]
  rfl

theorem projectiveCoordinateCartierSection_ne_zero
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    projectiveCoordinateCartierSection e g hg hggen j₀ j.val ≠ 0 := by
  apply (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp
  rw [projectiveCoordinateCartierSection_nonvanishing]
  exact j.property

/-- A positive power of an actual Cartier section has the same nonvanishing open. -/
theorem cartierSectionPower_nonvanishingOpen {Y : Scheme.{u}} [IsIntegral Y]
    (D : CartierDivisor Y) (s : Γ(D.sheaf, ⊤)) {N : ℕ} (hN : 0 < N) :
    cartierSectionNonvanishingOpen (N • D) (cartierSectionPower D s N) =
      cartierSectionNonvanishingOpen D s := by
  ext y
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt y
  change y ∈ cartierSectionNonvanishingOpen (N • D) (cartierSectionPower D s N) ↔
    y ∈ cartierSectionNonvanishingOpen D s
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ y (f ^ N)
    (cartierLocalEquation_pow D y f hf N),
    mem_cartierSectionNonvanishingOpen_iff_localCoefficient _ _ y f hf,
    cartierSectionPower_localCoefficient]
  exact isUnit_pow_iff hN.ne'

variable [IsAffineHom e] [CompactSpace X]

/-- A regular coefficient on a coordinate open extends after multiplication by all sufficiently
large powers of its coordinate section. -/
theorem projectiveChart_regular_function_eventually_global_section
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (a : Γ(X, projectivePullbackCoordinateOpen e j.val)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ s : Γ((N • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        cartierSectionRational _ s =
          X.germToFunctionField _ a *
            cartierSectionRational _ (projectiveCoordinateCartierSection e g hg hggen j₀ j.val) ^ N := by
  let : Nonempty (projectivePullbackCoordinateOpen e j.val) := j.property
  have hgen : MvPolynomial.X j.val ∉ (e (genericPoint X)).asHomogeneousIdeal :=
    genericPoint_mem (projectivePullbackCoordinateOpen e j.val)
  have hreg (y : X) (hy : y ∈ projectivePullbackCoordinateOpen e j.val)
      (v : X.functionFieldˣ) (hv : (0 : CartierDivisor X).IsLocalEquationAt y v) :
      (v : X.functionField) * X.germToFunctionField _ a ∈
        (algebraMap (X.presheaf.stalk y) X.functionField).range := by
    obtain ⟨w, hw⟩ := hv.exists_unit_mul_eq (CartierDivisor.isLocalEquationAt_zero y)
    rw [Units.val_one, mul_one] at hw
    refine ⟨(w : X.presheaf.stalk y) * X.presheaf.germ _ y hy a, ?_⟩
    rw [map_mul, hw, X.algebraMap_germ_eq_germToFunctionField hy]
  obtain ⟨N₀, hN₀⟩ := projectiveRationalSection_mem_sections e g hg hggen j₀ 0
    (MvPolynomial.X j.val) (MvPolynomial.isHomogeneous_X K j.val)
    (X.germToFunctionField _ a) one_pos hgen hreg
  refine ⟨N₀, fun N hN => ?_⟩
  have hm := hN₀ N hN
  simp only [mul_one, zero_add] at hm
  refine ⟨CartierDivisor.sectionMk _ hm, ?_⟩
  rw [cartierSectionRational_apply, CartierDivisor.sheafι_app_sectionMk,
    LinearEquiv.apply_symm_apply, projectiveCoordinateCartierSection_rational]

/-- The ratio to the fixed coordinate-power section is exactly the original actual regular
function in the scheme function field, at all sufficiently large positive degrees. -/
theorem projectiveChart_regular_function_eventually_section_ratio
    (j : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
    (a : Γ(X, projectivePullbackCoordinateOpen e j.val)) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ s : Γ((N • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        (cartierSectionRational _
          (cartierSectionPower _ (projectiveCoordinateCartierSection e g hg hggen j₀ j.val) N))⁻¹ *
            cartierSectionRational _ s = X.germToFunctionField _ a := by
  obtain ⟨N₀, hN₀⟩ := projectiveChart_regular_function_eventually_global_section e g hg hggen j₀ j a
  refine ⟨max N₀ 1, by omega, fun N hN => ?_⟩
  obtain ⟨s, hs⟩ := hN₀ N (le_trans (le_max_left _ _) hN)
  refine ⟨s, ?_⟩
  have hne : cartierSectionRational _
      (projectiveCoordinateCartierSection e g hg hggen j₀ j.val) ≠ 0 := by
    intro h
    exact projectiveCoordinateCartierSection_ne_zero e g hg hggen j₀ j
      (cartierSectionRational_injective _ (h.trans (map_zero _).symm))
  rw [cartierSectionPower_rational, hs]
  field_simp

end MixedFujita
