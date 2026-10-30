/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSGALineBundle
public import MixedFujita.AmpleDivisibleGlobalGeneration
public import MixedFujita.TwistedSectionFamily

/-!
The actual Cartier section of a homogeneous form has exactly its projective nonvanishing open.
Consequently a finite map to polynomial projective space supplies an ample SGA presentation of
the actual hyperplane Cartier divisor: coordinate sections have affine nonvanishing opens.
This uses the explicit Cartier divisor rather than an independently chosen representative.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n K) (g : MvPolynomial (Fin n) K)
  (hg : g.IsHomogeneous 1) (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- A finite polynomial-projective morphism makes the SGA presentation of its explicit
hyperplane Cartier divisor ample, using actual coordinate sections. -/
theorem projectiveHyperplaneCartier_sga_isAmple_of_finite [IsFinite e] :
    (cartierSGALineBundle (projectiveHyperplaneCartier e g hg hggen)).IsAmple := by
  have := polynomialProjectiveToBase_isProper n K
  have : CompactSpace (polynomialProjectiveScheme n K) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveToBase n K)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace e
  obtain ⟨k₀, hk₀⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint Y))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨k₀, ⟨⟨genericPoint Y, hk₀⟩⟩⟩
  have h : (cartierSGALineBundle (1 • projectiveHyperplaneCartier e g hg hggen)).IsAmple := by
    refine ⟨inferInstance, fun x => ?_⟩
    obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
    refine ⟨1, one_pos, cartierSGASection _
      (projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X K k)),
      ?_, ?_⟩
    · rw [cartierSGASection_nonvanishingLocus,
        projectiveFormSection_nonvanishingOpen e g hg hggen j₀ one_pos _ _]
      exact hk
    · rw [cartierSGASection_nonvanishingLocus,
        projectiveFormSection_nonvanishingOpen e g hg hggen j₀ one_pos _ _]
      exact (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K k) one_pos).preimage e
  simpa only [one_nsmul] using h

end MixedFujita
