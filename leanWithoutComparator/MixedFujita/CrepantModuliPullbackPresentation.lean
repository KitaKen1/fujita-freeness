/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CanonicalDiscriminantModuliWeil
public import MixedFujita.CrepantBoundaryPerturbation
public import MixedFujita.BirationalComposition

/-!
Transport the original actual Cartier presentation through a commuting modification
square. The normalized actual crepant canonical-plus-boundary divisor is rationally
linearly equivalent to the actual Q-Cartier pullback of the base's canonical,
discriminant and moduli sum. No positivity of the specified base Cartier divisor
or of the moduli part is assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y T B : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsIntegral T] [IsIntegral B]
  (π : T ⟶ X) [IsDominant π] (g : X ⟶ Y) [IsDominant g]
  (ρ : B ⟶ Y) [IsDominant ρ] (q : T ⟶ B) [IsDominant q]
  (hsquare : q ≫ ρ = π ≫ g)

include hsquare in
/-- The original principal witness pulls back to the same actual commuting model. -/
theorem cartier_presentation_of_compatible_modification
    (D : CartierDivisor X) (H : CartierDivisor Y) (m : ℕ) (ψ : X.functionFieldˣ)
    (hD : D = m • cartierPullback g H + principalCartierDivisor X ψ) :
    cartierPullback π D = m • cartierPullback q (cartierPullback ρ H) +
      principalCartierDivisor T (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) := by
  have hPb : cartierPullback π (cartierPullback g H) =
      cartierPullback q (cartierPullback ρ H) := by
    calc
      cartierPullback π (cartierPullback g H) = cartierPullback (π ≫ g) H :=
        (cartierPullback_comp g π H).symm
      _ = cartierPullback q (cartierPullback ρ H) := by
        simpa only [hsquare] using cartierPullback_comp ρ q H
  rw [hD, cartierPullback_add, cartierPullback_nsmul, cartierPullback_principal, hPb]

variable [IsNoetherian T] [IsNoetherian B]

include hsquare in
/-- The normalized pullback of the original Cartier divisor has the required rational class. -/
theorem compatible_moduli_pullback_linear_equivalence
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (D : CartierDivisor X) (H : CartierDivisor Y) (C : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (d : ℕ) (hd : 0 < d) (m : ℕ)
    (ψ : X.functionFieldˣ)
    (hD : D = m • cartierPullback g H + principalCartierDivisor X ψ) :
    OAI.RelativeDenominators.RationallyLinearlyEquivalent T
      ((1 / (d : ℚ)) • rationalCartierWeilDivisor (cartierPullback π D))
      (OAI.RelativeDenominators.pullbackQCartier hnormB q
        (rationalCartierWeilDivisor C + Δ +
          moduliWeilPart C (cartierPullback ρ H) Δ ((m : ℚ) / (d : ℚ)))
        (moduliWeilPart_combination_isQCartier C (cartierPullback ρ H) Δ
          ((m : ℚ) / (d : ℚ)))) := by
  rw [moduliWeilPart_combination_pullback]
  exact rationalCartierWeilDivisor_presentation_linear_equivalence
    (cartierPullback π D) (cartierPullback q (cartierPullback ρ H)) d hd m
    (Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ)
    (cartier_presentation_of_compatible_modification π g ρ q hsquare D H m ψ hD)

variable {K : Type u} [Field K] {n : ℕ}
  [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
  [π.IsOver (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]

/-- The actual crepant canonical-plus-boundary Weil divisor is the normalized Cartier pullback. -/
theorem crepant_canonical_boundary_rational_recombine
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (cT : EtaleChart K T n)
    (d : ℕ) (hd : 0 < d) (D : CartierDivisor X) :
    rationalCartierWeilDivisor (smoothCanonicalDivisor cT +
      principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
      (1 / (d : ℚ)) • rationalCartierWeilDivisor
        (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) =
      (1 / (d : ℚ)) • rationalCartierWeilDivisor (cartierPullback π D) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h1 : (1 / (d : ℚ)) * (d : ℚ) = 1 := by field_simp
  have hrat := congrArg (rationalCartierWeilDivisor (X := T))
    (crepantBoundaryCartier_smooth_recombine π hπ c f d D cT)
  simp only [rationalCartierWeilDivisor_add, rationalCartierWeilDivisor_nsmul_rat] at hrat
  rw [← hrat, smul_add, smul_smul, h1, one_smul, rationalCartierWeilDivisor_add]

include hsquare in
/-- The actual crepant canonical and boundary data satisfy the base moduli pullback formula. -/
theorem crepant_canonical_boundary_moduli_linear_equivalence
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (cT : EtaleChart K T n)
    (D : CartierDivisor X) (H : CartierDivisor Y) (C : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (d : ℕ) (hd : 0 < d) (m : ℕ)
    (ψ : X.functionFieldˣ)
    (hD : D = m • cartierPullback g H + principalCartierDivisor X ψ) :
    OAI.RelativeDenominators.RationallyLinearlyEquivalent T
      (rationalCartierWeilDivisor (smoothCanonicalDivisor cT +
        principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
        (1 / (d : ℚ)) • rationalCartierWeilDivisor
          (crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover))
      (OAI.RelativeDenominators.pullbackQCartier hnormB q
        (rationalCartierWeilDivisor C + Δ +
          moduliWeilPart C (cartierPullback ρ H) Δ ((m : ℚ) / (d : ℚ)))
        (moduliWeilPart_combination_isQCartier C (cartierPullback ρ H) Δ
          ((m : ℚ) / (d : ℚ)))) := by
  rw [crepant_canonical_boundary_rational_recombine π hπ c f cT d hd D]
  exact compatible_moduli_pullback_linear_equivalence π g ρ q hsquare hnormB D H C Δ d hd m ψ hD

end MixedFujita
