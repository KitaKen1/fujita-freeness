/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuliCartierIntegralPresentation
public import MixedFujita.CrepantModuliPullbackPresentation
public import MixedFujita.CartierSectionPowers

/-! The actual moduli Cartier multiple is represented by a cleared relative
adjoint Cartier divisor, with the actual pulled original principal witness.
The same integral identity holds for every further natural multiple. -/

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

/-- Clear the original denominator and both actual Cartier multiples in the relative adjoint. -/
noncomputable def relativeAdjointCartier (π : T ⟶ X) [IsDominant π]
    (q : T ⟶ B) [IsDominant q] (D : CartierDivisor X) (C CΔ : CartierDivisor B)
    (d m ℓ : ℕ) : CartierDivisor T :=
  (ℓ * m) • cartierPullback π D - (d * m * ℓ) • cartierPullback q C -
    (d * ℓ) • cartierPullback q CΔ

/-- The exact principal presentation uses the original actual Cartier relation and the
constructed discriminant/moduli Cartier coefficients on the same base. -/
theorem relative_adjoint_cartier_principal_presentation [IsNoetherian B]
    (π : T ⟶ X) [IsDominant π] (g : X ⟶ Y) [IsDominant g]
    (ρ : B ⟶ Y) [IsDominant ρ] (q : T ⟶ B) [IsDominant q]
    (hsquare : q ≫ ρ = π ≫ g)
    (hnormB : ∀ b : B, IsIntegrallyClosed (B.presheaf.stalk b))
    (D : CartierDivisor X) (H : CartierDivisor Y) (C CΔ CM : CartierDivisor B)
    (Δ : CodimensionOnePoint B →₀ ℚ) (d : ℕ) (hd : 0 < d) (m ℓ s : ℕ)
    (ψ : X.functionFieldˣ)
    (hD : D = s • cartierPullback g H + principalCartierDivisor X ψ)
    (hCΔ : ∀ β : CodimensionOnePoint B,
      (cartierCoefficient CΔ (β : B) : ℚ) = (m : ℚ) * Δ β)
    (hCM : ∀ β : CodimensionOnePoint B,
      (cartierCoefficient CM (β : B) : ℚ) =
        (ℓ : ℚ) * moduliWeilPart C (cartierPullback ρ H) Δ ((s : ℚ) / (d : ℚ)) β) :
    relativeAdjointCartier π q D C CΔ d m ℓ = (d * m) • cartierPullback q CM +
      principalCartierDivisor T
        ((Units.map (dominantFunctionFieldMap π).hom.toMonoidHom ψ) ^ (ℓ * m)) := by
  have hbase := moduli_cartier_integral_presentation hnormB C (cartierPullback ρ H)
    CΔ CM Δ d hd m ℓ s hCΔ hCM
  have hpull : (d * m) • cartierPullback q CM =
      (ℓ * m * s) • cartierPullback q (cartierPullback ρ H) -
        (d * m * ℓ) • cartierPullback q C - (d * ℓ) • cartierPullback q CΔ := by
    simpa only [cartierPullback_nsmul, cartierPullback_sub] using
      congrArg (cartierPullback q) hbase
  have hπ := cartier_presentation_of_compatible_modification π g ρ q hsquare D H s ψ hD
  unfold relativeAdjointCartier
  rw [hπ, nsmul_add, smul_smul, hpull, principalCartierDivisor_power]
  abel

/-- Any principal Cartier presentation supplies the exact principal witness for every multiple. -/
theorem cartier_principal_presentation_nsmul (L A : CartierDivisor T) (χ : T.functionFieldˣ)
    (hL : L = A + principalCartierDivisor T χ) (j : ℕ) :
    j • L = j • A + principalCartierDivisor T (χ ^ j) := by
  rw [hL, nsmul_add, principalCartierDivisor_power]

/-- The cleared relative adjoint is the actual crepant canonical-plus-boundary expression. -/
theorem relative_adjoint_cartier_crepant_expression
    {K : Type u} [Field K] {n : ℕ}
    [X.Over (Spec (CommRingCat.of K))] [T.Over (Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K))]
    (π : T ⟶ X) [IsDominant π] [π.IsOver (Spec (CommRingCat.of K))]
    (hπ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) π))
    (q : T ⟶ B) [IsDominant q] (c : EtaleChart K X n) (f : X.functionFieldˣ)
    (cT : EtaleChart K T n) (D : CartierDivisor X) (C CΔ : CartierDivisor B) (d m ℓ : ℕ) :
    relativeAdjointCartier π q D C CΔ d m ℓ =
      (ℓ * m) • (d • (smoothCanonicalDivisor cT +
        principalCartierDivisor T (crepantPullbackFormUnit π hπ c f cT)) +
        crepantBoundaryCartier π hπ c f d D cT etaleCharts_cover) -
      (d * m * ℓ) • cartierPullback q C - (d * ℓ) • cartierPullback q CΔ := by
  rw [crepantBoundaryCartier_smooth_recombine]
  rfl

end MixedFujita
