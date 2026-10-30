/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreProjectiveEmbedding
public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.DominantCartierPullback
public import MixedFujita.TwistedDifferentialForms

/-!
Ampleness from local equations (step 10, R4-3).

Let `e : Y → ℙ_κ` be a closed immersion over a field and `X_{k₀}` a coordinate with a nonempty
chart. If on the charts `U_i ⊆ D₊(X_{k(i)})` of a finite cover a divisor `D` has local equations
`λ_i` with `λ_i^{m'} = w_i · (X_{k₀}/X_{k(i)}) · f` for units `w_i` on `U_i` and one rational
function `f`, then `m' • D` and `H_{X_{k₀}} + div f` have the common local equations `λ_i^{m'}`
(`cartierDivisor_eq_of_isLocalEquationAt`), so `D` is ample
(`cartierIsAmpleProj_of_localEquations`). The chart equation of `X_k` on its own chart is `1`
(`projectivePullbackHomogeneousEquation_X_self`).

On the fibre `T_κ` the local equations `λ_i` of `m (Q_κ − K_κ) − Σ a_k E_{k,κ}` are the images of
functions on the closure `T_A`, and the relation is the image of one on `T_A` spread from `T`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {κ : Type u} [Field κ] {P : ℕ} {Y : Scheme.{u}}

/-- The chart equation of a coordinate on its own chart is `1`. -/
theorem projectivePullbackHomogeneousEquation_X_self (e : Y ⟶ polynomialProjectiveScheme P κ)
    (k : Fin P) :
    projectivePullbackHomogeneousEquation e k 1 (MvPolynomial.X k)
      (MvPolynomial.isHomogeneous_X κ k) = 1 := by
  rw [projectivePullbackHomogeneousEquation_eq_affine, projectiveDehomogenize_X_self, map_one]

/-- **A divisor whose local equations are, up to units, those of a hyperplane section plus a
principal divisor is ample.** -/
theorem cartierIsAmpleProj_of_localEquations [IsIntegral Y] [Y.Over (Spec (CommRingCat.of κ))]
    (e : Y ⟶ polynomialProjectiveScheme P κ) [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase P κ = Y ↘ Spec (CommRingCat.of κ)) (k₀ : Fin P)
    [Nonempty (projectivePullbackCoordinateOpen e k₀)] (D : CartierDivisor Y) (m' : ℕ)
    (hm' : 1 ≤ m') (f : Y.functionFieldˣ) {N : ℕ} (U : Fin N → Y.Opens) (hcov : ⨆ i, U i = ⊤)
    (kk : Fin N → Fin P) (hUk : ∀ i, U i ≤ projectivePullbackCoordinateOpen e (kk i))
    [hne : ∀ i, Nonempty (U i)] (lam : Fin N → Y.functionFieldˣ)
    (hlam : ∀ i, ∀ y ∈ U i, D.IsLocalEquationAt y (lam i)) (w : ∀ i, Γ(Y, U i)ˣ)
    (hw : ∀ i, haveI : Nonempty (projectivePullbackCoordinateOpen e (kk i)) :=
        ⟨⟨(Classical.arbitrary (U i)).1, hUk i (Classical.arbitrary (U i)).2⟩⟩
      ((lam i ^ m' : Y.functionFieldˣ) : Y.functionField) =
        Y.germToFunctionField (U i) (w i : Γ(Y, U i)) *
          Y.germToFunctionField (projectivePullbackCoordinateOpen e (kk i))
            (projectivePullbackHomogeneousEquation e (kk i) 1 (MvPolynomial.X k₀)
              (MvPolynomial.isHomogeneous_X κ k₀)) * f) :
    CartierIsAmpleProj κ D := by
  classical
  have hggen := X_notMem_genericPoint_of_nonempty e k₀
  refine ⟨m', hm', P, e, inferInstance, he, MvPolynomial.X k₀, MvPolynomial.isHomogeneous_X κ k₀,
    hggen, f, ?_⟩
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  have ht : t ∈ ⨆ i, U i := by rw [hcov]; exact Opens.mem_top t
  obtain ⟨i, hti⟩ := Opens.mem_iSup.mp ht
  have hV : t ∈ projectivePullbackCoordinateOpen e (kk i) := hUk i hti
  have : Nonempty (projectivePullbackCoordinateOpen e (kk i)) := ⟨⟨t, hV⟩⟩
  refine ⟨lam i ^ m', isLocalEquationAt_nsmul_pow (hlam i t hti) m', ?_⟩
  have hH := projectiveHyperplane_isLocalEquationAt e (MvPolynomial.X k₀)
    (MvPolynomial.isHomogeneous_X κ k₀) hggen ⟨kk i, ⟨⟨t, hV⟩⟩⟩ t hV
  have hHf := hH.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor t f)
  have hHfw := isLocalEquationAt_regularUnit_mul hHf (U i) hti (w i)
  convert hHfw using 1
  apply Units.ext
  rw [hw i, Units.val_mul, Units.val_mul, regularUnitToFunctionField_apply, mul_assoc]
  rfl

end MixedFujita
