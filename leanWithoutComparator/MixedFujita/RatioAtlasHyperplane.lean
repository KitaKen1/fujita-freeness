/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RatioAtlasEmbedding
public import MixedFujita.CartierSectionsEmbedding
public import MixedFujita.ProjectiveHyperplaneSections

/-!
The hyperplane divisors of the morphism to projective space given by an atlas of ratios
(step 10, R1).

For an atlas of ratios `c_β(q)` on opens `V_β` (`ratioAtlasMap`), the coordinate open
of `X_{idx β}` pulls back to `V_β`, and the chart equation of `X_q` there pulls back to `c_β(q)`
(`ratioAtlasMap_equation_germToFunctionField`, as for the morphism of sections of a divisor).
Hence the hyperplane divisor of a coordinate `X_{q₀}` has the local equation `c_β(q₀)` at every
point of `V_β` (`ratioAtlasMap_hyperplane_isLocalEquationAt`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open OAI.PiExponentSeshadri.Projective

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]
  {M : ℕ} {ι : Type u} (idx : ι → Fin M) (V : ι → Y.Opens) (hV : (⨆ β, V β) = ⊤)
  (c : ∀ β, Fin M → Γ(Y, V β)) (hnorm : ∀ β, c β (idx β) = 1)
  (hcocycle : ∀ β γ q,
    Y.presheaf.map (homOfLE (inf_le_right : V β ⊓ V γ ≤ V γ)).op (c γ q) =
      Y.presheaf.map (homOfLE (inf_le_right : V β ⊓ V γ ≤ V γ)).op (c γ (idx β)) *
        Y.presheaf.map (homOfLE (inf_le_left : V β ⊓ V γ ≤ V β)).op (c β q))

include hV in
/-- The coordinate open of `X_{idx β}` pulls back to the chart `V_β`. -/
theorem ratioAtlasMap_coordinateOpen (hbasic : ∀ β γ, Y.basicOpen (c γ (idx β)) ≤ V β)
    (β : ι) :
    projectivePullbackCoordinateOpen (ratioAtlasMap K idx V hV c hnorm hcocycle) (idx β) = V β :=
  ratioAtlasMap_preimage idx V hV c hnorm hcocycle hbasic β

variable [IsIntegral Y]

/-- **The chart equation of `X_q` on the chart of `X_{idx β}` pulls back to `c_β(q)`.** -/
theorem ratioAtlasMap_equation_germToFunctionField (β : ι) (q : Fin M) [Nonempty (V β)]
    [Nonempty (projectivePullbackCoordinateOpen (ratioAtlasMap K idx V hV c hnorm hcocycle)
      (idx β))] :
    Y.germToFunctionField
        (projectivePullbackCoordinateOpen (ratioAtlasMap K idx V hV c hnorm hcocycle) (idx β))
        (projectivePullbackHomogeneousEquation (ratioAtlasMap K idx V hV c hnorm hcocycle) (idx β) 1
          (MvPolynomial.X q) (MvPolynomial.isHomogeneous_X K q)) =
      Y.germToFunctionField (V β) (c β q) := by
  have hu : IsUnit ((MvPolynomial.eval₂Hom ((V β).ι.appTop.hom.comp (schemeBaseScalars K Y))
      (fun q => opensSectionToTop _ (c β q))) (MvPolynomial.X (idx β))) := by
    simpa only [MvPolynomial.eval₂Hom_X', hnorm, map_one] using
      (isUnit_one : IsUnit (1 : Γ((V β).toScheme, ⊤)))
  have hmem : MvPolynomial.X q ∈ MvPolynomial.homogeneousSubmodule (Fin M) K (1 • 1) := by
    simpa using MvPolynomial.isHomogeneous_X K q
  have H := evalAway_mk_clear
    (MvPolynomial.eval₂Hom ((V β).ι.appTop.hom.comp (schemeBaseScalars K Y))
      (fun q => opensSectionToTop _ (c β q)))
    (coordinates_X_mem (K := K) (idx β)) hu 1 (MvPolynomial.X q) hmem
  exact germToFunctionField_app_awayToSection_of_chart
    (ratioAtlasMap K idx V hV c hnorm hcocycle) (V β) (idx β) _
    (ratioAtlasMap_ι idx V hV c hnorm hcocycle β) _ (c β q)
    (by simpa only [MvPolynomial.eval₂Hom_X', hnorm, map_one, one_pow, mul_one] using H)

include hV in
/-- **The hyperplane divisor of `X_{q₀}` has the local equation `c_β(q₀)` on `V_β`.** -/
theorem ratioAtlasMap_hyperplane_isLocalEquationAt
    (hbasic : ∀ β γ, Y.basicOpen (c γ (idx β)) ≤ V β) (q₀ : Fin M)
    (hggen : MvPolynomial.X q₀ ∉
      ((ratioAtlasMap K idx V hV c hnorm hcocycle) (genericPoint Y)).asHomogeneousIdeal)
    (β : ι) [Nonempty (V β)] (hc : c β q₀ ≠ 0) (y : Y) (hy : y ∈ V β) :
    (projectiveHyperplaneCartier (ratioAtlasMap K idx V hV c hnorm hcocycle) (MvPolynomial.X q₀)
        (MvPolynomial.isHomogeneous_X K q₀) hggen).IsLocalEquationAt y
      (regularEquationRationalUnit Y (V β) (c β q₀) hc) := by
  have hcoord := ratioAtlasMap_coordinateOpen (K := K) idx V hV c hnorm hcocycle hbasic β
  have hne : Nonempty (projectivePullbackCoordinateOpen
      (ratioAtlasMap K idx V hV c hnorm hcocycle) (idx β)) := by
    rw [hcoord]
    infer_instance
  have hy' : y ∈ projectivePullbackCoordinateOpen
      (ratioAtlasMap K idx V hV c hnorm hcocycle) (idx β) := by
    rw [hcoord]
    exact hy
  have h := projectiveHyperplane_isLocalEquationAt (ratioAtlasMap K idx V hV c hnorm hcocycle)
    (MvPolynomial.X q₀) (MvPolynomial.isHomogeneous_X K q₀) hggen ⟨idx β, hne⟩ y hy'
  have hu : projectiveHyperplaneUnit (ratioAtlasMap K idx V hV c hnorm hcocycle)
      (MvPolynomial.X q₀) (MvPolynomial.isHomogeneous_X K q₀) hggen ⟨idx β, hne⟩ =
      regularEquationRationalUnit Y (V β) (c β q₀) hc := by
    apply Units.ext
    rw [regularEquationRationalUnit_val]
    exact ratioAtlasMap_equation_germToFunctionField (K := K) idx V hV c hnorm hcocycle β q₀
  rw [hu] at h
  exact h

end MixedFujita
