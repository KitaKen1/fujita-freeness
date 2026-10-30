/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveHyperplaneSections
public import MixedFujita.DominantCartierPullback
public import MixedFujita.ProjectiveCartierSheafPullback

/-!
The actual Cartier divisor cut out by a homogeneous form commutes with composition by a
dominant morphism. Prove the equation identity on coordinate opens and the rational-unit
identity through the actual function-field map, then compare local equations at every point.
This supplies an explicit Cartier pullback identity for a Stein target's hyperplane divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {R : Type u} [CommRing R] {n : ℕ} {T Y : Scheme.{u}}
  (ρ : T ⟶ Y) (e : Y ⟶ polynomialProjectiveScheme n R)

theorem projectivePullbackCoordinateOpen_comp (k : Fin n) :
    projectivePullbackCoordinateOpen (ρ ≫ e) k = ρ ⁻¹ᵁ projectivePullbackCoordinateOpen e k := rfl

theorem projectivePullbackHomogeneousEquation_comp_appLE (k : Fin n) (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) :
    projectivePullbackHomogeneousEquation (ρ ≫ e) k d f hf =
      ρ.appLE (projectivePullbackCoordinateOpen e k)
        (projectivePullbackCoordinateOpen (ρ ≫ e) k) le_rfl
        (projectivePullbackHomogeneousEquation e k d f hf) := by
  rw [← projectivePullbackHomogeneousEquation_comp e ρ d f hf k]
  simp [Scheme.Hom.appLE]
  exact (T.presheaf.map_id_apply
    (op (projectivePullbackCoordinateOpen (ρ ≫ e) k))
      (ρ.app (projectivePullbackCoordinateOpen e k)
        (projectivePullbackHomogeneousEquation e k d f hf))).symm

variable [IsIntegral T] [IsIntegral Y] [IsDominant ρ]

theorem projectiveHomogeneous_generic_comp (f : MvPolynomial (Fin n) R)
    (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    f ∉ ((ρ ≫ e) (genericPoint T)).asHomogeneousIdeal := by
  simpa only [Scheme.Hom.comp_apply, dominant_map_genericPoint] using hfgen

theorem projectivePullbackHomogeneousRationalUnit_comp (k : Fin n)
    [Nonempty (projectivePullbackCoordinateOpen e k)]
    [Nonempty (projectivePullbackCoordinateOpen (ρ ≫ e) k)]
    (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    Units.map (dominantFunctionFieldMap ρ).hom.toMonoidHom
        (projectivePullbackHomogeneousRationalUnit e ⟨k, inferInstance⟩ d f hf hd hfgen) =
      projectivePullbackHomogeneousRationalUnit (ρ ≫ e) ⟨k, inferInstance⟩ d f hf hd
        (projectiveHomogeneous_generic_comp ρ e f hfgen) := by
  apply Units.ext
  simp only [Units.coe_map, MonoidHom.coe_coe, projectivePullbackHomogeneousRationalUnit,
    regularEquationRationalUnit_val]
  exact (dominantFunctionFieldMap_germ ρ (projectivePullbackCoordinateOpen e k)
    (projectivePullbackCoordinateOpen (ρ ≫ e) k) le_rfl
      (projectivePullbackHomogeneousEquation e k d f hf)).trans
        (congrArg (T.germToFunctionField (projectivePullbackCoordinateOpen (ρ ≫ e) k))
          (projectivePullbackHomogeneousEquation_comp_appLE ρ e k d f hf).symm)

/-- An actual homogeneous Cartier cut commutes with dominant pullback, with its generic
nonvanishing on the composite constructed rather than assumed. -/
theorem cartierPullback_projectivePullbackHomogeneousCartier (d : ℕ)
    (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    cartierPullback ρ (projectivePullbackHomogeneousCartier e d f hf hd hfgen) =
      projectivePullbackHomogeneousCartier (ρ ≫ e) d f hf hd
        (projectiveHomogeneous_generic_comp ρ e f hfgen) := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  have ht : ρ t ∈ ⨆ k : Fin n, projectivePullbackCoordinateOpen e k := by
    rw [projectivePullbackCoordinateOpen_cover]
    trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.mp ht
  letI : Nonempty (projectivePullbackCoordinateOpen e k) := ⟨⟨ρ t, hk⟩⟩
  letI : Nonempty (projectivePullbackCoordinateOpen (ρ ≫ e) k) := ⟨⟨t, hk⟩⟩
  refine ⟨projectivePullbackHomogeneousRationalUnit (ρ ≫ e) ⟨k, inferInstance⟩ d f hf hd
    (projectiveHomogeneous_generic_comp ρ e f hfgen), ?_, ?_⟩
  · rw [← projectivePullbackHomogeneousRationalUnit_comp ρ e k d f hf hd hfgen]
    apply cartierPullback_isLocalEquationAt
    exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
      (projectivePullbackHomogeneousCartier_restrict e d f hf hd hfgen ⟨k, inferInstance⟩).symm hk
  · exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
      (projectivePullbackHomogeneousCartier_restrict (ρ ≫ e) d f hf hd
        (projectiveHomogeneous_generic_comp ρ e f hfgen) ⟨k, inferInstance⟩).symm hk

theorem cartierPullback_projectiveHyperplaneCartier (f : MvPolynomial (Fin n) R)
    (hf : f.IsHomogeneous 1) (hfgen : f ∉ (e (genericPoint Y)).asHomogeneousIdeal) :
    cartierPullback ρ (projectiveHyperplaneCartier e f hf hfgen) =
      projectiveHyperplaneCartier (ρ ≫ e) f hf (projectiveHomogeneous_generic_comp ρ e f hfgen) :=
  cartierPullback_projectivePullbackHomogeneousCartier ρ e 1 f hf one_pos hfgen

end MixedFujita
