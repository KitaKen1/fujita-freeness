/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.AffineOpenIdealPullback
public import MixedFujita.ProjectivePointedCartierCut

/-!
The glued source Cartier ideal equals the actual Scheme pullback of the
projective hypersurface ideal, including its multiplicities. Its subscheme
is therefore the actual fiber product, and its quotient complex is short
exact. Pointed degree-one cuts have these properties without a supplied
Cartier assumption. Smooth integral cuts and fixed-class Bertini flags
remain separate obligations.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {n : ℕ} {R : Type u} [CommRing R] {Y : Scheme.{u}} [IsIntegral Y]
  (e : Y ⟶ polynomialProjectiveScheme n R) [IsAffineHom e]
  (d : ℕ) (f : MvPolynomial (Fin n) R) (hf : f.IsHomogeneous d) (hd : 0 < d)
  (hgeneric : f ∉ (e (genericPoint Y)).asHomogeneousIdeal)

omit [IsIntegral Y] in
theorem projectiveHypersurfacePullback_coordinate_ideal
    (k : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)}) :
    ((projectiveHypersurfaceIdealSheaf f d hf).comap e).ideal
        (projectivePullbackNonemptyCoordinateAffineOpen e k) =
      Ideal.span ({projectivePullbackHomogeneousEquation e k.val d f hf} :
        Set Γ(Y, projectivePullbackNonemptyCoordinateOpen e k)) := by
  dsimp only [projectivePullbackNonemptyCoordinateAffineOpen,
    projectivePullbackNonemptyCoordinateOpen, projectivePullbackCoordinateOpen,
    projectivePullbackHomogeneousEquation]
  rw [idealSheaf_comap_affineOpen _ e (polynomialProjectiveCoordinateAffineOpen R k.val),
    projectiveHypersurfaceIdealSheaf_coordinate_ideal, Ideal.map_span, Set.image_singleton]

theorem projectivePullbackCartierIdealSheaf_eq_hypersurface_comap :
    projectivePullbackCartierIdealSheaf e d f hf hd hgeneric =
      (projectiveHypersurfaceIdealSheaf f d hf).comap e := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top
    (projectivePullbackNonemptyCoordinateAffineOpen e)
    (projectivePullbackNonemptyCoordinateOpen_cover e)
  intro k
  rw [projectivePullbackCartierIdealSheaf_coordinate_ideal,
    projectiveHypersurfacePullback_coordinate_ideal]

noncomputable def projectivePullbackCartierCutIso :
    (projectivePullbackCartierIdealSheaf e d f hf hd hgeneric).subscheme ≅
      CategoryTheory.Limits.pullback e (projectiveHypersurfaceIdealSheaf f d hf).subschemeι :=
  idealSheafPullbackIso _ _ _
    (projectivePullbackCartierIdealSheaf_eq_hypersurface_comap e d f hf hd hgeneric).symm

theorem projectivePullbackCartierCutIso_hom_fst :
    (projectivePullbackCartierCutIso e d f hf hd hgeneric).hom ≫
        CategoryTheory.Limits.pullback.fst _ _ =
      (projectivePullbackCartierIdealSheaf e d f hf hd hgeneric).subschemeι :=
  idealSheafPullbackIso_hom_fst _ _ _ _

noncomputable def projectiveHypersurfacePullbackIdealPresentation :
    InvertibleIdealPresentation ((projectiveHypersurfaceIdealSheaf f d hf).comap e) :=
  (projectivePullbackCartierIdealSheaf_eq_hypersurface_comap e d f hf hd hgeneric) ▸
    projectivePullbackCartierIdealPresentation e d f hf hd hgeneric

theorem projectiveHypersurfacePullback_quotient_shortExact :
    (invertibleIdealSubschemeShortComplex
      (projectiveHypersurfacePullbackIdealPresentation e d f hf hd hgeneric)).ShortExact :=
  invertibleIdealSubschemeShortComplex_shortExact _

theorem polynomialProjective_closedImmersion_pointed_hypersurfacePullback
    {K : Type u} [Field K] [IsAlgClosed K] {n : ℕ}
    {Y : Scheme.{u}} [IsIntegral Y] [Nontrivial Y]
    (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
    (x : Y) (hx : IsClosed {x}) (Z : Set Y) (hZ : Z.Finite) (hxZ : x ∉ Z) :
    ∃ f : MvPolynomial.homogeneousSubmodule (Fin n) K 1,
      let I := (projectiveHypersurfaceIdealSheaf f.val 1 f.property).comap e
      Nonempty (InvertibleIdealPresentation I) ∧
        x ∈ Set.range I.subschemeι ∧ ∀ y ∈ Z, y ∉ Set.range I.subschemeι := by
  obtain ⟨f, hgeneric, hpres, hfx, hfy⟩ :=
    polynomialProjective_closedImmersion_pointed_effectiveCartierCut e x hx Z hZ hxZ
  refine ⟨f, ?_⟩
  exact (projectivePullbackCartierIdealSheaf_eq_hypersurface_comap e 1 f.val f.property
    Nat.zero_lt_one hgeneric) ▸ ⟨hpres, hfx, hfy⟩

end MixedFujita
