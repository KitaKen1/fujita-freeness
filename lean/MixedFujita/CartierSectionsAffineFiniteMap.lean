/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierSectionsEmbedding

/-! 実切断のaffine非消滅開被覆から射影切断写像のaffine性と有限性。 See reports/check-235-cartier-sga-ampleness-dictionary.json for the verified scope. The original Cartier projective ampleness predicate is equivalent to the actual affine-open power-section criterion and to SGA ampleness of an actual module presentation. Actual affine pullback representatives preserve original ampleness. Numerical ampleness criteria, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Affine nonvanishing opens of every coordinate make the ACTUAL
Cartier section morphism affine; no coordinate-ring generation is assumed. -/
theorem cartierSectionsMap_isAffine_of_affine_nonvanishing
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] (D : CartierDivisor X)
    {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u} (idx : ι → Fin M)
    (hne : ∀ β, t (idx β) ≠ 0)
    (hcover : (⨆ β, cartierSectionNonvanishingOpen D (t (idx β))) = ⊤)
    (haff : ∀ q, IsAffineOpen (cartierSectionNonvanishingOpen D (t q))) :
    IsAffineHom (cartierSectionsMap K D t idx hne hcover) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨q, hq⟩ := polynomialProjective_exists_coordinate_chart M K y
  refine ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin M) K) (MvPolynomial.X q), hq,
    Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K q) one_pos, ?_⟩
  rw [cartierSectionsMap_preimage]
  exact haff q


/-- Properness upgrades the actual section morphism to a finite morphism
from affine nonvanishing opens, without a finite-map witness as input. -/
theorem cartierSectionsMap_isFinite_of_affine_nonvanishing
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (D : CartierDivisor X) {M : ℕ} (t : Fin M → Γ(D.sheaf, ⊤)) {ι : Type u}
    (idx : ι → Fin M) (hne : ∀ β, t (idx β) ≠ 0)
    (hcover : (⨆ β, cartierSectionNonvanishingOpen D (t (idx β))) = ⊤)
    (haff : ∀ q, IsAffineOpen (cartierSectionNonvanishingOpen D (t q))) :
    IsFinite (cartierSectionsMap K D t idx hne hcover) := by
  exact IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨cartierSectionsMap_isProper D t idx hne hcover,
      cartierSectionsMap_isAffine_of_affine_nonvanishing K D t idx hne hcover haff⟩

end MixedFujita
