/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import SGA.Foundations.Cohomology.InvertibleSheaf
public import TauCeti.AlgebraicGeometry.CartierDivisor.Representation

/-!
The SGA module sheaf of any integer power of a line bundle is an actual TauCeti invertible
sheaf. The unit frames are the constructed SGA restriction isomorphisms. On an integral scheme,
the proved Cartier representation theorem therefore gives a genuine Cartier divisor and an
actual module-sheaf isomorphism. No Cartier representative is an additional premise.
This does not by itself identify different notions of ampleness or descend a source divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (L : X.LineBundle)

/-- Actual SGA rank-one restriction isomorphisms supply invertibility in the existing
module-sheaf implementation, for every integer power. -/
theorem sgaLineBundle_toModules_isInvertible (n : ℤ) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X (L.toModules n) := by
  apply TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_iff_exists_isOpenCover.mpr
  exact ⟨L.ι, L.U, IsOpenCover.mk L.iSup_eq_top, fun i => ⟨(L.restrictIso n i).symm⟩⟩

noncomputable def sgaLineBundleInvertibleSheaf (n : ℤ) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf X :=
  ⟨L.toModules n, sgaLineBundle_toModules_isInvertible L n⟩

variable [IsIntegral X]

/-- Every actual SGA line-bundle power has a genuine Cartier representative on an integral
scheme, with an isomorphism of the actual module sheaves. -/
theorem sgaLineBundle_exists_cartier_representation (n : ℤ) :
    ∃ H : CartierDivisor X, Nonempty (L.toModules n ≅ H.sheaf) :=
  CartierDivisor.exists_nonempty_iso_sheaf (sgaLineBundleInvertibleSheaf L n)

noncomputable def sgaLineBundleCartierDivisor : CartierDivisor X :=
  Classical.choose (sgaLineBundle_exists_cartier_representation L 1)

noncomputable def sgaLineBundleCartierIso :
    L.toModules 1 ≅ (sgaLineBundleCartierDivisor L).sheaf :=
  Classical.choice (Classical.choose_spec (sgaLineBundle_exists_cartier_representation L 1))

end MixedFujita
