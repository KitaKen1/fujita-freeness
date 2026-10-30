/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.CartierDivisor.Representation

/-!
Construct actual pullback of global module sections through the unit of the
scheme module pullback/pushforward adjunction. An actual Cartier line bundle
pulls back to an invertible sheaf. On an integral target it has an actual
Cartier-divisor representation, and global sections can be transported to
that divisor without changing whether the pulled-back section is zero.
Nonzero source sections need not pull back to nonzero sections. The local
coefficient compatibility with the actual stalk restriction, a Bertini
curve avoiding the zero divisor, and the ambient intersection-number
identification remain separate requirements.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {Y X : Scheme.{u}}

noncomputable def modulePullbackGlobalSections (φ : Y ⟶ X) (M : X.Modules) :
    Γ(M, ⊤) →+ Γ((Scheme.Modules.pullback φ).obj M, ⊤) :=
  (((Scheme.Modules.pullback φ).obj M).presheaf.map
    (eqToHom (φ.preimage_top).symm).op).hom.comp
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) ⊤).hom

theorem modulePullbackGlobalSections_apply (φ : Y ⟶ X) (M : X.Modules) (s : Γ(M, ⊤)) :
    modulePullbackGlobalSections φ M s =
      ((Scheme.Modules.pullback φ).obj M).presheaf.map (eqToHom (φ.preimage_top).symm).op
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction φ).unit.app M) ⊤ s) :=
  rfl

variable [IsIntegral X]

noncomputable def cartierPullbackLineBundle (D : CartierDivisor X) (φ : Y ⟶ X) :
    TauCeti.AlgebraicGeometry.InvertibleSheaf Y :=
  (TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback φ).obj D.toInvertibleSheaf

theorem cartierPullbackLineBundle_obj (D : CartierDivisor X) (φ : Y ⟶ X) :
    (cartierPullbackLineBundle D φ).obj = (Scheme.Modules.pullback φ).obj D.sheaf := by
  change ((TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback φ).obj D.toInvertibleSheaf).obj = _
  rw [TauCeti.AlgebraicGeometry.InvertibleSheaf.pullback_obj_obj, CartierDivisor.toInvertibleSheaf_obj]

theorem cartierPullbackSheaf_isInvertible (D : CartierDivisor X) (φ : Y ⟶ X) :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible Y
      ((Scheme.Modules.pullback φ).obj D.sheaf) := by
  let := D.isInvertible_sheaf
  exact TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback φ D.sheaf

variable [IsIntegral Y]

theorem cartierPullbackLineBundle_exists_cartierDivisor (D : CartierDivisor X) (φ : Y ⟶ X) :
    ∃ E : CartierDivisor Y, Nonempty ((Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf) := by
  simpa only [cartierPullbackLineBundle_obj] using
    CartierDivisor.exists_nonempty_iso_sheaf (cartierPullbackLineBundle D φ)

noncomputable def cartierPullbackGlobalSectionViaIso (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (e : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf) :
    Γ(D.sheaf, ⊤) →+ Γ(E.sheaf, ⊤) :=
  (Scheme.Modules.Hom.app e.hom ⊤).hom.comp (modulePullbackGlobalSections φ D.sheaf)

theorem cartierPullbackGlobalSectionViaIso_apply (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (e : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackGlobalSectionViaIso D φ E e s =
      Scheme.Modules.Hom.app e.hom ⊤ (modulePullbackGlobalSections φ D.sheaf s) := rfl

theorem cartierPullbackGlobalSectionViaIso_ne_zero_iff (D : CartierDivisor X) (φ : Y ⟶ X)
    (E : CartierDivisor Y) (e : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf)
    (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackGlobalSectionViaIso D φ E e s ≠ 0 ↔ modulePullbackGlobalSections φ D.sheaf s ≠ 0 := by
  have hi : Function.Injective (Scheme.Modules.Hom.app e.hom ⊤) :=
    (ConcreteCategory.bijective_of_isIso
      (((Scheme.Modules.toPresheaf Y).mapIso e).hom.app (op ⊤))).1
  rw [cartierPullbackGlobalSectionViaIso_apply]
  exact map_ne_zero_iff _ hi

end MixedFujita
