/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupBaseFieldCoordinates
public import MixedFujita.HironakaSNCDictionary
public import Hironaka.Scheme.Smooth.GraphCompletion
public import Hironaka.Scheme.Smooth.Adapted

/-! Compare polynomial sections with the actual stalk maps of coordinate
morphisms, including the passage through an affine open of the source. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Scheme.Hom
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}

theorem germ_sectionsHom {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (σ : Y ⟶ Spec (.of R)) (V : Y.Opens) (p : Y) (hp : p ∈ V) (r : R) :
    Y.presheaf.germ V p hp (sectionsHom σ V r) =
      σ.stalkMap p ((Spec (.of R)).presheaf.germ ⊤ (σ p) trivial
        ((Scheme.ΓSpecIso (.of R)).inv r)) := by
  exact σ.germ_appLE_apply ⊤ V le_top hp trivial _

theorem germ_sectionsHom_comp {R : Type u} [CommRing R] {Y W : Scheme.{u}}
    (a : Y ⟶ W) (σ : W ⟶ Spec (.of R)) (V : Y.Opens) (p : Y) (hp : p ∈ V)
    (r : R) :
    Y.presheaf.germ V p hp (sectionsHom (a ≫ σ) V r) =
      a.stalkMap p (W.presheaf.germ ⊤ (a p) trivial (sectionsHom σ ⊤ r)) := by
  rw [germ_sectionsHom, germ_sectionsHom]
  exact congrArg (fun g => g ((Spec (.of R)).presheaf.germ ⊤ ((a ≫ σ) p) trivial
    ((Scheme.ΓSpecIso (.of R)).inv r))) (Scheme.Hom.stalkMap_comp a σ p)

theorem germ_sectionsHom_toAffineSpace {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (U : X.Opens) (v : Fin n → Γ(X, U))
    (a : Y ⟶ U.toScheme) (V : Y.Opens) (p : Y) (hp : p ∈ V) (i : Fin n) :
    Y.presheaf.germ V p hp (sectionsHom (a ≫ toAffineSpace f U v) V (MvPolynomial.X i)) =
      (a ≫ U.ι).stalkMap p (X.presheaf.germ U ((a ≫ U.ι) p) (a p).2 (v i)) := by
  rw [germ_sectionsHom_comp]
  have hsec : sectionsHom (toAffineSpace f U v) ⊤ (MvPolynomial.X i) = U.topIso.inv (v i) := by
    change (toAffineSpace f U v).appLE ⊤ ⊤ le_top _ = _
    have happ : (toAffineSpace f U v).appLE ⊤ ⊤ le_top = (toAffineSpace f U v).appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
      exact Category.comp_id _
    rw [happ]
    exact toAffineSpace_appTop_X f U v i
  rw [hsec]
  have hg := congrArg (fun g => g (v i)) (Scheme.Opens.germ_comp_ι_stalkMap U (a p))
  simp only [CommRingCat.comp_apply] at hg
  rw [← hg]
  exact (congrArg (fun g => g (X.presheaf.germ U ((a ≫ U.ι) p) (a p).2 (v i)))
    (Scheme.Hom.stalkMap_comp a U.ι p)).symm

theorem stalkMap_germ_congr {X Y : Scheme.{u}} {a b : Y ⟶ X} (hab : a = b)
    (U : X.Opens) (p : Y) (ha : a p ∈ U) (hb : b p ∈ U) (s : Γ(X, U)) :
    a.stalkMap p (X.presheaf.germ U (a p) ha s) =
      b.stalkMap p (X.presheaf.germ U (b p) hb s) := by
  subst b
  rfl

end MixedFujita
