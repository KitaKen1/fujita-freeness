/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.BlowUpLiftPoints
public import Hironaka.Resolution.Algebraic.Kol07.IsoRestrict

/-! Actual base opens and section-ring isomorphisms inside an isomorphism locus.
Every open inside its full inverse image is itself an inverse image of an actual
base open; no replacement neighborhood is supplied as an extra assumption. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {B Y : Scheme.{u}} (ρ : B ⟶ Y) (W : Y.Opens) [IsIso (ρ ∣_ W)]

/-- The actual section ring map is an isomorphism on every base open in the isomorphism locus. -/
theorem isIso_app_of_isIso_base_restrict (V : Y.Opens) (hVW : V ≤ W) : IsIso (ρ.app V) := by
  haveI : IsIso (ρ ∣_ V) := Hironaka.Sequence.isIso_restrict_of_le ρ hVW
  have h := morphismRestrict_appTop ρ V
  haveI : IsIso (ρ.app (V.ι ''ᵁ ⊤) ≫
      B.presheaf.map (eqToHom (image_morphismRestrict_preimage ρ V ⊤)).op) := by
    rw [← h]
    infer_instance
  have hApp : IsIso (ρ.app (V.ι ''ᵁ ⊤)) := IsIso.of_isIso_comp_right
    (ρ.app (V.ι ''ᵁ ⊤)) (B.presheaf.map (eqToHom (image_morphismRestrict_preimage ρ V ⊤)).op)
  exact Eq.mp (congrArg (fun U : Y.Opens => IsIso (ρ.app U)) V.ι_image_top) hApp

/-- Every open of the modified base contained in the isomorphism locus is the
full inverse image of an actual original-base open, with an actual ring isomorphism. -/
theorem exists_base_open_of_subset_isomorphism_locus (U : B.Opens) (hU : U ≤ ρ ⁻¹ᵁ W) :
    ∃ V : Y.Opens, V ≤ W ∧ ρ ⁻¹ᵁ V = U ∧ IsIso (ρ.app V) := by
  let e : (ρ ⁻¹ᵁ W) ≃ₜ W := (ρ ∣_ W).homeomorph
  have heval (a : ρ ⁻¹ᵁ W) : (e a).1 = ρ a.1 :=
    morphismRestrict_base_coe ρ W a
  have himage : ρ '' (U : Set B) =
      (fun w : W => w.1) '' (e '' ((fun b : ρ ⁻¹ᵁ W => b.1) ⁻¹' (U : Set B))) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨e ⟨b, hU hb⟩, ⟨⟨b, hU hb⟩, hb, rfl⟩, heval ⟨b, hU hb⟩⟩
    · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b.1, hb, (heval b).symm⟩
  have hopen : IsOpen (ρ '' (U : Set B)) := by
    rw [himage]
    exact W.isOpen.isOpenMap_subtype_val _
      (e.isOpenMap _ (U.isOpen.preimage continuous_subtype_val))
  let V : Y.Opens := ⟨ρ '' (U : Set B), hopen⟩
  have hVW : V ≤ W := by
    rintro y ⟨b, hb, rfl⟩
    exact hU hb
  have hpre : ρ ⁻¹ᵁ V = U := by
    ext b
    constructor
    · rintro ⟨a, ha, hab⟩
      have hbW : ρ b ∈ W := by rw [← hab]; exact hU ha
      have hea : e ⟨a, hU ha⟩ = e ⟨b, hbW⟩ := by
        apply Subtype.ext
        exact (heval ⟨a, hU ha⟩).trans (hab.trans (heval ⟨b, hbW⟩).symm)
      have hab' : a = b := congrArg Subtype.val (e.injective hea)
      exact hab' ▸ ha
    · intro hb
      exact ⟨b, hb, rfl⟩
  exact ⟨V, hVW, hpre, isIso_app_of_isIso_base_restrict ρ W V hVW⟩

end MixedFujita
