/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierActualPullbackOrder

/-!
Construct the actual open where an actual Cartier section is locally a
generator. Its point criterion is independent of the local equation.
It is nonempty exactly when the source global section is nonzero. On an
integral target, the actual pulled section is nonzero exactly when the
actual scheme image meets this open; the generic target point supplies
the witness. This proves the nonzero-restriction interface for a future
Bertini curve, but does not construct that curve or its fixed degree.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

noncomputable def cartierSectionNonvanishingOpen (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    X.Opens :=
  ⨆ (U : X.Opens) (hU : Nonempty U),
    letI : Nonempty U := hU
    ⨆ (f : X.functionFieldˣ) (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U),
      X.basicOpen (cartierOpenCoefficient D U f hf U le_rfl
        (D.sheaf.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s))

theorem mem_cartierSectionNonvanishingOpen (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (x : X) :
    x ∈ cartierSectionNonvanishingOpen D s ↔
      ∃ (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f),
        IsUnit (cartierLocalCoefficient D x f hf s) := by
  simp only [cartierSectionNonvanishingOpen, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨U, hU, f, hf, hx⟩
    let : Nonempty U := hU
    have hxU : x ∈ U := (X.basicOpen_le _) hx
    refine ⟨f, CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hf hxU, ?_⟩
    rw [← cartierOpenCoefficient_germ_global D U f hf x hxU s]
    exact (X.mem_basicOpen _ x hxU).mp hx
  · rintro ⟨f, hf, hu⟩
    obtain ⟨U, hx, hU⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
    let : Nonempty U := ⟨⟨x, hx⟩⟩
    refine ⟨U, inferInstance, f, hU, ?_⟩
    apply (X.mem_basicOpen _ x hx).mpr
    rwa [cartierOpenCoefficient_germ_global]

theorem mem_cartierSectionNonvanishingOpen_iff_localCoefficient
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) (x : X)
    (f : X.functionFieldˣ) (hf : D.IsLocalEquationAt x f) :
    x ∈ cartierSectionNonvanishingOpen D s ↔ IsUnit (cartierLocalCoefficient D x f hf s) := by
  rw [mem_cartierSectionNonvanishingOpen]
  constructor
  · rintro ⟨g, hg, hu⟩
    obtain ⟨v, hv⟩ := cartierLocalCoefficient_change_frame D x f g hf hg
    rw [hv s]
    exact v.isUnit.mul hu
  · intro hu
    exact ⟨f, hf, hu⟩

theorem cartierSectionNonvanishingOpen_genericPoint_iff
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    genericPoint X ∈ cartierSectionNonvanishingOpen D s ↔ s ≠ 0 := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (genericPoint X)
  rw [mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (genericPoint X) f hf]
  change IsUnit (cartierLocalCoefficient D (genericPoint X) f hf s : X.functionField) ↔ s ≠ 0
  rw [isUnit_iff_ne_zero, cartierLocalCoefficient_ne_zero_iff]

theorem cartierSectionNonvanishingOpen_nonempty_iff
    (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    Nonempty (cartierSectionNonvanishingOpen D s) ↔ s ≠ 0 := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen D s x).mp hx
    exact (cartierLocalCoefficient_ne_zero_iff D x f hf s).mp hu.ne_zero
  · intro hs
    exact ⟨⟨genericPoint X, (cartierSectionNonvanishingOpen_genericPoint_iff D s).mpr hs⟩⟩

variable [IsIntegral Y]

theorem cartierActualGlobalPullback_ne_zero_of_image_mem_nonvanishingOpen
    (D : CartierDivisor X) (φ : Y ⟶ X) (s : Γ(D.sheaf, ⊤)) (y : Y)
    (hy : φ y ∈ cartierSectionNonvanishingOpen D s) :
    modulePullbackGlobalSections φ D.sheaf s ≠ 0 := by
  obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen D s (φ y)).mp hy
  apply (cartierStalkPullbackCoefficient_ne_zero_iff_actualGlobalPullback D φ y f hf s).mp
  rw [cartierStalkPullbackCoefficient_apply]
  exact (hu.map (φ.stalkMap y).hom).ne_zero

theorem cartierActualGlobalPullback_ne_zero_iff_image_meets_nonvanishingOpen
    (D : CartierDivisor X) (φ : Y ⟶ X) (s : Γ(D.sheaf, ⊤)) :
    modulePullbackGlobalSections φ D.sheaf s ≠ 0 ↔
      ∃ y : Y, φ y ∈ cartierSectionNonvanishingOpen D s := by
  constructor
  · intro hs
    let y : Y := genericPoint Y
    obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt (φ y)
    refine ⟨y, (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s (φ y) f hf).mpr ?_⟩
    have hn := (cartierStalkPullbackCoefficient_ne_zero_iff_actualGlobalPullback D φ y f hf s).mpr hs
    rw [cartierStalkPullbackCoefficient_apply] at hn
    have hu : IsUnit (φ.stalkMap y (cartierLocalCoefficient D (φ y) f hf s)) := by
      exact isUnit_iff_ne_zero.mpr hn
    exact (isUnit_map_iff (φ.stalkMap y).hom _).mp hu
  · rintro ⟨y, hy⟩
    exact cartierActualGlobalPullback_ne_zero_of_image_mem_nonvanishingOpen D φ s y hy

end MixedFujita
