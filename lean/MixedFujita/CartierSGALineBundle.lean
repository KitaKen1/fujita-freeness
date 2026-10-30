/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleFramesToSGALineBundle
public import MixedFujita.CartierSectionNonvanishingOpen

/-!
Present an actual Cartier divisor as an SGA line bundle using chosen genuine local equations.
Its actual global sections become SGA sections with exactly the same nonvanishing opens.
The equations, cover, frame-transition units and compatibility are constructed internally.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} [IsIntegral X]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- A genuine local equation neighbourhood at each point, with no equation supplied by a caller. -/
structure CartierEquationOpenCover (D : CartierDivisor X) where
  U : X → X.Opens
  mem : ∀ x : X, x ∈ U x
  equation : X → X.functionFieldˣ
  equation_eq : ∀ x : X,
    letI : Nonempty (U x) := ⟨⟨x, mem x⟩⟩
    rationalUnitClass X (U x) (Additive.ofMul (equation x)) = D |_ U x

noncomputable def cartierEquationOpenCover (D : CartierDivisor X) : CartierEquationOpenCover D := by
  classical
  choose U hU hx f hf using fun x : X => D.exists_localEquation_le ⊤ (Opens.mem_top x)
  exact ⟨U, hx, f, hf⟩

variable {D : CartierDivisor X} (C : CartierEquationOpenCover D)

theorem cartierEquationOpenCover_iSup_eq_top : ⨆ x, C.U x = ⊤ := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, C.mem x⟩

noncomputable def cartierEquationOpenCover_frame (x : X) :
    D.sheaf.over (C.U x) ≅ SheafOfModules.unit (X.ringCatSheaf.over (C.U x)) :=
  letI : Nonempty (C.U x) := ⟨⟨x, C.mem x⟩⟩
  cartierOpenFrameIso D (C.U x) (C.equation x) (C.equation_eq x)

noncomputable def cartierEquationOpenCover_sgaLineBundle : X.LineBundle :=
  moduleFramesSGALineBundle D.sheaf C.U (cartierEquationOpenCover_frame C) (cartierEquationOpenCover_iSup_eq_top C)

noncomputable def cartierEquationOpenCover_sgaSection (s : Γ(D.sheaf, ⊤)) : (cartierEquationOpenCover_sgaLineBundle C).sections 1 :=
  moduleFramesSGASection D.sheaf C.U (cartierEquationOpenCover_frame C) (cartierEquationOpenCover_iSup_eq_top C) s

/-- The SGA section has exactly the actual Cartier nonvanishing open, for every global section. -/
theorem cartierEquationOpenCover_sgaSection_nonvanishingLocus (s : Γ(D.sheaf, ⊤)) :
    (cartierEquationOpenCover_sgaLineBundle C).nonvanishingLocus ((cartierEquationOpenCover_sgaSection C) s) =
      cartierSectionNonvanishingOpen D s := by
  ext y
  change y ∈ (⨆ x : X, X.basicOpen (((cartierEquationOpenCover_sgaSection C) s).val x)) ↔
    y ∈ cartierSectionNonvanishingOpen D s
  rw [Opens.mem_iSup]
  constructor
  · rintro ⟨x, hx⟩
    letI : Nonempty (C.U x) := ⟨⟨x, C.mem x⟩⟩
    change y ∈ X.basicOpen (cartierOpenCoefficient D (C.U x) (C.equation x)
      (C.equation_eq x) (C.U x) le_rfl
        (D.sheaf.presheaf.map (homOfLE le_top : C.U x ⟶ ⊤).op s)) at hx
    have hy : y ∈ C.U x := (X.basicOpen_le _) hx
    have hu := (X.mem_basicOpen _ y hy).mp hx
    rw [cartierOpenCoefficient_germ_global] at hu
    exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s y
      (C.equation x) (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
        (C.equation_eq x) hy)).mpr hu
  · intro hy
    refine ⟨y, ?_⟩
    letI : Nonempty (C.U y) := ⟨⟨y, C.mem y⟩⟩
    change y ∈ X.basicOpen (cartierOpenCoefficient D (C.U y) (C.equation y)
      (C.equation_eq y) (C.U y) le_rfl
        (D.sheaf.presheaf.map (homOfLE le_top : C.U y ⟶ ⊤).op s))
    apply (X.mem_basicOpen _ y (C.mem y)).mpr
    rw [cartierOpenCoefficient_germ_global]
    exact (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D s y
      (C.equation y) (CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq
        (C.equation_eq y) (C.mem y))).mp hy


/-- The SGA line bundle constructed from actual local Cartier equations. -/
noncomputable def cartierSGALineBundle (D : CartierDivisor X) : X.LineBundle :=
  (cartierEquationOpenCover_sgaLineBundle (cartierEquationOpenCover D))

noncomputable def cartierSGASection (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    (cartierSGALineBundle D).sections 1 := (cartierEquationOpenCover_sgaSection (cartierEquationOpenCover D)) s

/-- The new line-bundle presentation retains all actual global Cartier sections. -/
theorem cartierSGASection_bijective (D : CartierDivisor X) :
    Function.Bijective (cartierSGASection D) :=
  moduleFramesSGASection_bijective D.sheaf (cartierEquationOpenCover D).U
    (cartierEquationOpenCover_frame (cartierEquationOpenCover D)) (cartierEquationOpenCover_iSup_eq_top (cartierEquationOpenCover D))

noncomputable def cartierSGASectionEquiv (D : CartierDivisor X) :
    Γ(D.sheaf, ⊤) ≃ (cartierSGALineBundle D).sections 1 :=
  Equiv.ofBijective _ (cartierSGASection_bijective D)

theorem cartierSGASection_nonvanishingLocus (D : CartierDivisor X) (s : Γ(D.sheaf, ⊤)) :
    (cartierSGALineBundle D).nonvanishingLocus (cartierSGASection D s) =
      cartierSectionNonvanishingOpen D s :=
  (cartierEquationOpenCover_sgaSection_nonvanishingLocus (cartierEquationOpenCover D)) s

end MixedFujita
