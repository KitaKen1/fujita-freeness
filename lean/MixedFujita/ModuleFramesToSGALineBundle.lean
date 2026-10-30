/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ModuleOpenFrameCoefficients
public import SGA.Foundations.Projective.ProjectiveSpaceHom

/-!
Actual unit frames of a module sheaf give an SGA line bundle with regular transition units.
The transitions are constructed from the frame linear equivalences; their restriction and
cocycle identities are proved. Actual global module sections then give compatible SGA sections.
This bridges the module-sheaf Cartier implementation to SGA's projective-space morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
  (e : ∀ i, M.over (U i) ≅ SheafOfModules.unit (X.ringCatSheaf.over (U i)))

/-- The actual regular unit changing two module frames on any common subopen. -/
noncomputable def moduleFrameTransitionUnit (i j : ι) (W : X.Opens)
    (hWi : W ≤ U i) (hWj : W ≤ U j) : Γ(X, W)ˣ :=
  linearSelfFrameUnit ((moduleOverFrameCoefficient M (U j) (e j) W hWj).symm.trans
    (moduleOverFrameCoefficient M (U i) (e i) W hWi))

theorem moduleFrameTransitionUnit_mul (i j : ι) (W : X.Opens)
    (hWi : W ≤ U i) (hWj : W ≤ U j) (s : Γ(M, W)) :
    (moduleFrameTransitionUnit M U e i j W hWi hWj : Γ(X, W)) *
        moduleOverFrameCoefficient M (U j) (e j) W hWj s =
      moduleOverFrameCoefficient M (U i) (e i) W hWi s := by
  rw [moduleFrameTransitionUnit, linearSelfFrameUnit_mul]
  exact (moduleOverFrameCoefficient M (U i) (e i) W hWi).congr_arg
    ((moduleOverFrameCoefficient M (U j) (e j) W hWj).symm_apply_apply s)

/-- Restriction of a frame transition is the transition of the same frames on the smaller open. -/
theorem moduleFrameTransitionUnit_restrict (i j : ι) {W V : X.Opens}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hVW : V ≤ W) :
    X.presheaf.map (homOfLE hVW).op
        (moduleFrameTransitionUnit M U e i j W hWi hWj : Γ(X, W)) =
      (moduleFrameTransitionUnit M U e i j V (hVW.trans hWi) (hVW.trans hWj) : Γ(X, V)) := by
  let s := (moduleOverFrameCoefficient M (U j) (e j) W hWj).symm 1
  have hs : moduleOverFrameCoefficient M (U j) (e j) W hWj s = 1 :=
    LinearEquiv.apply_symm_apply _ _
  have hW := moduleFrameTransitionUnit_mul M U e i j W hWi hWj s
  rw [hs, mul_one] at hW
  have hsV : moduleOverFrameCoefficient M (U j) (e j) V (hVW.trans hWj)
      (M.presheaf.map (homOfLE hVW).op s) = 1 := by
    rw [moduleOverFrameCoefficient_restrict M (U j) (e j) hWj (homOfLE hVW), hs, map_one]
  have hV := moduleFrameTransitionUnit_mul M U e i j V
    (hVW.trans hWi) (hVW.trans hWj) (M.presheaf.map (homOfLE hVW).op s)
  rw [hsV, mul_one] at hV
  rw [hW, ← moduleOverFrameCoefficient_restrict M (U i) (e i) hWi (homOfLE hVW)]
  exact hV.symm

/-- The actual transition units satisfy the cocycle equation on every common subopen. -/
theorem moduleFrameTransitionUnit_cocycle (i j k : ι) (W : X.Opens)
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hWk : W ≤ U k) :
    (moduleFrameTransitionUnit M U e i j W hWi hWj : Γ(X, W)) *
        (moduleFrameTransitionUnit M U e j k W hWj hWk : Γ(X, W)) =
      (moduleFrameTransitionUnit M U e i k W hWi hWk : Γ(X, W)) := by
  let s := (moduleOverFrameCoefficient M (U k) (e k) W hWk).symm 1
  have hs : moduleOverFrameCoefficient M (U k) (e k) W hWk s = 1 :=
    LinearEquiv.apply_symm_apply _ _
  have hij := moduleFrameTransitionUnit_mul M U e i j W hWi hWj s
  have hjk := moduleFrameTransitionUnit_mul M U e j k W hWj hWk s
  have hik := moduleFrameTransitionUnit_mul M U e i k W hWi hWk s
  rw [hs, mul_one] at hjk hik
  rw [← hjk] at hij
  exact hij.trans hik.symm

/-- The SGA line bundle presented by an actual open cover of unit module frames. -/
noncomputable def moduleFramesSGALineBundle (hU : ⨆ i, U i = ⊤) : X.LineBundle where
  ι := ι
  U := U
  iSup_eq_top := hU
  g i j := moduleFrameTransitionUnit M U e i j (U i ⊓ U j) inf_le_left inf_le_right
  cocycle i j k := by
    simp only [moduleFrameTransitionUnit_restrict]
    exact moduleFrameTransitionUnit_cocycle M U e i j k _ _ _ _

/-- An actual global module section gives a compatible degree-one SGA line-bundle section. -/
noncomputable def moduleFramesSGASection (hU : ⨆ i, U i = ⊤) (s : Γ(M, ⊤)) :
    (moduleFramesSGALineBundle M U e hU).sections 1 := by
  dsimp only [Scheme.LineBundle.sections, moduleFramesSGALineBundle]
  refine ⟨fun i => moduleOverFrameCoefficient M (U i) (e i) (U i) le_rfl
    (M.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s), ?_⟩
  intro i j
  change X.presheaf.map (homOfLE inf_le_left).op _ =
    (moduleFrameTransitionUnit M U e i j (U i ⊓ U j) inf_le_left inf_le_right :
      Γ(X, U i ⊓ U j)) ^ 1 * X.presheaf.map (homOfLE inf_le_right).op _
  rw [pow_one,
    ← moduleOverFrameCoefficient_restrict M (U i) (e i) le_rfl (homOfLE inf_le_left),
    ← moduleOverFrameCoefficient_restrict M (U j) (e j) le_rfl (homOfLE inf_le_right),
    moduleFrameTransitionUnit_mul]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Every compatible SGA section comes from exactly one actual global module section. -/
theorem moduleFramesSGASection_bijective (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (moduleFramesSGASection M U e hU) := by
  constructor
  · intro s t h
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ U ⊤
      (fun _ => homOfLE le_top) hU.ge s t
    intro i
    apply (moduleOverFrameCoefficient M (U i) (e i) (U i) le_rfl).injective
    exact congrArg (fun z => z.val i) h
  · intro t
    dsimp only [Scheme.LineBundle.sections, moduleFramesSGALineBundle] at t
    let sf (i : ι) : Γ(M, U i) :=
      (moduleOverFrameCoefficient M (U i) (e i) (U i) le_rfl).symm (t.val i)
    have hcompat : TopCat.Presheaf.IsCompatible M.presheaf U sf := by
      intro i j
      apply (moduleOverFrameCoefficient M (U i) (e i) (U i ⊓ U j) inf_le_left).injective
      calc
        _ = X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (t.val i) := by
          exact (moduleOverFrameCoefficient_restrict M (U i) (e i) le_rfl
            (Opens.infLELeft (U i) (U j)) (sf i)).trans
              (congrArg (X.presheaf.map (Opens.infLELeft (U i) (U j)).op)
                ((moduleOverFrameCoefficient M (U i) (e i) (U i) le_rfl).apply_symm_apply _))
        _ = (moduleFrameTransitionUnit M U e i j (U i ⊓ U j)
              inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) *
            X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (t.val j) := by
          simpa only [pow_one] using t.property i j
        _ = (moduleFrameTransitionUnit M U e i j (U i ⊓ U j)
              inf_le_left inf_le_right : Γ(X, U i ⊓ U j)) *
            moduleOverFrameCoefficient M (U j) (e j) (U i ⊓ U j) inf_le_right
              (M.presheaf.map (homOfLE inf_le_right).op (sf j)) := by
          rw [moduleOverFrameCoefficient_restrict M (U j) (e j) le_rfl
            (homOfLE inf_le_right)]
          congr 2
          exact (moduleOverFrameCoefficient M (U j) (e j) (U j) le_rfl).apply_symm_apply _ |>.symm
        _ = _ := moduleFrameTransitionUnit_mul M U e i j (U i ⊓ U j)
          inf_le_left inf_le_right _
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨M.presheaf, M.isSheaf⟩ U ⊤
      (fun _ => homOfLE le_top) hU.ge sf hcompat
    refine ⟨s, ?_⟩
    apply Subtype.ext
    funext i
    change moduleOverFrameCoefficient M (U i) (e i) (U i) le_rfl
      (M.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op s) = t.val i
    rw [hs i]
    exact LinearEquiv.apply_symm_apply _ _

noncomputable def moduleFramesSGASectionEquiv (hU : ⨆ i, U i = ⊤) :
    Γ(M, ⊤) ≃ (moduleFramesSGALineBundle M U e hU).sections 1 :=
  Equiv.ofBijective _ (moduleFramesSGASection_bijective M U e hU)

end MixedFujita
