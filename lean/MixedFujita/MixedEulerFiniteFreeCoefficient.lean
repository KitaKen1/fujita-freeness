/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentMixedEulerDifference
public import MixedFujita.ProjectiveCoherentSectionSurjections
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct

/-! 実混合Euler差分の係数同型・有限自由層の階数倍公式。 See reports/check-225-generic-rank-positive-quotient.json for the verified scope. Integral-unit nonnegativity and a positive actual quotient remain geometric inputs; full mixed ample positivity is unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Isomorphic coefficient modules give identical actual mixed Euler
differences. This is an actual tensor/module comparison, not a rank axiom. -/
theorem cartierPulledModuleMixedEulerDifference_coefficient_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] (p : Y ⟶ X)
    (D : List (CartierDivisor X)) (E : CartierDivisor X)
    {M N : Y.Modules} (a : M ≅ N) :
    cartierPulledModuleMixedEulerDifference K p M D E =
      cartierPulledModuleMixedEulerDifference K p N D E := by
  have heq : (fun F : CartierDivisor X => Scheme.Modules.eulerChar
      (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj M)) =
      fun F : CartierDivisor X => Scheme.Modules.eulerChar
        (Y ↘ Spec (CommRingCat.of K)) ((cartierPullbackTwistFunctor F p).obj N) := by
    funext F
    exact moduleEulerChar_congr K (tensorIso (Iso.refl _) a)
  unfold cartierPulledModuleMixedEulerDifference
  rw [heq]


/-- The finite free module splits off one actual unit summand. -/
noncomputable def unitBiproductSuccIso (Y : Scheme.{u}) (k : ℕ) :
    CohomologyAux.unitBiproduct Y (k + 1) ≅
      CohomologyAux.unitModule Y ⊞ CohomologyAux.unitBiproduct Y k :=
  biproduct.whiskerEquiv (f := fun _ : Fin (k + 1) => CohomologyAux.unitModule Y)
    (g := fun _ : Option (Fin k) => CohomologyAux.unitModule Y)
    (finSuccEquiv k) (fun _ => Iso.refl _) ≪≫
      TauCeti.biproductOptionIso (fun _ : Option (Fin k) => CohomologyAux.unitModule Y)


/-- Split exactness gives additivity of actual mixed Euler differences
on a binary coherent biproduct, with all cohomology finiteness internal. -/
theorem proper_cartierPulledModuleMixedEulerDifference_biprod
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (M N : Y.Modules) [M.IsCoherent] [N.IsCoherent] [(M ⊞ N).IsCoherent] :
    cartierPulledModuleMixedEulerDifference K p (M ⊞ N) D E =
      cartierPulledModuleMixedEulerDifference K p M D E +
        cartierPulledModuleMixedEulerDifference K p N D E := by
  let S : ShortComplex Y.Modules := ShortComplex.mk
    (biprod.inl : M ⟶ M ⊞ N) (biprod.snd : M ⊞ N ⟶ N) (by simp)
  have hS : S.ShortExact :=
    { exact := (ShortComplex.Splitting.ofHasBinaryBiproduct M N).exact
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; infer_instance }
  exact cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S) hS


/-- Every actual finite free coefficient contributes exactly its number of
unit summands to every mixed Euler difference, including rank zero. -/
theorem proper_cartierPulledModuleMixedEulerDifference_unitBiproduct
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X) (k : ℕ) :
    cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitBiproduct Y k) D E =
      (k : ℤ) * cartierPulledModuleMixedEulerDifference K p (CohomologyAux.unitModule Y) D E := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    apply cartierPulledModuleMixedEulerDifference_zero_sections
    intro V s
    have hid : 𝟙 (CohomologyAux.unitBiproduct Y 0) = 0 := by
      apply biproduct.hom_ext
      intro j
      exact j.elim0
    have h := congrArg (fun f : CohomologyAux.unitBiproduct Y 0 ⟶ _ => f.app V s) hid
    exact h
  | succ k ih =>
    let : (CohomologyAux.unitBiproduct Y (k + 1)).IsCoherent := unitBiproduct_isCoherent Y (k + 1)
    let : (CohomologyAux.unitBiproduct Y k).IsCoherent := unitBiproduct_isCoherent Y k
    let : (CohomologyAux.unitBiproduct Y (k + 1)).IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
    let : (CohomologyAux.unitModule Y).IsCoherent := invertible_module_isCoherent (CohomologyAux.unitModule Y)
    let : (CohomologyAux.unitModule Y ⊞ CohomologyAux.unitBiproduct Y k).IsCoherent :=
      ⟨Scheme.Modules.isQuasicoherent_of_iso (unitBiproductSuccIso Y k),
        Scheme.Modules.isFiniteType_of_iso (unitBiproductSuccIso Y k)⟩
    rw [cartierPulledModuleMixedEulerDifference_coefficient_iso K p D E (unitBiproductSuccIso Y k),
      proper_cartierPulledModuleMixedEulerDifference_biprod, ih]
    push_cast
    ring

end MixedFujita
