/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentGenericComparison

/-! 開集合全体での実連接核・像の一様比較と正確な閉支持。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Vanishing on the affine basis of a WHOLE prescribed open gives exact
support in its closed complement. No smaller source open is substituted. -/
theorem moduleVanishesOff_open_complement_of_affine_sections_zero
    {Y : Scheme.{u}} (N : Y.Modules) (W : Y.Opens)
    (hN : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → ∀ s : Γ(N, U), s = 0) :
    CohomologyAux.VanishesOff N (W : Set Y)ᶜ := by
  intro V hV s
  have hVW : V ≤ W := fun x hx => not_not.mp fun hn => Set.disjoint_left.mp hV hx hn
  have hx : ∀ x : V, ∃ (U : Y.Opens), IsAffineOpen U ∧ x.1 ∈ U ∧ U ≤ V := by
    intro x
    exact (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) x.2
  choose U hU hxU hUV using hx
  refine TopCat.Sheaf.eq_of_locally_eq' N.toAbSheaf U V (fun x => homOfLE (hUV x))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩) s 0 ?_
  intro x
  rw [map_zero]
  exact hN (U x) (hU x) ((hUV x).trans hVW) _


/-- Kernel errors of a morphism injective on every affine inside W have
support in the EXACT complement of W. -/
theorem moduleKernelFactor_vanishesOff_open_complement
    {Y : Scheme.{u}} {G Q : Y.Modules} [G.IsQuasicoherent] [Q.IsQuasicoherent]
    (φ : G ⟶ Q) (W : Y.Opens)
    (hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Injective (φ.app U)) :
    CohomologyAux.VanishesOff (kernel (Abelian.factorThruImage φ)) (W : Set Y)ᶜ := by
  apply moduleVanishesOff_open_complement_of_affine_sections_zero
  intro U hU hUW s
  exact (CohomologyAux.vanishesOff_kernel_factorThruImage φ hU (hφ U hU hUW)) U
    (Set.disjoint_left.mpr fun _ hx hnx => hnx hx) s


/-- Cokernel errors have the same exact support control on a whole open. -/
theorem moduleCokernel_vanishesOff_open_complement
    {Y : Scheme.{u}} {G Q : Y.Modules} [G.IsQuasicoherent] [Q.IsQuasicoherent]
    (φ : G ⟶ Q) (W : Y.Opens)
    (hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Surjective (φ.app U)) :
    CohomologyAux.VanishesOff (cokernel φ) (W : Set Y)ᶜ := by
  apply moduleVanishesOff_open_complement_of_affine_sections_zero
  intro U hU hUW s
  exact (CohomologyAux.vanishesOff_cokernel φ hU (hφ U hU hUW)) U
    (Set.disjoint_left.mpr fun _ hx hnx => hnx hx) s


/-- The SAME actual coherent kernel/image zigzag is bijective on EVERY
affine inside the given open, with its common quasi-coherent target allowed
to be noncoherent. This preserves supports pulled back from the base. -/
theorem exists_coherent_whole_open_comparison_zigzag
    {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (G Q R : Y.Modules) [G.IsCoherent] [Q.IsCoherent] [R.IsQuasicoherent]
    (φ : G ⟶ R) (ψ : Q ⟶ R) (W : Y.Opens)
    (hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (φ.app U))
    (hψ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (ψ.app U)) :
    ∃ P I : Y.Modules, P.IsCoherent ∧ I.IsCoherent ∧
      ∃ (a : P ⟶ G) (b : P ⟶ I) (c : Q ⟶ I),
        ∀ U : Y.Opens, IsAffineOpen U → U ≤ W →
          Function.Bijective (a.app U) ∧ Function.Bijective (b.app U) ∧ Function.Bijective (c.app U) := by
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (cokernel ψ).IsQuasicoherent := CohomologyAux.isQuasicoherent_cokernel ψ
  let θ := φ ≫ cokernel.π ψ
  let P := kernel θ
  let I := Abelian.image ψ
  let : P.IsCoherent := moduleKernel_isCoherent_of_source_isCoherent θ
  let : I.IsCoherent := moduleImage_isCoherent_of_source_isCoherent ψ
  let a : P ⟶ G := kernel.ι θ
  let c : Q ⟶ I := Abelian.factorThruImage ψ
  let d : I ⟶ R := Abelian.image.ι ψ
  let b : P ⟶ I := kernel.lift (cokernel.π ψ) (a ≫ φ) (by
    simpa only [Category.assoc] using kernel.condition θ)
  have hbd : b ≫ d = a ≫ φ := kernel.lift_ι _ _ _
  have hcd : c ≫ d = ψ := Abelian.image.fac ψ
  refine ⟨P, I, inferInstance, inferInstance, a, b, c, ?_⟩
  intro U hU hUW
  have hd : Function.Bijective (d.app U) := by
    refine ⟨CohomologyAux.app_injective_of_mono d U, ?_⟩
    intro r
    obtain ⟨q, hq⟩ := (hψ U hU hUW).2 r
    exact ⟨c.app U q, (congrArg (fun f : Q ⟶ R => f.app U q) hcd).trans hq⟩
  have hzero : ∀ s : Γ(cokernel ψ, U), s = 0 :=
    (CohomologyAux.vanishesOff_cokernel ψ hU (hψ U hU hUW).2) U
      (Set.disjoint_left.mpr fun _ hx hnx => hnx hx)
  have ha : Function.Bijective (a.app U) :=
    moduleKernel_ι_app_bijective_of_target_sections_zero θ U hzero
  have hbcomp : Function.Bijective (d.app U ∘ b.app U) := by
    change Function.Bijective ((b ≫ d).app U)
    rw [hbd]
    exact (hφ U hU hUW).comp ha
  have hccomp : Function.Bijective (d.app U ∘ c.app U) := by
    change Function.Bijective ((c ≫ d).app U)
    rw [hcd]
    exact hψ U hU hUW
  exact ⟨ha, (Function.Bijective.of_comp_iff' hd _).mp hbcomp,
    (Function.Bijective.of_comp_iff' hd _).mp hccomp⟩

end MixedFujita
