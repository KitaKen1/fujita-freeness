/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.WholeOpenCoherentComparison
public import MixedFujita.CoherentMixedEulerDevissage

/-! 指定した開集合の補集合に支持を保つ実混合Euler比較。 See reports/check-227-base-dimension-pullback-vanishing.json for the verified scope. Positivity through the base dimension and the original numerical-dimension dictionary remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Actual coherent errors of a comparison on a prescribed whole open. -/
theorem cartierPulledModuleMixedEulerDifference_whole_open_difference
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q)
    (W : Y.Opens)
    (hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (φ.app U)) :
    ∃ N₁ N₂ : Y.Modules, N₁.IsCoherent ∧ N₂.IsCoherent ∧
      CohomologyAux.VanishesOff N₁ (W : Set Y)ᶜ ∧
      CohomologyAux.VanishesOff N₂ (W : Set Y)ᶜ ∧
      cartierPulledModuleMixedEulerDifference K p G D E -
          cartierPulledModuleMixedEulerDifference K p Q D E =
        cartierPulledModuleMixedEulerDifference K p N₁ D E -
          cartierPulledModuleMixedEulerDifference K p N₂ D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : (Abelian.image φ).IsCoherent := moduleImage_isCoherent_of_source_isCoherent φ
  let : (Abelian.image φ).IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let S₁ := ShortComplex.kernelSequence (Abelian.factorThruImage φ)
  let S₂ := ShortComplex.kernelSequence (cokernel.π φ)
  have hS₁ := CohomologyAux.shortExact_kernelSequence (Abelian.factorThruImage φ)
  have hS₂ := CohomologyAux.shortExact_kernelSequence (cokernel.π φ)
  let : S₁.X₁.IsQuasicoherent := CohomologyAux.isQuasicoherent_kernel _
  let : S₁.X₂.IsCoherent := inferInstanceAs G.IsCoherent
  let : S₁.X₃.IsCoherent := inferInstanceAs (Abelian.image φ).IsCoherent
  let : S₁.X₁.IsCoherent := CohomologyAux.isCoherent_X₁_of_shortExact hS₁
  let : S₂.X₁.IsQuasicoherent := inferInstanceAs (Abelian.image φ).IsQuasicoherent
  let : S₂.X₁.IsCoherent := inferInstanceAs (Abelian.image φ).IsCoherent
  let : S₂.X₂.IsCoherent := inferInstanceAs Q.IsCoherent
  let : S₂.X₃.IsCoherent := CohomologyAux.isCoherent_X₃_of_shortExact hS₂
  refine ⟨S₁.X₁, S₂.X₃, inferInstance, inferInstance,
    moduleKernelFactor_vanishesOff_open_complement φ W (fun U hU hUW => (hφ U hU hUW).1),
    moduleCokernel_vanishesOff_open_complement φ W (fun U hU hUW => (hφ U hU hUW).2), ?_⟩
  have h₁ := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S₁) hS₁
  have h₂ := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S₂) hS₂
  change cartierPulledModuleMixedEulerDifference K p G D E =
    cartierPulledModuleMixedEulerDifference K p S₁.X₁ D E +
      cartierPulledModuleMixedEulerDifference K p (Abelian.image φ) D E at h₁
  change cartierPulledModuleMixedEulerDifference K p Q D E =
    cartierPulledModuleMixedEulerDifference K p (Abelian.image φ) D E +
      cartierPulledModuleMixedEulerDifference K p S₂.X₃ D E at h₂
  omega


/-- Equality modulo coherent modules supported in the exact open complement. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_whole_open_morphism
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (W : Y.Opens)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → CohomologyAux.VanishesOff N (W : Set Y)ᶜ →
      cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q)
    (hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (φ.app U)) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  obtain ⟨N₁,N₂,h₁,h₂,hN₁,hN₂,h⟩ :=
    cartierPulledModuleMixedEulerDifference_whole_open_difference K p D E G Q φ W hφ
  have hz₁ := hsmall N₁ h₁ hN₁
  have hz₂ := hsmall N₂ h₂ hN₂
  omega


/-- A common target need only be quasi-coherent; the coherent zigzag is internal. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_whole_open_common_target
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (W : Y.Opens)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → CohomologyAux.VanishesOff N (W : Set Y)ᶜ →
      cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q R : Y.Modules) [G.IsCoherent] [Q.IsCoherent] [R.IsQuasicoherent]
    (φ : G ⟶ R) (ψ : Q ⟶ R)
    (hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (φ.app U))
    (hψ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (ψ.app U)) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  obtain ⟨P,I,hP,hI,a,b,c,habc⟩ :=
    exists_coherent_whole_open_comparison_zigzag G Q R φ ψ W hφ hψ
  let := hP
  let := hI
  have h₁ := cartierPulledModuleMixedEulerDifference_eq_of_whole_open_morphism K p D E W hsmall
    P G a (fun U hU hUW => (habc U hU hUW).1)
  have h₂ := cartierPulledModuleMixedEulerDifference_eq_of_whole_open_morphism K p D E W hsmall
    P I b (fun U hU hUW => (habc U hU hUW).2.1)
  have h₃ := cartierPulledModuleMixedEulerDifference_eq_of_whole_open_morphism K p D E W hsmall
    Q I c (fun U hU hUW => (habc U hU hUW).2.2)
  exact h₁.symm.trans (h₂.trans h₃.symm)


/-- Actual isomorphism on a whole open, preserving its exact complement support. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_whole_open_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (W : Y.Opens)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → CohomologyAux.VanishesOff N (W : Set Y)ᶜ →
      cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent]
    (e : (Scheme.Modules.pullback W.ι).obj Q ≅ (Scheme.Modules.pullback W.ι).obj G) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let R := (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.pullback W.ι).obj G)
  let : R.IsQuasicoherent := CohomologyAux.isQuasicoherent_pushforward_ι W _
  let φ := CohomologyAux.unitPushPull W.ι G
  let ψ := CohomologyAux.unitPushPull W.ι Q ≫ (Scheme.Modules.pushforward W.ι).map e.hom
  have hφ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (φ.app U) := by
    intro U _ hUW
    exact Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion W.ι G U
      (by simpa only [Scheme.Opens.opensRange_ι] using hUW)
  have hψ : ∀ U : Y.Opens, IsAffineOpen U → U ≤ W → Function.Bijective (ψ.app U) := by
    intro U _ hUW
    have hQ := Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion W.ι Q U
      (by simpa only [Scheme.Opens.opensRange_ι] using hUW)
    have he : Function.Bijective (((Scheme.Modules.pushforward W.ι).map e.hom).app U) :=
      ConcreteCategory.bijective_of_isIso _
    exact he.comp hQ
  exact cartierPulledModuleMixedEulerDifference_eq_of_whole_open_common_target K p D E W hsmall
    G Q R φ ψ hφ hψ

end MixedFujita
