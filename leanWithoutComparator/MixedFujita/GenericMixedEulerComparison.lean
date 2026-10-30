/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentGenericComparison
public import MixedFujita.CoherentMixedEulerDevissage

/-! 開集合上で同型な実連接層の混合Euler差の小支持への帰着。 See reports/check-221-general-mixed-euler-nilpotence.json for the verified scope. Ordinary mixed-intersection identification and ample-pullback positivity remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A morphism bijective on a nonempty affine open has a mixed Euler
difference equal to that of two actual coherent modules supported on the
proper closed complement. No kernel, cokernel or Euler relation is supplied. -/
theorem cartierPulledModuleMixedEulerDifference_generic_difference
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q)
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set Y).Nonempty)
    (hφ : Function.Bijective (φ.app U)) :
    ∃ N₁ N₂ : Y.Modules, N₁.IsCoherent ∧ N₂.IsCoherent ∧
      CohomologyAux.VanishesOff N₁ (U : Set Y)ᶜ ∧
      CohomologyAux.VanishesOff N₂ (U : Set Y)ᶜ ∧
      IsClosed (U : Set Y)ᶜ ∧ (U : Set Y)ᶜ ≠ Set.univ ∧
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
    CohomologyAux.vanishesOff_kernel_factorThruImage φ hU hφ.1,
    CohomologyAux.vanishesOff_cokernel φ hU hφ.2,
    U.2.isClosed_compl, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    intro h
    exact (h ▸ Set.mem_univ x : x ∈ (U : Set Y)ᶜ) hx
  · have h₁ := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S₁) hS₁
    have h₂ := cartierPulledModuleMixedEulerDifference_of_shortExact K p D E (S := S₂) hS₂
    change cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p S₁.X₁ D E +
        cartierPulledModuleMixedEulerDifference K p (Abelian.image φ) D E at h₁
    change cartierPulledModuleMixedEulerDifference K p Q D E =
      cartierPulledModuleMixedEulerDifference K p (Abelian.image φ) D E +
        cartierPulledModuleMixedEulerDifference K p S₂.X₃ D E at h₂
    omega


/-- Lower-support vanishing makes actual mixed Euler differences invariant
under a morphism bijective on a nonempty affine open. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_generic_morphism
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → ∀ T : Set Y, IsClosed T → T ≠ Set.univ →
      CohomologyAux.VanishesOff N T → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q)
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set Y).Nonempty)
    (hφ : Function.Bijective (φ.app U)) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  obtain ⟨N₁,N₂,h₁,h₂,hN₁,hN₂,hT,hneT,h⟩ :=
    cartierPulledModuleMixedEulerDifference_generic_difference K p D E G Q φ U hU hne hφ
  have hz₁ := hsmall N₁ h₁ _ hT hneT hN₁
  have hz₂ := hsmall N₂ h₂ _ hT hneT hN₂
  omega


/-- The internally constructed coherent zigzag compares actual mixed Euler
differences of generically equal coherent modules, even when the common
quasi-coherent target is not coherent. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_generic_common_target
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → ∀ T : Set Y, IsClosed T → T ≠ Set.univ →
      CohomologyAux.VanishesOff N T → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q R : Y.Modules) [G.IsCoherent] [Q.IsCoherent] [R.IsQuasicoherent]
    (φ : G ⟶ R) (ψ : Q ⟶ R) (U : Y.Opens) (hU : IsAffineOpen U)
    (hne : (U : Set Y).Nonempty)
    (hφ : Function.Bijective (φ.app U)) (hψ : Function.Bijective (ψ.app U)) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  obtain ⟨P,I,hP,hI,a,b,c,ha,hb,hc⟩ :=
    exists_coherent_generic_comparison_zigzag G Q R φ ψ U hU hφ hψ
  let := hP
  let := hI
  have h₁ := cartierPulledModuleMixedEulerDifference_eq_of_generic_morphism K p D E hsmall
    P G a U hU hne ha
  have h₂ := cartierPulledModuleMixedEulerDifference_eq_of_generic_morphism K p D E hsmall
    P I b U hU hne hb
  have h₃ := cartierPulledModuleMixedEulerDifference_eq_of_generic_morphism K p D E hsmall
    Q I c U hU hne hc
  exact h₁.symm.trans (h₂.trans h₃.symm)


/-- Actual isomorphism after restriction to a nonempty affine open suffices
for mixed Euler comparison modulo lower support. The quasi-coherent common
target and coherent kernel zigzag are constructed internally. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_affine_open_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → ∀ T : Set Y, IsClosed T → T ≠ Set.univ →
      CohomologyAux.VanishesOff N T → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) (hne : (U : Set Y).Nonempty)
    (e : (Scheme.Modules.pullback U.ι).obj Q ≅ (Scheme.Modules.pullback U.ι).obj G) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let R := (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj G)
  let : R.IsQuasicoherent := CohomologyAux.isQuasicoherent_pushforward_ι U _
  let φ := CohomologyAux.unitPushPull U.ι G
  let ψ := CohomologyAux.unitPushPull U.ι Q ≫ (Scheme.Modules.pushforward U.ι).map e.hom
  have hφ : Function.Bijective (φ.app U) :=
    Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion U.ι G U
      (by rw [Scheme.Opens.opensRange_ι])
  have hQ : Function.Bijective ((CohomologyAux.unitPushPull U.ι Q).app U) :=
    Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion U.ι Q U
      (by rw [Scheme.Opens.opensRange_ι])
  have he : Function.Bijective (((Scheme.Modules.pushforward U.ι).map e.hom).app U) :=
    ConcreteCategory.bijective_of_isIso _
  exact cartierPulledModuleMixedEulerDifference_eq_of_generic_common_target K p D E hsmall
    G Q R φ ψ U hU hne hφ (he.comp hQ)


/-- Actual isomorphism after restriction to any nonempty open suffices;
an affine subopen and the actual restricted isomorphism are internal. -/
theorem cartierPulledModuleMixedEulerDifference_eq_of_open_iso
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (p : Y ⟶ X) (D : List (CartierDivisor X)) (E : CartierDivisor X)
    (hsmall : ∀ N : Y.Modules, N.IsCoherent → ∀ T : Set Y, IsClosed T → T ≠ Set.univ →
      CohomologyAux.VanishesOff N T → cartierPulledModuleMixedEulerDifference K p N D E = 0)
    (G Q : Y.Modules) [G.IsCoherent] [Q.IsCoherent]
    (W : Y.Opens) (hne : (W : Set Y).Nonempty)
    (e : (Scheme.Modules.pullback W.ι).obj Q ≅ (Scheme.Modules.pullback W.ι).obj G) :
    cartierPulledModuleMixedEulerDifference K p G D E =
      cartierPulledModuleMixedEulerDifference K p Q D E := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨U, hU, hyU, hUW⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) hy
  let V : Y.Opens := U
  let j := Y.homOfLE (show V ≤ W from hUW)
  let a : (Scheme.Modules.pullback V.ι).obj Q ≅ (Scheme.Modules.pullback V.ι).obj G :=
    Scheme.Modules.pullbackCompIso' j W.ι V.ι (Y.homOfLE_ι hUW) Q ≪≫
      (Scheme.Modules.pullback j).mapIso e ≪≫
        (Scheme.Modules.pullbackCompIso' j W.ι V.ι (Y.homOfLE_ι hUW) G).symm
  exact cartierPulledModuleMixedEulerDifference_eq_of_affine_open_iso K p D E hsmall
    G Q V hU ⟨y, hyU⟩ a

end MixedFujita
