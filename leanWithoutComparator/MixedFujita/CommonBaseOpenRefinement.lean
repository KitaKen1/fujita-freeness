/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DominantOpenBaseRestriction
public import MixedFujita.NormalBasePrimeUniformizer

/-!
Actual open inclusions provide common-refinement diagrams. Their inverse-image
ranges cover the corresponding source opens. At a normal base prime, the actual
stalk isomorphisms preserve DVRs and Cartier coefficients on every smaller open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

/-- A nonempty actual open inclusion in an integral scheme is dominant. -/
theorem isDominant_homOfLE_integral {X : Scheme.{u}} [IsIntegral X]
    {V U : X.Opens} [Nonempty V] [Nonempty U] (h : V ≤ U) :
    IsDominant (X.homOfLE h) :=
  ⟨(X.homOfLE h).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩

/-- The actual open square covers the inverse image of the smaller base open. -/
theorem morphismRestrict_homOfLE_range_cover {X Y : Scheme.{u}} (g : X ⟶ Y)
    {V U : Y.Opens} (h : V ≤ U) :
    (g ∣_ U) ⁻¹ᵁ (Y.homOfLE h).opensRange ≤
      (X.homOfLE (g.preimage_mono h)).opensRange := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  have heq := congrArg (fun z : U.toScheme => z.1) hy
  simp only [Scheme.homOfLE_apply, morphismRestrict_base_coe] at heq
  have hmem : g x.1 ∈ V := heq ▸ y.property
  refine ⟨⟨x.1, hmem⟩, ?_⟩
  apply Subtype.ext
  simp only [Scheme.homOfLE_apply]

variable {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  (η : CodimensionOnePoint Y) [IsIntegrallyClosed (Y.presheaf.stalk (η : Y))]

/-- The original normal prime supplies an actual DVR on each base neighbourhood. -/
theorem normal_base_prime_open_stalk_DVR (U : Y.Opens) (hηU : (η : Y) ∈ U) :
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    IsDiscreteValuationRing (U.toScheme.presheaf.stalk ⟨(η : Y), hηU⟩) := by
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  let θ : U.toScheme := ⟨(η : Y), hηU⟩
  letI : IsDiscreteValuationRing (Y.presheaf.stalk (U.ι θ)) := normal_codimensionOne_stalk_DVR η
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (RingEquiv.ofBijective (U.ι.stalkMap θ).hom
      (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap θ)))

/-- Cartier coefficients at the original prime are preserved on a common smaller open. -/
theorem cartierCoefficient_homOfLE_at_normal_base_prime
    {V U : Y.Opens} (h : V ≤ U) (hηV : (η : Y) ∈ V) (hηU : (η : Y) ∈ U) :
    letI : Nonempty V := ⟨⟨(η : Y), hηV⟩⟩
    letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
    letI : IsDominant (Y.homOfLE h) := isDominant_homOfLE_integral h
    ∀ H : CartierDivisor U.toScheme,
      cartierCoefficient (cartierPullback (Y.homOfLE h) H) (⟨(η : Y), hηV⟩ : V.toScheme) =
        cartierCoefficient H (⟨(η : Y), hηU⟩ : U.toScheme) := by
  letI : Nonempty V := ⟨⟨(η : Y), hηV⟩⟩
  letI : Nonempty U := ⟨⟨(η : Y), hηU⟩⟩
  letI : IsDominant (Y.homOfLE h) := isDominant_homOfLE_integral h
  intro H
  let θ : V.toScheme := ⟨(η : Y), hηV⟩
  have hθ : Order.coheight θ = 1 :=
    (coheight_eq_of_stalkMap_bijective V.ι θ
      (ConcreteCategory.bijective_of_isIso (V.ι.stalkMap θ))).trans η.property
  have heq : Y.homOfLE h θ = (⟨(η : Y), hηU⟩ : U.toScheme) := Subtype.ext (by simp [θ])
  have hξ : Order.coheight (Y.homOfLE h θ) = 1 := by
    rw [heq]
    exact (coheight_eq_of_stalkMap_bijective U.ι _
      (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap _))).trans η.property
  letI : IsDiscreteValuationRing (V.toScheme.presheaf.stalk θ) :=
    normal_base_prime_open_stalk_DVR η V hηV
  letI : IsDiscreteValuationRing (U.toScheme.presheaf.stalk (Y.homOfLE h θ)) := by
    rw [heq]
    exact normal_base_prime_open_stalk_DVR η U hηU
  have he := cartierCoefficient_pullback_of_stalkMap_bijective (Y.homOfLE h) ⟨θ, hθ⟩ hξ
    (ConcreteCategory.bijective_of_isIso ((Y.homOfLE h).stalkMap θ)) H
  simpa [heq, θ] using he

end MixedFujita
