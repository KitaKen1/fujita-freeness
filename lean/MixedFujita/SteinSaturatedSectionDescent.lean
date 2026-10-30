/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SteinRationalCartierDescent
public import MixedFujita.CartierGlobalGenerationOperations

/-!
An actual globally generated Cartier divisor descends along a Stein-type map as soon as its
generating opens are inverse images of target opens. Descend the regular ratios s0/si on these
opens. Their nonzero rational functions are local equations downstairs, and their pulled-back
local equations give D + div(s0). Regular unit transitions are constructed by the preceding
gluing theorem. The final version chooses the generating sections and target cover internally
from ordinary global generation and saturation of the actual section nonvanishing opens.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (g : X ⟶ Y) [IsDominant g]
  (happ : ∀ U : Y.Opens, Function.Bijective (g.app U).hom)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

include happ

/-- Descend a generating system with actual saturated nonvanishing opens. -/
theorem stein_exists_cartier_descent_of_saturated_section_cover
    (D : CartierDivisor X) {ι : Type*} (s : ι → Γ(D.sheaf, ⊤)) (hne : ∀ i, s i ≠ 0)
    (U : ι → Y.Opens) [∀ i, Nonempty (U i)] (hcover : iSup U = ⊤)
    (hsat : ∀ i, cartierSectionNonvanishingOpen D (s i) = g ⁻¹ᵁ U i) (i₀ : ι) :
    ∃ (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      D = cartierPullback g H + principalCartierDivisor X φ := by
  classical
  letI hV : ∀ i : ι, Nonempty (cartierSectionNonvanishingOpen D (s i)) := fun i =>
    (cartierSectionNonvanishingOpen_nonempty_iff D (s i)).mpr (hne i)
  letI hpre : ∀ i : ι, Nonempty (g ⁻¹ᵁ U i) := fun i => dominant_preimage_nonempty g (U i)
  let b (i : ι) : Γ(X, g ⁻¹ᵁ U i) :=
    X.presheaf.map (homOfLE (hsat i).symm.le).op (cartierSectionRatio D (s i) (hne i) (s i₀))
  choose a ha using fun i => (happ (U i)).2 (b i)
  have haFF (i : ι) : (dominantFunctionFieldMap g).hom (Y.germToFunctionField (U i) (a i)) =
      (cartierSectionRational D (s i))⁻¹ * cartierSectionRational D (s i₀) := by
    rw [dominantFunctionFieldMap_germ g (U i) (g ⁻¹ᵁ U i) le_rfl,
      Scheme.Hom.appLE_eq_app, ha]
    change X.germToFunctionField (g ⁻¹ᵁ U i)
      (X.presheaf.map (homOfLE (hsat i).symm.le).op
        (cartierSectionRatio D (s i) (hne i) (s i₀))) = _
    rw [germToFunctionField_restrict X, cartierSectionRatio_germToFunctionField]
  have hτ (i : ι) : cartierSectionRational D (s i) ≠ 0 := fun h =>
    hne i (cartierSectionRational_injective D (h.trans (map_zero _).symm))
  have ha0 (i : ι) : Y.germToFunctionField (U i) (a i) ≠ 0 := by
    intro hz
    have h := haFF i
    rw [hz, map_zero] at h
    exact (mul_ne_zero (inv_ne_zero (hτ i)) (hτ i₀)) h.symm
  let f (i : ι) : Y.functionFieldˣ := Units.mk0 _ (ha0 i)
  let τ₀ := cartierSectionUnit D (s i₀) (hne i₀)
  have hf (i : ι) : Units.map (dominantFunctionFieldMap g).hom.toMonoidHom (f i) =
      (cartierSectionUnit D (s i) (hne i))⁻¹ * τ₀ := by
    apply Units.ext
    change (dominantFunctionFieldMap g).hom (Y.germToFunctionField (U i) (a i)) = _
    rw [haFF, Units.val_mul, Units.val_inv_eq_inv_val, cartierSectionUnit_val]
    rfl
  obtain ⟨H, hH⟩ := stein_exists_cartier_descent_of_rational_local_equations g happ U hcover f
    (D + principalCartierDivisor X τ₀) (fun i x hx => by
      rw [hf]
      have hx' : x ∈ cartierSectionNonvanishingOpen D (s i) := by rwa [hsat]
      exact (isLocalEquationAt_inv_cartierSectionUnit D (s i) (hne i) x hx').mul
        (CartierDivisor.isLocalEquationAt_principalCartierDivisor x τ₀))
  refine ⟨H, τ₀⁻¹, ?_⟩
  rw [← hH, principalCartierDivisor_inv]
  abel

/-- Ordinary global generation and saturation choose the entire descent data internally. -/
theorem stein_exists_cartier_descent_of_saturated_generation
    (hsurj : Function.Surjective g) (D : CartierDivisor X) (hD : CartierIsGloballyGenerated D)
    (hsat : ∀ s : Γ(D.sheaf, ⊤), ∃ U : Y.Opens,
      cartierSectionNonvanishingOpen D s = g ⁻¹ᵁ U) :
    ∃ (H : CartierDivisor Y) (φ : X.functionFieldˣ),
      D = cartierPullback g H + principalCartierDivisor X φ := by
  classical
  choose s hs using hD
  have hx (x : X) : x ∈ cartierSectionNonvanishingOpen D (s x) :=
    (mem_cartierSectionNonvanishingOpen_iff_localCoefficient D (s x) x _ _).mpr (hs x)
  have hne (x : X) : s x ≠ 0 :=
    (cartierSectionNonvanishingOpen_nonempty_iff D (s x)).mp ⟨⟨x, hx x⟩⟩
  choose U hU using fun x => hsat (s x)
  letI hUne : ∀ x : X, Nonempty (U x) := fun x =>
    ⟨⟨g x, by change x ∈ g ⁻¹ᵁ U x; rw [← hU]; exact hx x⟩⟩
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact Opens.mem_iSup.mpr ⟨x, by change x ∈ g ⁻¹ᵁ U x; rw [← hU]; exact hx x⟩
  exact stein_exists_cartier_descent_of_saturated_section_cover g happ D s hne U hcover hU
    (genericPoint X)

end MixedFujita
