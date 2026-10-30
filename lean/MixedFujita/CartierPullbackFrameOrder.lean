/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierRepresentationFrameUnits
public import MixedFujita.ProperCurveOrderBounds

/-!
Evaluate actual pulled Cartier local frames on the actual pulled global
section. A chosen actual target Cartier representation gives the same
intrinsic vanishing order, with the transition unit proved rather than
supplied. This order is independent of the source equation/open choices.
On an actual proper smooth curve a nonzero actual global pullback has the
proved degree bound in this frame. The remaining source-side bridge is to
identify this germ with the source intrinsic coefficient sent through the
actual stalk map; arbitrary-dimensional Bertini/intersection bounds are
not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} [IsIntegral X]

noncomputable def cartierPullbackFrameCoefficientGerm (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) : Y.presheaf.stalk y :=
  moduleOverFrameGlobalCoefficientGerm ((Scheme.Modules.pullback φ).obj D.sheaf) (φ ⁻¹ᵁ U)
    (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D φ U f hf)) y hy
      (modulePullbackGlobalSections φ D.sheaf s)

noncomputable def cartierPullbackFrameOrder (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) : ℕ∞ :=
  localAdicOrder (Y.presheaf.stalk y) (cartierPullbackFrameCoefficientGerm D φ U f hf y hy s)

variable [IsIntegral Y]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

theorem cartierPullbackFrameOrder_eq_target_order (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤))
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf) :
    cartierPullbackFrameOrder D φ U f hf y hy s =
      cartierSectionVanishingOrder E y (cartierPullbackGlobalSectionViaIso D φ E a s) := by
  exact (cartierRepresentationFrameOrder_eq _ E a (φ ⁻¹ᵁ U)
    (moduleRestrictFrameOverIso _ _ (cartierPullbackLocalFrameIso D φ U f hf)) y hy
      (modulePullbackGlobalSections φ D.sheaf s)).symm

theorem cartierPullbackFrameOrder_independent (D : CartierDivisor X) (φ : Y ⟶ X)
    (U V : X.Opens) [Nonempty U] [Nonempty V] (f g : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (hg : rationalUnitClass X V (Additive.ofMul g) = D |_ V)
    (y : Y) (hyU : φ y ∈ U) (hyV : φ y ∈ V) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackFrameOrder D φ U f hf y hyU s =
      cartierPullbackFrameOrder D φ V g hg y hyV s := by
  obtain ⟨E, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  rw [cartierPullbackFrameOrder_eq_target_order D φ U f hf y hyU s E a,
    cartierPullbackFrameOrder_eq_target_order D φ V g hg y hyV s E a]

theorem cartierPullbackFrameOrder_lt_top_iff (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) [IsNoetherianRing (Y.presheaf.stalk y)] (hy : φ y ∈ U) (s : Γ(D.sheaf, ⊤)) :
    cartierPullbackFrameOrder D φ U f hf y hy s < ⊤ ↔
      modulePullbackGlobalSections φ D.sheaf s ≠ 0 := by
  obtain ⟨E, ⟨a⟩⟩ := cartierPullbackLineBundle_exists_cartierDivisor D φ
  rw [cartierPullbackFrameOrder_eq_target_order D φ U f hf y hy s E a,
    cartierSectionVanishingOrder_lt_top_iff,
    cartierPullbackGlobalSectionViaIso_ne_zero_iff]

variable {K : Type u} [Field K] [Y.Over (Spec (CommRingCat.of K))]
  [IsProper (Y ↘ Spec (CommRingCat.of K))] [Smooth (Y ↘ Spec (CommRingCat.of K))]

theorem properSmoothCurve_actual_pullbackFrameOrder_le_degree
    (hY : topologicalKrullDim Y = 1) (D : CartierDivisor X) (φ : Y ⟶ X)
    (U : X.Opens) [Nonempty U] (f : X.functionFieldˣ)
    (hf : rationalUnitClass X U (Additive.ofMul f) = D |_ U)
    (y : Y) (hy : φ y ∈ U) (hClosed : IsClosed {y}) (s : Γ(D.sheaf, ⊤))
    (hs : modulePullbackGlobalSections φ D.sheaf s ≠ 0)
    (E : CartierDivisor Y) (a : (Scheme.Modules.pullback φ).obj D.sheaf ≅ E.sheaf) :
    cartierPullbackFrameOrder D φ U f hf y hy s ≤ (properCurveCartierDegree (K := K) hY E).toNat := by
  rw [cartierPullbackFrameOrder_eq_target_order D φ U f hf y hy s E a]
  exact properSmoothCurve_closedPoint_vanishingOrder_le_degree (K := K) hY E y hClosed _
    ((cartierPullbackGlobalSectionViaIso_ne_zero_iff D φ E a s).mpr hs)

end MixedFujita
