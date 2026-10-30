/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.AmpleModelOrderBound
public import MixedFujita.EtaleChartDimension

/-!
Uniform order bounds on the simple normal crossing model, with no ample divisor assumed on it
(step 5). Let X be an integral scheme of finite type and separated over an algebraically closed
field of characteristic zero, with an ample Cartier divisor, and consider the simple normal
crossing model T of a log pair on X constructed by resolution. The model is a closed subscheme
of a projective space over the field, so it carries a very ample Cartier divisor. Hence for
every Cartier divisor L on X one constant bounds the vanishing orders of the pullbacks to T of
all nonzero sections of all positive multiples jL, at all closed points of T, by a linear
function of j. The ample divisor on the model, the comparison section and the comparison integer
are all constructed, not assumed.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K] {n : ℕ} {X : Scheme.{u}}
  [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of K))] [IsSeparated (X ↘ Spec (CommRingCat.of K))]

/-- The simple normal crossing model of a log pair on a scheme with an ample divisor has a
uniform linear bound for the vanishing orders of all pulled back sections of the multiples of any
Cartier divisor of the source. No ample divisor on the model is assumed. -/
theorem exists_projective_snc_model_with_order_bound {ι : Type*} [Finite ι] (hn : 1 ≤ n)
    (c : EtaleChart K X n) (f : X.functionFieldˣ) (d : ℕ) (D : CartierDivisor X)
    (G : ι → CartierDivisor X) {H : CartierDivisor X} (hH : CartierIsAmpleProj K H) :
    ∃ (T : Scheme.{u}) (_ : IsIntegral T) (_ : T.Over (Spec (CommRingCat.of K)))
      (_ : IsNoetherian T)
      (_ : SmoothOfRelativeDimension n (T ↘ Spec (CommRingCat.of K)))
      (ρ : T ⟶ X) (_ : IsDominant ρ) (_ : ρ.IsOver (Spec (CommRingCat.of K))) (_ : IsProper ρ)
      (hρ : Function.Bijective (dominantFunctionFieldAlgHom (K := K) ρ))
      (cT : EtaleChart K T n) (r : ℕ) (ξ : Fin r → T),
      Function.Injective ξ ∧ (∀ i, Order.coheight (ξ i) = 1) ∧ IsSNCFamily K n ξ ∧
      (∀ t : CodimensionOnePoint T, (t : T) ∉ Set.range ξ →
        cartierCoefficient (crepantBoundaryCartier ρ hρ c f d D cT etaleCharts_cover)
          (t : T) = 0) ∧
      (∀ (j : ι) (t : CodimensionOnePoint T), (t : T) ∉ Set.range ξ →
        cartierCoefficient (cartierPullback ρ (G j)) (t : T) = 0) ∧
      (∃ J : CartierDivisor T, CartierIsVeryAmpleProj K J) ∧
      ∀ L : CartierDivisor X, ∃ C : ℕ, ∀ x : T, IsClosed {x} → ∀ j : ℕ, 1 ≤ j →
        ∀ s : Γ((j • L).sheaf, ⊤), s ≠ 0 →
          cartierSectionVanishingOrder (cartierPullback ρ (j • L)) x
            (cartierDominantPullbackSection ρ (j • L) s) ≤ ((C * j : ℕ) : ℕ∞) := by
  obtain ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp,
    hG, J, hJ⟩ := exists_projective_snc_model_with_ample c f d D G hH
  have hsm : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hft : LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K)) := inferInstance
  have hdim : topologicalKrullDim T = n := etaleChart_topologicalKrullDim cT
  exact ⟨T, hTi, hTo, hTN, hTs, ρ, hdom, hover, hprop, hρ, cT, r, ξ, hinj, hcoh, hsnc, hsupp, hG,
    ⟨J, hJ⟩, fun L => pulledSection_vanishingOrder_le_of_ample_model hdim hn
      (cartierIsAmpleProj_of_veryAmple hJ) ρ L⟩

end MixedFujita
