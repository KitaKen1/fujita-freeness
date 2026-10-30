/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.PointBlowupRelativeCanonical
public import MixedFujita.AlignedEtalePointBlowup

/-! The actual composite stalk Jacobian satisfies the point-blow-up
chain rule F = u^(n-1) J. The intermediate polynomial coordinates may
be given directly in the blow-up stalk; no global chart there, global
relative canonical identity or completion naturality is needed. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X Y T : Scheme.{u}}
  [IsIntegral X] [IsIntegral T]
  [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))] [T.Over (Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

theorem actual_stalkMap_comp_at_eq (π : Y ⟶ X) (g : T ⟶ Y) (P : T)
    (β : Y.presheaf.stalk (g P) →ₐ[K] T.presheaf.stalk P)
    (hβ : β.toRingHom = (g.stalkMap P).hom)
    (x : X) (hq : π (g P) = x) (a : X.presheaf.stalk x) :
    β (stalkMapAtEq π (g P) x hq a) = stalkMapAtEq (g ≫ π) P x hq a := by
  subst x
  change β (π.stalkMap (g P) a) = (g ≫ π).stalkMap P a
  have hb : β (π.stalkMap (g P) a) = g.stalkMap P (π.stalkMap (g P) a) :=
    RingHom.congr_fun hβ _
  exact hb.trans ((ConcreteCategory.congr_hom (Scheme.Hom.stalkMap_comp g π P) a).symm)

theorem stalkMapAtEq_chart_coordinate {n : ℕ} (ρ : T ⟶ X) [ρ.IsOver (Spec (.of K))]
    (P : T) (x : X) (hq : ρ P = x) (c : EtaleChart K X n) (hx : x ∈ c.U)
    (a : MvPolynomial (Fin n) K) :
    stalkMapAtEq ρ P x hq (etaleChartStalkCoords c x hx a) =
      schemeStalkMapAlgHom (K := K) ρ P
        (etaleChartStalkCoords c (ρ P) (hq.symm ▸ hx) a) := by
  subst x
  rfl

theorem pointBlowup_actual_composite_stalkJacobian {n : ℕ}
    (π : Y ⟶ X) [π.IsOver (Spec (.of K))]
    (g : T ⟶ Y) [g.IsOver (Spec (.of K))] (P : T)
    (β : Y.presheaf.stalk (g P) →ₐ[K] T.presheaf.stalk P)
    (hβ : β.toRingHom = (g.stalkMap P).hom)
    (x : X) (hq : π (g P) = x) (cX : EtaleChart K X n) (hxcX : x ∈ cX.U)
    (cT : EtaleChart K T n) (hPcT : P ∈ cT.U)
    (k : Fin n) (τ : MvPolynomial (Fin n) K →ₐ[K] Y.presheaf.stalk (g P))
    (hτ : τ.toRingHom.FormallyEtale)
    (hcoord : ∀ a, stalkMapAtEq π (g P) x hq (etaleChartStalkCoords cX x hxcX a) =
      τ (polynomialPointBlowupMap k a)) :
    (etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) (g ≫ π) P)
      (etaleChartStalkCoords cX ((g ≫ π) P) (hq.symm ▸ hxcX))
      (etaleChartStalkCoords cT P hPcT) (etaleChartStalkCoords_formallyEtale cT P hPcT)).det =
        β (τ (MvPolynomial.X k)) ^ (n - 1) *
          (etaleRelativeJacobian β τ (etaleChartStalkCoords cT P hPcT)
            (etaleChartStalkCoords_formallyEtale cT P hPcT)).det := by
  let γ := stalkMapAtEqAlgHom (K := K) π (g P) x hq
  have hγ (a : X.presheaf.stalk x) : γ a = stalkMapAtEq π (g P) x hq a :=
    RingHom.congr_fun (stalkMapAtEqAlgHom_toRingHom (K := K) π (g P) x hq) a
  have hc (i : Fin n) : γ (etaleChartStalkCoords cX x hxcX (MvPolynomial.X i)) =
      if i = k then τ (MvPolynomial.X k) else τ (MvPolynomial.X i) * τ (MvPolynomial.X k) := by
    rw [hγ, hcoord]
    by_cases hi : i = k
    · subst i
      rw [polynomialPointBlowupMap_X_self, ite_eq_left rfl]
    · rw [polynomialPointBlowupMap_X_other k i hi, map_mul, ite_eq_right hi]
  have hcomp : etaleRelativeJacobian (schemeStalkMapAlgHom (K := K) (g ≫ π) P)
      (etaleChartStalkCoords cX ((g ≫ π) P) (hq.symm ▸ hxcX))
      (etaleChartStalkCoords cT P hPcT) (etaleChartStalkCoords_formallyEtale cT P hPcT) =
      etaleRelativeJacobian (β.comp γ) (etaleChartStalkCoords cX x hxcX)
        (etaleChartStalkCoords cT P hPcT) (etaleChartStalkCoords_formallyEtale cT P hPcT) := by
    apply Matrix.ext
    intro i j
    change _ = etaleCoordinateDerivation _ _ j (β (γ _))
    rw [hγ, actual_stalkMap_comp_at_eq π g P β hβ x hq,
      stalkMapAtEq_chart_coordinate (g ≫ π) P x hq cX hxcX]
    rfl
  rw [hcomp, etaleRelativeJacobian_det_comp γ β _ τ hτ,
    pointBlowup_etaleRelativeJacobian_det γ _ τ hτ k hc, map_pow]

end MixedFujita
