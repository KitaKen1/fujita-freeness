/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LocalPointBlowupLeadingRestriction
public import Hironaka.Scheme.BlowUp.AffineBlowUp.Universal.Membership

/-!
Transport the local-ring calculation to actual stalks of the scheme blow-up of Spec R.
The chart immersion induces an actual stalk isomorphism. Its inverse, composed with
the chart germ map, carries the strict transform and exceptional restriction to the
blow-up stalk, compatibly with the actual projection's stalk map. Further transport
from the blow-up of Spec O_{X,x} to the blow-up of X is separate.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R]

noncomputable def affineBlowupChartToStalk (I : Ideal R) (a : I)
    (p : Spec (.of (affineBlowUpAlgebra I a))) :
    affineBlowUpAlgebra I a →+* (affineBlowUp I).presheaf.stalk (affineBlowUp.chart I a p) :=
  (asIso ((affineBlowUp.chart I a).stalkMap p)).inv.hom.comp (specGerm p)

theorem affineBlowupChartToStalk_algebraMap (I : Ideal R) (a : I)
    (p : Spec (.of (affineBlowUpAlgebra I a))) (s : R) :
    affineBlowupChartToStalk I a p (algebraMap R _ s) =
      (affineBlowUp.π I).stalkMap (affineBlowUp.chart I a p)
        (specGerm (affineBlowUp.π I (affineBlowUp.chart I a p)) s) := by
  apply (ConcreteCategory.bijective_of_isIso ((affineBlowUp.chart I a).stalkMap p)).1
  let e := asIso ((affineBlowUp.chart I a).stalkMap p)
  change e.hom (e.inv (specGerm p (algebraMap R _ s))) = _
  rw [Iso.inv_hom_id_apply]
  exact (stalkMap_chart_stalkMap_π I a p s).symm

theorem affineBlowupChartToStalk_exceptionalIdeal (I : Ideal R) (a : I)
    (p : Spec (.of (affineBlowUpAlgebra I a))) :
    (affineBlowUp.exceptionalIdeal I).stalkIdeal (affineBlowUp.chart I a p) =
      Ideal.span {affineBlowupChartToStalk I a p (algebraMap R _ a)} := by
  let e := asIso ((affineBlowUp.chart I a).stalkMap p)
  have h : ((affineBlowUp.exceptionalIdeal I).stalkIdeal (affineBlowUp.chart I a p)).map
      e.hom.hom = Ideal.span {specGerm p (algebraMap R _ a)} :=
    stalkIdeal_exceptionalIdeal_chart_map I a p
  have he := congrArg (Ideal.map e.inv.hom) h
  have hid : e.inv.hom.comp e.hom.hom = RingHom.id _ := by
    ext r
    exact Iso.hom_inv_id_apply e r
  change _ = Ideal.span {e.inv.hom (specGerm p (algebraMap R _ a))}
  simpa only [Ideal.map_map, hid, Ideal.map_id, Ideal.map_span, Set.image_singleton] using he

variable {K : Type u} [Field K] [Algebra K R] [IsLocalRing R] {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem localPointBlowup_actual_stalk_exceptional_restriction
    (ψ : MvPolynomial (Fin n) K →ₐ[K] R) (T : R →ₐ[K] MvPowerSeries (Fin n) K)
    (hX : ∀ i, T (ψ (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hord : ∀ r, (T r).order = localAdicOrder R r) (k : Fin n)
    (p : Spec (.of (affineBlowUpAlgebra (IsLocalRing.maximalIdeal R) (ψ (MvPolynomial.X k)))))
    (s : R) (m : ℕ) (hs : (m : ℕ∞) ≤ (T s).order) :
    let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
    let a : IsLocalRing.maximalIdeal R := ⟨ψ (MvPolynomial.X k), hψ k⟩
    let ν := affineBlowupChartToStalk (IsLocalRing.maximalIdeal R) a p
    let τ := ν.comp (localPointBlowupPolynomialMap (IsLocalRing.maximalIdeal R) ψ hψ k)
    ∃ q : (affineBlowUp (IsLocalRing.maximalIdeal R)).presheaf.stalk
        (affineBlowUp.chart (IsLocalRing.maximalIdeal R) a p),
      (affineBlowUp.π (IsLocalRing.maximalIdeal R)).stalkMap
          (affineBlowUp.chart (IsLocalRing.maximalIdeal R) a p)
          (specGerm (affineBlowUp.π (IsLocalRing.maximalIdeal R)
            (affineBlowUp.chart (IsLocalRing.maximalIdeal R) a p)) s) =
        τ (MvPolynomial.X k) ^ m * q ∧
      Ideal.Quotient.mk (Ideal.span {τ (MvPolynomial.X k)}) q =
        pointBlowupExceptionalEvaluation τ k
          (projectiveDehomogenize K k (homogeneousTaylorForm m (T s))) := by
  dsimp only
  let hψ := localTaylorCoordinate_mem_maximalIdeal ψ T hX hord
  let a : IsLocalRing.maximalIdeal R := ⟨ψ (MvPolynomial.X k), hψ k⟩
  obtain ⟨q, hq, hres⟩ := localPointBlowup_germ_exceptional_restriction_afterMap ψ T hX hord k
    (affineBlowupChartToStalk (IsLocalRing.maximalIdeal R) a p) s m hs
  rw [affineBlowupChartToStalk_algebraMap] at hq
  exact ⟨q, hq, hres⟩

end MixedFujita
