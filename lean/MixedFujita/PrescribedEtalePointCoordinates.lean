/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AlignedCompletionCoordinates
public import MixedFujita.PointBlowupAdaptedCoordinates
public import Hironaka.Scheme.Smooth.DifferentialBasis
public import Hironaka.Scheme.Smooth.EtaleLocal
public import Hironaka.Scheme.Smooth.EtaleCoordinates
public import Hironaka.Scheme.Smooth.Adapted

/-! Spread prescribed regular parameters to an actual adapted etale
chart without changing their germs. This lets completion coordinates
aligned with supplied leading forms choose the actual blow-up chart,
rather than independently choosing unrelated etale coordinates. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open KaehlerDifferential TensorProduct
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

set_option maxHeartbeats 1000000 in
theorem exists_adaptedPointCoordinates_with_prescribed_parameters
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) (hx : IsClosed ({x} : Set X)) (y : Fin n → X.presheaf.stalk x)
    (hspan : maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range y)) :
    ∃ E : EtaleCoordinatesAdapted f n n (pointClosureIdeal x) x,
      ∀ i, X.presheaf.germ E.U.1 x E.mem (E.v i) = y i := by
  classical
  let _ := f.stalkAlgebra x
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨V, hxV, -, w, hw⟩ := exists_affineOpen_germ_eq ⟨V₀, hV₀⟩ hxV₀ y
  obtain ⟨b, hb⟩ := exists_basis_tensor_kaehlerDifferential_of_span_eq_maximalIdeal f n hx y hspan
  have hb' : ∃ b' : Module.Basis (Fin n) (ResidueField (X.presheaf.stalk x))
      (ResidueField (X.presheaf.stalk x) ⊗[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄K]),
      ∀ i, b' i = 1 ⊗ₜ D K (X.presheaf.stalk x) (X.presheaf.germ V.1 x hxV (w i)) :=
    ⟨b, fun i => by rw [hb i, hw i]⟩
  obtain ⟨U, hxU, hUV, hE⟩ := exists_etale_toAffineSpace_of_basis f n V hxV w hb'
  let w' : Fin n → Γ(X, U.1) := fun i => X.presheaf.map (homOfLE hUV).op (w i)
  have hw' (i : Fin n) : X.presheaf.germ U.1 x hxU (w' i) = y i := by
    dsimp only [w']
    rw [X.presheaf.germ_res_apply, hw i]
  have hZ : (pointClosureIdeal x).stalkIdeal x =
      Ideal.span ((fun i => X.presheaf.germ U.1 x hxU (w' i)) '' {i : Fin n | i.val < n}) := by
    rw [pointClosureIdeal_stalkIdeal_self, hspan]
    congr 1
    simpa only [hw', Fin.is_lt, Set.setOf_true, Set.image_univ]
  obtain ⟨U', hxU', hU'U, hAd⟩ :=
    exists_comap_eq_comap_coordinateSubspace f n n (pointClosureIdeal x) U hxU w' hZ
  have : Etale (toAffineSpace f U.1 w') := hE
  refine ⟨⟨U', hxU', fun i => X.presheaf.map (homOfLE hU'U).op (w' i),
    etale_toAffineSpace_restrict f hU'U w', hAd⟩, ?_⟩
  intro i
  change X.presheaf.germ U'.1 x hxU' (X.presheaf.map (homOfLE hU'U).op (w' i)) = y i
  rw [X.presheaf.germ_res_apply, hw']

variable {K : Type u} [Field K] [PerfectField K] {n : ℕ} {X : Scheme.{u}}
  [X.Over (Spec (.of K))] [SmoothOfRelativeDimension n (X ↘ Spec (.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseLocalScalarTower cartierBaseOpenAlgebra

/-- The same prescribed etale chart and the aligned completion have the
supplied leading forms. The adapted model is constructed with exactly
the chosen parameter germs, not merely an arbitrary parameter system. -/
theorem exists_suppliedCompletion_adapted_point_coordinates
    (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U) (hxc : IsClosed ({x} : Set X))
    (α : X.presheaf.stalk x →ₐ[K] K)
    (e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[K]
      MvPowerSeries (Fin n) K) :
    ∃ (e' : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃ₐ[K]
        MvPowerSeries (Fin n) K) (ψ : MvPolynomial (Fin n) K →ₐ[K] X.presheaf.stalk x)
      (E : EtaleCoordinatesAdapted (X ↘ Spec (.of K)) n n (pointClosureIdeal x) x),
      maximalIdeal (X.presheaf.stalk x) = Ideal.span (Set.range fun i => ψ (MvPolynomial.X i)) ∧
      (∀ i, X.presheaf.germ E.U.1 x E.mem (E.v i) = ψ (MvPolynomial.X i)) ∧
      (∀ i, stalkTaylorExpansion x e' (ψ (MvPolynomial.X i)) = MvPowerSeries.X i) ∧
      ∀ (r : X.presheaf.stalk x) (m : ℕ), (m : ℕ∞) ≤ localAdicOrder (X.presheaf.stalk x) r →
        homogeneousTaylorForm m (stalkTaylorExpansion x e' r) =
          homogeneousTaylorForm m (stalkTaylorExpansion x e r) := by
  let : Smooth (X ↘ Spec (.of K)) := SmoothOfRelativeDimension.smooth n _
  obtain ⟨e', ψ, hmax, hX, hforms⟩ :=
    etaleChart_exists_completionCoordinates_with_supplied_leading_forms c x hx α e
  obtain ⟨E, hE⟩ := exists_adaptedPointCoordinates_with_prescribed_parameters
    (X ↘ Spec (.of K)) n x hxc (fun i => ψ (MvPolynomial.X i)) hmax
  exact ⟨e', ψ, E, hmax, hE, hX, hforms⟩

end MixedFujita
