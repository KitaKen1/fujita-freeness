/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.StrictTransformQuotientChart

/-!
Assembling the geometric part of a strict transform chart with connectedness as an explicit input.

On a birational SNC model, connectedness of the indicated non-klt components over the closed point
selects a component meeting the strict transform. The chart, its two distinguished coordinates,
the quotient ring, its kernel over the original hyperplane and its point are all constructed here.
Only the connectedness assertion is used to select the intersection; no chart or quotient-point
witness is supplied. The coefficient data and strict-transform member belong to the given model.
The monomial factorizations and their identification with these coefficients remain separate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section ConnectedChart

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {n r : ℕ}

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

/-- Connectedness selects the meeting component and constructs the actual quotient chart over the
closed point. The quotient by the first coordinate is a domain, and the second coordinate vanishes
at the constructed prime. Its contraction, and the kernel on base functions, are exact. -/
theorem exists_connected_strictTransform_quotient_chart
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsDominant ρ] [IsProper ρ]
    [ρ.IsOver (Spec (CommRingCat.of K))]
    (hρ : Function.Bijective (dominantFunctionFieldMap ρ).hom)
    (φ : MvPolynomial (Fin (n + 2)) K →ₐ[K] A)
    (χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K)
    (ξ : Fin r → T) (hsnc : IsSNCFamily K (n + 2) ξ)
    (M : ℤ) (hM : 0 < M) (h k a : Fin r → ℤ)
    (hconn : _root_.IsPreconnected (⋃ s ∈ {s | M ≤ M * (h s - k s) + a s},
      closure ({ξ s} : Set T) ∩ ρ ⁻¹' Set.singleton (specAlgHomPoint
        (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))))))
    (s₀ s₁ : Fin r) (hh₀ : h s₀ = 1) (hk₀ : k s₀ = 0) (ha₀ : a s₀ = 0)
    (hh₁ : 0 ≤ h s₁) (hk₁ : 0 ≤ k s₁) (hbad : M * (1 + k s₁) ≤ a s₁)
    (himage : (ρ (ξ s₀)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)})
    (hx₁ : specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K
      (Ideal.span {φ (MvPolynomial.X 0)}))) ∈ ρ '' closure ({ξ s₁} : Set T)) :
    ∃ (j : Fin r) (t : T) (c : EtaleChart K T (n + 2))
      (σ : Fin r → Option (Fin (n + 2))),
      j ≠ s₀ ∧ M * (1 + k j - h j) ≤ a j ∧
      t ∈ closure ({ξ s₀} : Set T) ∧ t ∈ closure ({ξ j} : Set T) ∧
      ρ t = specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K
        (Ideal.span {φ (MvPolynomial.X 0)}))) ∧
      t ∈ c.U ∧ IsSNCChart c ξ σ ∧ σ s₀ = some 0 ∧ σ j = some 1 ∧
      Function.Injective (modelChartAlgHom (K := K) ρ c.U) ∧
      (∀ f : Γ(T, c.U), ∃ b d : A, d ≠ 0 ∧
        modelChartAlgHom (K := K) ρ c.U d * f = modelChartAlgHom (K := K) ρ c.U b) ∧
      (hyperplaneCoords c.coords).toRingHom.Etale ∧
      (hyperplaneCoords c.coords).toRingHom.FormallyEtale ∧
      (Ideal.span {c.coords (MvPolynomial.X 0)}).IsPrime ∧
      ∃ (w : Γ(T, c.U))
        (hw : modelChartAlgHom (K := K) ρ c.U (φ (MvPolynomial.X 0)) =
          c.coords (MvPolynomial.X 0) * w),
        (∀ b : A, Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)})
          (modelChartAlgHom (K := K) ρ c.U b) = 0 ↔ b ∈ Ideal.span {φ (MvPolynomial.X 0)}) ∧
        ∃ P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}), P.IsPrime ∧
          P.comap (strictTransformHyperplaneMap φ c.coords
            (modelChartAlgHom (K := K) ρ c.U) w hw) = RingHom.ker χ.toRingHom ∧
          hyperplaneCoords c.coords (MvPolynomial.X (0 : Fin (n + 1))) ∈ P ∧
          ∀ (ht : t ∈ c.U) (f : Γ(T, c.U)), Ideal.Quotient.mk _ f ∈ P ↔
            f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal := by
  classical
  let x := specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K
    (Ideal.span {φ (MvPolynomial.X 0)})))
  have hx₀ := hyperplane_point_mem_strictTransform_image ρ φ χ (ξ s₀) himage
  obtain ⟨j, hj, hineq, t, htj, ht₀, htx⟩ := exists_adjacent_nonklt_member ρ ρ.continuous ξ x
    (specAlgHomPoint_isClosed _) M hM h k a hconn s₀ s₁ hh₀ hk₀ ha₀ hh₁ hk₁ hbad hx₀ hx₁
  obtain ⟨c, σ, ht, hc, hσ₀, hσj⟩ :=
    exists_snc_chart_two_members_at ξ hsnc t s₀ j hj.symm ht₀ htj
  have hξ₀ : ξ s₀ ∈ c.U := (specializes_iff_mem_closure.mpr ht₀).mem_open c.U.isOpen ht
  obtain ⟨hprime, w, hw, hker⟩ :=
    exists_modelChart_hyperplane_factor_and_kernel ρ φ c ξ σ hc s₀ hσ₀ hξ₀ himage
  have hy₀ := sncChart_coordinate_mem_point_prime c ξ σ hc s₀ 0 hσ₀ t ht ht₀
  have hy₁ := sncChart_coordinate_mem_point_prime c ξ σ hc j 1 hσj t ht htj
  obtain ⟨P, hP, hPx, hmem, hcoords⟩ :=
    exists_modelChart_quotient_point ρ φ c w hw χ t ht htx hy₀
  have : Nonempty c.U := c.nonempty
  obtain ⟨hinj, hbir⟩ := appLE_top_injective_birational ρ hρ c.U
  refine ⟨j, t, c, σ, hj, hineq, ht₀, htj, htx, ht, hc, hσ₀, hσj, hinj, hbir,
    etaleChart_hyperplaneCoords_etale c, hyperplaneCoords_formallyEtale c.coords c.formallyEtale,
    hprime, w, hw, hker, P, hP, hPx, ?_, fun _ => hmem⟩
  exact (hcoords 0).mpr hy₁

end ConnectedChart

end MixedFujita
