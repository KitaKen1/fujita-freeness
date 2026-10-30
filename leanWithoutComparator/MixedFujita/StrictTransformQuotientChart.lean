/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCChartTwoMembers

/-!
The actual quotient ring and point of a strict transform chart.

The coordinate of an SNC member generates its prime. Consequently the ring of the strict
transform is the quotient by that coordinate, with no further localization. The kernel over the
base is determined by the image of the generic point. The prime of an intersection point descends
to this quotient and contracts to the original closed point. These statements construct the
geometric part of the strict transform charts; monomial factorizations are a separate step.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

section Coordinates

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  {n r : ℕ}

/-- A coordinate assigned to an SNC member vanishes at every point of that member in the chart. -/
theorem sncChart_coordinate_mem_point_prime (c : EtaleChart K T n) (ξ : Fin r → T)
    (σ : Fin r → Option (Fin n)) (hc : IsSNCChart c ξ σ) (i : Fin r) (a : Fin n)
    (ha : σ i = some a) (t : T) (ht : t ∈ c.U) (hti : t ∈ closure ({ξ i} : Set T)) :
    c.coords (MvPolynomial.X a) ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal := by
  rw [mem_primeIdealOf_iff_mem_zeroLocus c.isAffine t ht]
  have h := hc.2 i
  rw [ha] at h
  have ht' : t ∈ closure ({ξ i} : Set T) ∩ c.U := ⟨hti, ht⟩
  rw [h] at ht'
  exact ht'.1

end Coordinates

section Kernel

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
  {T : Scheme.{u}} [IsIntegral T] [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {N r : ℕ}

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

/-- The equation and kernel of the strict transform quotient come from the image of its generic
point. In particular, the quotient ideal is prime. -/
theorem exists_modelChart_hyperplane_factor_and_kernel
    (ρ : T ⟶ Spec (CommRingCat.of A)) [ρ.IsOver (Spec (CommRingCat.of K))]
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (c : EtaleChart K T (N + 1))
    (ξ : Fin r → T) (σ : Fin r → Option (Fin (N + 1))) (hc : IsSNCChart c ξ σ)
    (i : Fin r) (hi : σ i = some 0) (hξ : ξ i ∈ c.U)
    (himage : (ρ (ξ i)).asIdeal = Ideal.span {φ (MvPolynomial.X 0)}) :
    (Ideal.span {c.coords (MvPolynomial.X 0)}).IsPrime ∧
      ∃ w : Γ(T, c.U),
        modelChartAlgHom (K := K) ρ c.U (φ (MvPolynomial.X 0)) =
          c.coords (MvPolynomial.X 0) * w ∧
        ∀ a : A, Ideal.Quotient.mk (Ideal.span {c.coords (MvPolynomial.X 0)})
          (modelChartAlgHom (K := K) ρ c.U a) = 0 ↔ a ∈ Ideal.span {φ (MvPolynomial.X 0)} := by
  have hmem (a : A) : modelChartAlgHom (K := K) ρ c.U a ∈
      Ideal.span {c.coords (MvPolynomial.X 0)} ↔ a ∈ Ideal.span {φ (MvPolynomial.X 0)} := by
    rw [modelChartAlgHom_apply, appLE_mem_span_coordinate_iff ρ c ξ σ hc i 0 hi hξ, himage]
  have hx := (hmem (φ (MvPolynomial.X 0))).mpr (Ideal.subset_span rfl)
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hx
  exact ⟨span_coordinate_isPrime_of_isSNCChart c ξ σ hc i 0 hi hξ,
    w, hw, fun a => Ideal.Quotient.eq_zero_iff_mem.trans (hmem a)⟩

end Kernel

section Etale

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of K))] {N : ℕ}

attribute [local instance] cartierBaseOpenAlgebra

/-- The remaining coordinates on the actual hyperplane quotient are étale, not merely formally
étale: finite presentation follows from finite type over the field. -/
theorem etaleChart_hyperplaneCoords_etale (c : EtaleChart K T (N + 1)) :
    (hyperplaneCoords c.coords).toRingHom.Etale := by
  have := sectionsBaseOpen_finiteType (K := K) c.isAffine
  have : Algebra.FinitePresentation K
      (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact etale_of_formallyEtale_of_finitePresentation _
    (hyperplaneCoords_formallyEtale c.coords c.formallyEtale)

end Etale

section Point

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
  {T : Scheme.{u}} [T.Over (Spec (CommRingCat.of K))] {N : ℕ}

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

omit [T.Over (Spec (CommRingCat.of K))] in
/-- Properness and the generic-point image put every point of the original hyperplane in the image
of the closure of the strict-transform member. No point of that closure is supplied. -/
theorem hyperplane_point_mem_strictTransform_image
    (ρ : T ⟶ Spec (CommRingCat.of A)) [IsProper ρ]
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A)
    (χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K) (z : T)
    (hz : (ρ z).asIdeal = Ideal.span {φ (MvPolynomial.X 0)}) :
    specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K
      (Ideal.span {φ (MvPolynomial.X 0)}))) ∈ ρ '' closure ({z} : Set T) := by
  let x := specAlgHomPoint (χ.comp (Ideal.Quotient.mkₐ K
    (Ideal.span {φ (MvPolynomial.X 0)})))
  have hle : (ρ z).asIdeal ≤ x.asIdeal := by
    rw [hz]
    intro a ha
    change χ (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hx : x ∈ closure ({ρ z} : Set (Spec (CommRingCat.of A))) :=
    specializes_iff_mem_closure.mp ((PrimeSpectrum.le_iff_specializes _ _).mp hle)
  have hsub : ({ρ z} : Set (Spec (CommRingCat.of A))) ⊆ ρ '' closure ({z} : Set T) :=
    Set.singleton_subset_iff.mpr ⟨z, subset_closure (Set.mem_singleton z), rfl⟩
  exact closure_minimal hsub ((Scheme.Hom.isClosedMap ρ) _ isClosed_closure) hx

/-- The prime of an actual intersection point, in the actual coordinate quotient, lies over the
specified closed point of the original hyperplane. Every remaining coordinate that vanishes at
the intersection point belongs to this prime. -/
theorem exists_modelChart_quotient_point
    (ρ : T ⟶ Spec (CommRingCat.of A)) [ρ.IsOver (Spec (CommRingCat.of K))]
    (φ : MvPolynomial (Fin (N + 1)) K →ₐ[K] A) (c : EtaleChart K T (N + 1))
    (w : Γ(T, c.U))
    (hw : modelChartAlgHom (K := K) ρ c.U (φ (MvPolynomial.X 0)) =
      c.coords (MvPolynomial.X 0) * w)
    (χ : A ⧸ Ideal.span {φ (MvPolynomial.X 0)} →ₐ[K] K)
    (t : T) (ht : t ∈ c.U)
    (hρt : ρ t = specAlgHomPoint
      (χ.comp (Ideal.Quotient.mkₐ K (Ideal.span {φ (MvPolynomial.X 0)}))))
    (hy : c.coords (MvPolynomial.X 0) ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) :
    ∃ P : Ideal (Γ(T, c.U) ⧸ Ideal.span {c.coords (MvPolynomial.X 0)}), P.IsPrime ∧
      P.comap (strictTransformHyperplaneMap φ c.coords (modelChartAlgHom (K := K) ρ c.U) w hw) =
        RingHom.ker χ.toRingHom ∧
      (∀ f : Γ(T, c.U), Ideal.Quotient.mk _ f ∈ P ↔
        f ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal) ∧
      ∀ l : Fin N, hyperplaneCoords c.coords (MvPolynomial.X l) ∈ P ↔
        c.coords (MvPolynomial.X l.succ) ∈ (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal := by
  let I := Ideal.span {c.coords (MvPolynomial.X 0)}
  let Q := (c.isAffine.primeIdealOf ⟨t, ht⟩).asIdeal
  let P := Q.map (Ideal.Quotient.mk I)
  have hle : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by
    rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
    exact hy
  have hP : P.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hle
  have hmem (f : Γ(T, c.U)) : Ideal.Quotient.mk I f ∈ P ↔ f ∈ Q :=
    mem_map_primeIdealOf_quotient_iff c.isAffine t ht _ hy f
  refine ⟨P, hP, ?_, hmem, fun l => ?_⟩
  · ext a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.mem_comap, strictTransformHyperplaneMap_mk, hmem,
      modelChartAlgHom_apply, appLE_mem_primeIdealOf_iff ρ c.isAffine t ht, hρt]
    rfl
  · rw [hyperplaneCoords_X, hmem]

end Point

end MixedFujita
