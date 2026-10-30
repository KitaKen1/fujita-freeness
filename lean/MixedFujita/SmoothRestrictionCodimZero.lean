/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothDomainLocalization
public import MixedFujita.EtaleChartDimension

/-!
The restriction theorem in codimension zero (step 9).

A smooth K-domain of relative dimension N has Krull dimension N (`ringKrullDim_eq_of_smooth`, an
étale chart of its spectrum). A surjection of domains of the same finite Krull dimension is
injective (`injective_of_surjective_of_ringKrullDim_eq`): a nonzero element of the kernel is a
non-zero-divisor, so the quotient by it, which still surjects onto the target, has smaller
dimension. Hence in `SmoothRestrictionStatement` the codimension-zero case holds outright
(`smoothRestriction_codim_zero`): the surjection is an isomorphism, and badness transfers along
the isomorphism of spectra (check-317), the base of the induction on the codimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

universe u

section Dimension

/-- A surjection from a domain onto a nontrivial ring of the same finite Krull dimension is
injective. -/
theorem injective_of_surjective_of_ringKrullDim_eq {A A' : Type*} [CommRing A] [IsDomain A]
    [CommRing A'] [Nontrivial A'] (π : A →+* A') (hπ : Function.Surjective π) {N : ℕ}
    (hA : ringKrullDim A = N) (hA' : ringKrullDim A' = N) : Function.Injective π := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hx0
  have hnzd : x ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_ne_zero hx0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have hlift : ∀ a ∈ Ideal.span {x}, π a = 0 := by
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hx, mul_zero]
  have h2 : ringKrullDim A' ≤ ringKrullDim (A ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.lift (Ideal.span {x}) π hlift)
      (Ideal.Quotient.lift_surjective_of_surjective _ hlift hπ)
  rw [hA'] at h2
  rw [hA] at h1
  have h3 : ((N : ℕ∞) : WithBot ℕ∞) + 1 ≤ (N : ℕ∞) := (add_le_add_left h2 1).trans h1
  have h4 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ((N : ℕ) : WithBot ℕ∞) := by exact_mod_cast h3
  have h5 : N + 1 ≤ N := by exact_mod_cast h4
  omega

variable {K : Type u} [Field K]

attribute [local instance] specAlgebraOver

/-- A smooth K-domain of relative dimension N has Krull dimension N. -/
theorem ringKrullDim_eq_of_smooth {A : Type u} [CommRing A] [IsDomain A] [Algebra K A] {N : ℕ}
    [SmoothOfRelativeDimension N (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))] :
    ringKrullDim A = N := by
  have : Smooth (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth N _
  obtain ⟨c⟩ : Nonempty (EtaleChart K (Spec (CommRingCat.of A)) N) := by
    obtain ⟨c, -⟩ := Opens.mem_iSup.mp
      ((etaleCharts_cover (K := K) (X := Spec (CommRingCat.of A)) (n := N)).symm ▸
        Opens.mem_top (Classical.choice inferInstance : Spec (CommRingCat.of A)))
    exact ⟨c⟩
  have h := etaleChart_topologicalKrullDim c
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact h

end Dimension

section CodimZero

variable {K : Type u} [Field K]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra
  specAlgebraOver

/-- The restriction theorem in codimension zero holds: a surjection of smooth K-domains of the
same relative dimension is an isomorphism, and badness transfers along it. -/
theorem smoothRestriction_codim_zero {A A' : Type u} [CommRing A] [IsDomain A] [Algebra K A]
    [CommRing A'] [IsDomain A'] [Algebra K A'] {N : ℕ}
    [SmoothOfRelativeDimension (N + 0) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))]
    [SmoothOfRelativeDimension N (Spec (CommRingCat.of A') ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of A)) (N + 0))
    (cZ : EtaleChart K (Spec (CommRingCat.of A')) N) (π : A →ₐ[K] A')
    (hπ : Function.Surjective π) {J : Type} (g : J → A) (M : ℕ) (χ : A' →ₐ[K] K)
    (h : ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of A)).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of A))
        (1 : (Spec (CommRingCat.of A)).functionFieldˣ)))
      (specAlgHomPoint (χ.comp π))
      (fun j => (Spec (CommRingCat.of A)).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g j))) M) :
    ModelThresholdBadAt cZ (1 : (Spec (CommRingCat.of A')).functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cZ + principalCartierDivisor (Spec (CommRingCat.of A'))
        (1 : (Spec (CommRingCat.of A')).functionFieldˣ)))
      (specAlgHomPoint χ)
      (fun j => (Spec (CommRingCat.of A')).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (π (g j)))) M := by
  haveI : SmoothOfRelativeDimension N (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K)) :=
    ‹SmoothOfRelativeDimension (N + 0) (Spec (CommRingCat.of A) ↘ Spec (CommRingCat.of K))›
  -- π is an isomorphism
  have hA : ringKrullDim A = N := ringKrullDim_eq_of_smooth (K := K)
  have hA' : ringKrullDim A' = N := ringKrullDim_eq_of_smooth (K := K)
  have hinj := injective_of_surjective_of_ringKrullDim_eq π.toRingHom hπ hA hA'
  let e : A ≃ₐ[K] A' := AlgEquiv.ofBijective π ⟨hinj, hπ⟩
  let j : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
    Spec.map (RingEquiv.toCommRingCatIso e.toRingEquiv).hom
  have : IsIso j := inferInstance
  have : IsOpenImmersion j := inferInstance
  have : IsDominant j := ⟨j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  have : j.IsOver (Spec (CommRingCat.of K)) := by
    constructor
    change Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      Spec.map (CommRingCat.ofHom (algebraMap K A'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext k
    exact e.commutes k
  have hpt : j (specAlgHomPoint χ) = specAlgHomPoint (χ.comp π) := by
    apply PrimeSpectrum.ext
    ext a
    change π a ∈ RingHom.ker χ.toRingHom ↔ a ∈ RingHom.ker (χ.comp π).toRingHom
    rw [RingHom.mem_ker, RingHom.mem_ker]
    rfl
  haveI : Nonempty (⊤ : (Spec (CommRingCat.of A')).Opens) := ⟨⟨specAlgHomPoint χ, trivial⟩⟩
  have hg : ∀ i, (dominantFunctionFieldMap j).hom ((Spec (CommRingCat.of A)).germToFunctionField ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (g i))) =
      (Spec (CommRingCat.of A')).germToFunctionField ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of A')).inv (π (g i))) := by
    intro i
    rw [← (Spec (CommRingCat.of A)).algebraMap_germ_eq_germToFunctionField
        (show j (specAlgHomPoint χ) ∈ (⊤ : (Spec (CommRingCat.of A)).Opens) from trivial),
      dominantFunctionFieldMap_algebraMap,
      ← (Spec (CommRingCat.of A')).algebraMap_germ_eq_germToFunctionField
        (show specAlgHomPoint χ ∈ (⊤ : (Spec (CommRingCat.of A')).Opens) from trivial)]
    congr 1
    rw [stalkMap_germ_top]
    congr 1
    exact specMap_appTop_ΓSpecIso_inv _ _
  rw [← hpt] at h
  exact (modelThresholdBadAt_openImmersion_iff j cX cZ (specAlgHomPoint χ) _ _ hg M).mpr h

end CodimZero

end MixedFujita
