/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AlgClosedProductIntegral

/-!
Spectra of sections over affine opens and their products (step 9). For an affine open V of a
scheme Y over K, the isomorphism of V with the spectrum of Γ(V) is an isomorphism over K when
Γ(V) carries the K-algebra structure of the structure presheaf (`isoSpec_inv_comp_over`); so the
spectrum of Γ(V) of a smooth variety is smooth of the same relative dimension
(`smoothOfRelativeDimension_spec_sections`). The spectrum of a tensor product A ⊗ B over K is the
fibre product of the spectra and is smooth of the sum of the relative dimensions
(`smoothOfRelativeDimension_spec_tensorProduct`). A K-algebra map χ : R → K gives a closed point of
Spec R at which a global section vanishes exactly when χ kills it
(`mem_primeIdealOf_specAlgHomPoint_iff`), and Lemma 3 for a fixed family on Spec R takes the form
of an ideal of R whose zero set in the K-points is the bad set (`exists_ideal_badAt_spec`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

section Sections

variable {K : Type u} [Field K] {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of K))]

/-- An affine open is isomorphic over K to the spectrum of its sections. -/
theorem isoSpec_inv_comp_over {V : Y.Opens} (hV : IsAffineOpen V) :
    hV.isoSpec.inv ≫ V.ι ≫ (Y ↘ Spec (CommRingCat.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, V))) := by
  rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι,
    ← IsAffineOpen.SpecMap_appLE_fromSpec (Y ↘ Spec (CommRingCat.of K)) (isAffineOpen_top _) hV
      le_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  change _ = CommRingCat.ofHom ((Y.baseRingToStructurePresheaf K).app (op V)).hom
  rw [CommRingCat.ofHom_hom, Scheme.baseRingToStructurePresheaf_app_eq_appLE]

variable {n : ℕ} [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- The spectrum of the sections over an affine open of a smooth scheme is smooth of the same
relative dimension. -/
theorem smoothOfRelativeDimension_spec_sections {V : Y.Opens} (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, V)))) := by
  rw [← isoSpec_inv_comp_over hV]
  have h : SmoothOfRelativeDimension (0 + (0 + n))
      (hV.isoSpec.inv ≫ V.ι ≫ (Y ↘ Spec (CommRingCat.of K))) := inferInstance
  simpa only [Nat.zero_add] using h

end Sections

section Product

variable {K : Type u} [Field K] (A B : Type u) [CommRing A] [CommRing B] [Algebra K A]
  [Algebra K B]

/-- The spectrum of a tensor product of smooth algebras is smooth of the sum of the relative
dimensions. -/
theorem smoothOfRelativeDimension_spec_tensorProduct {n d : ℕ}
    [SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap K A)))]
    [SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B)))] :
    SmoothOfRelativeDimension (n + d)
      (Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B)))) := by
  have heq : Spec.map (CommRingCat.ofHom (algebraMap K (A ⊗[K] B))) =
      (pullbackSpecIso K A B).inv ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    rw [pullbackSpecIso_inv_snd_assoc, ← Spec.map_comp]
    congr 1
    ext k
    change algebraMap K (A ⊗[K] B) k = (Algebra.TensorProduct.includeRight :
      B →ₐ[K] A ⊗[K] B) (algebraMap K B k)
    rw [AlgHom.commutes]
  rw [heq]
  have h : SmoothOfRelativeDimension (0 + (n + d))
      ((pullbackSpecIso K A B).inv ≫ pullback.snd _ _ ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B))) := inferInstance
  simpa only [Nat.zero_add] using h

end Product

section Points

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R]

/-- The closed point of the spectrum given by a K-algebra map to K. -/
def specAlgHomPoint (χ : R →ₐ[K] K) : Spec (CommRingCat.of R) :=
  ⟨RingHom.ker χ.toRingHom, RingHom.ker_isPrime _⟩

theorem specAlgHomPoint_isClosed (χ : R →ₐ[K] K) :
    IsClosed ({specAlgHomPoint χ} : Set (Spec (CommRingCat.of R))) := by
  have hsurj : Function.Surjective χ := fun k => ⟨algebraMap K R k, χ.commutes k⟩
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
    (RingHom.ker_isMaximal_of_surjective _ hsurj)

/-- A global section vanishes at the closed point of χ exactly when χ kills it. -/
theorem mem_primeIdealOf_specAlgHomPoint_iff (χ : R →ₐ[K] K) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv r ∈
      ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
        ⟨specAlgHomPoint χ, trivial⟩).asIdeal ↔ χ r = 0 := by
  rw [← not_iff_not, ← mem_basicOpen_iff_notMem_primeIdealOf (isAffineOpen_top _) _ trivial,
    basicOpen_eq_of_affine]
  change r ∉ RingHom.ker χ.toRingHom ↔ _
  rw [RingHom.mem_ker]
  rfl

/-- Every closed point of the spectrum of a finitely generated algebra over an algebraically
closed field is the point of a K-algebra map. -/
theorem exists_algHom_of_isClosed [IsAlgClosed K] [Algebra.FiniteType K R]
    (x : Spec (CommRingCat.of R)) (hx : IsClosed ({x} : Set (Spec (CommRingCat.of R)))) :
    ∃ χ : R →ₐ[K] K, specAlgHomPoint χ = x := by
  have hmax : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx
  refine ⟨closedPointEvaluation (K := K) x.asIdeal, PrimeSpectrum.ext ?_⟩
  ext r
  change r ∈ RingHom.ker _ ↔ _
  rw [RingHom.mem_ker]
  exact closedPointEvaluation_eq_zero_iff (K := K) x.asIdeal r

end Points

section FixedFamily

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] (R : Type u) [CommRing R]
  [IsDomain R] [Algebra K R] {m : ℕ}
  [SmoothOfRelativeDimension m (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of K))]

/-- Lemma 3 for a fixed family on the spectrum of a smooth domain: the K-points at which the
threshold of finitely many elements of R is at most 1/M are the zero set of an ideal of R. -/
theorem exists_ideal_badAt_spec (cX : EtaleChart K (Spec (CommRingCat.of R)) m) {J : Type}
    [Finite J] (g : J → R) (M : ℕ) (hM : 1 ≤ M) :
    ∃ I : Ideal R, ∀ χ : R →ₐ[K] K,
      (ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of R)).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor (Spec (CommRingCat.of R))
          (1 : (Spec (CommRingCat.of R)).functionFieldˣ)))
        (specAlgHomPoint χ)
        (fun j => (Spec (CommRingCat.of R)).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv (g j))) M ↔
        ∀ r ∈ I, χ r = 0) := by
  have : Smooth (Spec (CommRingCat.of R) ↘ Spec (CommRingCat.of K)) :=
    SmoothOfRelativeDimension.smooth m _
  obtain ⟨I', hI'⟩ := exists_ideal_modelThresholdBadAt_of_affine cX ⊤ (isAffineOpen_top _)
    (fun j => (Scheme.ΓSpecIso (CommRingCat.of R)).inv (g j)) M hM
  refine ⟨I'.comap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom, fun χ => ?_⟩
  rw [hI' (specAlgHomPoint χ) trivial (specAlgHomPoint_isClosed χ)]
  constructor
  · intro h r hr
    exact (mem_primeIdealOf_specAlgHomPoint_iff χ r).mp (h _ hr)
  · intro h a ha
    have ha' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv
        ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) = a :=
      Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a
    rw [← ha']
    refine (mem_primeIdealOf_specAlgHomPoint_iff χ _).mpr (h _ ?_)
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) ∈ I'
    rw [ha']
    exact ha

end FixedFamily

end MixedFujita
