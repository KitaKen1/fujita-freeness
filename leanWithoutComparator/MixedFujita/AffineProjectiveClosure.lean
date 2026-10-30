/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ProjectiveChartEquiv
public import MixedFujita.ProjectiveIdealSheafGluing
public import MixedFujita.PolynomialProjectiveCharts
public import OAI.AlgebraicGeometry.NumericalDimension.PrimeSpecialization
public import MixedFujita.ProjectiveBaseChange
public import MixedFujita.EtaleChartOpenRestriction
public import MixedFujita.AffineEtaleChartModel
public import MixedFujita.AmpleDivisibleGlobalGeneration
public import MixedFujita.CartierBigDefinition
public import MixedFujita.ProjectivePullbackCartier
public import MixedFujita.TwistedCartierApproximation
public import MixedFujita.EtaleChartDimension

/-!
The projective closure of an affine variety (step 9, compactification for relative vanishing).

Generators `a₁, …, a_r` of a finitely generated `K`-domain `A` give a surjection from the ring of
the chart `X₀ ≠ 0` of `ℙ^r` onto `A` (`X_j/X₀ ↦ a_j`), hence a closed immersion of `Spec A` into
that chart and a morphism `f : Spec A → ℙ^r` (`affineClosureMap`). Its scheme-theoretic image
`X̄₀` (`affineClosure`) is integral (the image of an integral scheme), with the closed immersion
`X̄₀ → ℙ^r`. The factorization `Spec A → X̄₀` is an open immersion onto the part of `X̄₀` over the chart
(`affineClosure_toImage_isOpenImmersion`, `affineClosure_toImage_opensRange`). Over the chart, the
factorization is a closed immersion into an affine scheme whose global sections map is injective
(the image is scheme-theoretically dominated), so it is an isomorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Limits
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false

attribute [local instance] MvPolynomial.gradedAlgebra

section Closure

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The affine coordinates `x_j = X_j / X₀` of the chart `X₀ ≠ 0` sent to `π(x_j)`. -/
noncomputable def affineClosureCoordHom {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    MvPolynomial {j : Fin (r + 1) // j ≠ 0} K →+* A :=
  π.toRingHom.comp (MvPolynomial.rename
    (fun j : {j : Fin (r + 1) // j ≠ 0} => j.1.pred j.2)).toRingHom

theorem affineClosureCoordHom_surjective {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) : Function.Surjective (affineClosureCoordHom π) := by
  have hren : Function.Surjective (MvPolynomial.rename (R := K)
      (fun j : {j : Fin (r + 1) // j ≠ 0} => j.1.pred j.2)) := by
    apply MvPolynomial.rename_surjective
    intro i
    exact ⟨⟨i.succ, Fin.succ_ne_zero i⟩, by simp⟩
  exact hπ.comp hren

theorem affineClosureCoordHom_C {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) (c : K) :
    affineClosureCoordHom π (MvPolynomial.C c) = algebraMap K A c := by
  simp [affineClosureCoordHom]

/-- The chart `X₀ ≠ 0` of `ℙ^r` as an open subset. -/
noncomputable abbrev affineClosureChart (r : ℕ) : (polynomialProjectiveScheme (r + 1) K).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) (MvPolynomial.X 0)

/-- `Spec A` as a closed subscheme of the chart `X₀ ≠ 0`. -/
noncomputable def affineClosureChartMap {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Spec (CommRingCat.of A) ⟶ (affineClosureChart (K := K) r).toScheme :=
  Spec.map (CommRingCat.ofHom (affineClosureCoordHom π)) ≫
    (polynomialProjectiveAffineChartIso K (0 : Fin (r + 1))).inv

theorem affineClosureChartMap_isClosedImmersion {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) : IsClosedImmersion (affineClosureChartMap π) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (affineClosureCoordHom π))) :=
    IsClosedImmersion.spec_of_surjective _ (affineClosureCoordHom_surjective π hπ)
  unfold affineClosureChartMap
  infer_instance

/-- `Spec A` in `ℙ^r` through the chart `X₀ ≠ 0`. -/
noncomputable def affineClosureMap {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Spec (CommRingCat.of A) ⟶ polynomialProjectiveScheme (r + 1) K :=
  affineClosureChartMap π ≫ (affineClosureChart (K := K) r).ι

instance affineClosureMap_quasiCompact [IsNoetherianRing A] {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    QuasiCompact (affineClosureMap π) :=
  quasiCompact_of_noetherianSpace_source _

/-- The projective closure of `Spec A`: the scheme-theoretic image in `ℙ^r`. -/
noncomputable abbrev affineClosure {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) : Scheme.{u} :=
  (affineClosureMap π).image

instance affineClosure_isIntegral [IsDomain A] [IsNoetherianRing A] {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    IsIntegral (affineClosure π) :=
  OAI.NumericalDimensionOne.integral_image _

/-- The closed immersion of the closure into `ℙ^r`. -/
noncomputable abbrev affineClosureι {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    affineClosure π ⟶ polynomialProjectiveScheme (r + 1) K :=
  (affineClosureMap π).imageι

/-- The factorization of `Spec A` through its closure. -/
noncomputable abbrev affineClosureToImage {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Spec (CommRingCat.of A) ⟶ affineClosure π :=
  (affineClosureMap π).toImage

/-- The part of the closure over the chart `X₀ ≠ 0`. -/
noncomputable abbrev affineClosureChartPart {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (affineClosure π).Opens :=
  affineClosureι π ⁻¹ᵁ affineClosureChart r

theorem affineClosure_range_toImage_subset {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Set.range (affineClosureToImage π) ⊆ Set.range (affineClosureChartPart π).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  change affineClosureι π (affineClosureToImage π x) ∈ affineClosureChart (K := K) r
  rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
  change ((affineClosureChart (K := K) r).ι (affineClosureChartMap π x)) ∈ affineClosureChart r
  exact (affineClosureChartMap π x).2

/-- `Spec A` into the part of its closure over the chart. -/
noncomputable def affineClosureChartLift {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Spec (CommRingCat.of A) ⟶ (affineClosureChartPart π).toScheme :=
  IsOpenImmersion.lift (affineClosureChartPart π).ι (affineClosureToImage π)
    (affineClosure_range_toImage_subset π)

@[reassoc (attr := simp)]
theorem affineClosureChartLift_fac {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    affineClosureChartLift π ≫ (affineClosureChartPart π).ι = affineClosureToImage π :=
  IsOpenImmersion.lift_fac _ _ _

theorem affineClosureChartLift_comp_restrict {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    affineClosureChartLift π ≫ (affineClosureι π ∣_ affineClosureChart r) =
      affineClosureChartMap π := by
  rw [← cancel_mono (affineClosureChart (K := K) r).ι, Category.assoc, morphismRestrict_ι,
    affineClosureChartLift_fac_assoc, Scheme.Hom.toImage_imageι]
  rfl

theorem affineClosureChartLift_isClosedImmersion {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) : IsClosedImmersion (affineClosureChartLift π) := by
  have : IsClosedImmersion (affineClosureChartLift π ≫ (affineClosureι π ∣_ affineClosureChart r)) := by
    rw [affineClosureChartLift_comp_restrict]
    exact affineClosureChartMap_isClosedImmersion π hπ
  exact IsClosedImmersion.of_comp_isClosedImmersion _ (affineClosureι π ∣_ affineClosureChart r)

instance affineClosureChartPart_isAffine {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    IsAffine (affineClosureChartPart π).toScheme := by
  have : IsAffine (affineClosureChart (K := K) r).toScheme :=
    Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K 0) Nat.zero_lt_one
  exact isAffine_of_isAffineHom (affineClosureι π ∣_ affineClosureChart r)

theorem affineClosureChartLift_appTop_injective [IsNoetherianRing A] {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Function.Injective (affineClosureChartLift π).appTop := by
  have haffU : IsAffineOpen (affineClosureChart (K := K) r) :=
    Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K 0) Nat.zero_lt_one
  have hinj := (affineClosureMap π).toImage_app_injective ⟨affineClosureChart (K := K) r, haffU⟩
  change Function.Injective ((affineClosureToImage π).app (affineClosureChartPart π)) at hinj
  rw [← affineClosureChartLift_fac π, Scheme.Hom.comp_app] at hinj
  have : IsIso ((affineClosureChartPart π).ι.app (affineClosureChartPart π)) := by
    rw [Scheme.Opens.ι_app_self]
    infer_instance
  have hbij : Function.Bijective ((affineClosureChartPart π).ι.app (affineClosureChartPart π)) :=
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Injective ((affineClosureChartLift π).app
      ((affineClosureChartPart π).ι ⁻¹ᵁ affineClosureChartPart π)) := by
    intro a b hab
    obtain ⟨a', rfl⟩ := hbij.2 a
    obtain ⟨b', rfl⟩ := hbij.2 b
    have := hinj hab
    rw [this]
  rw [Scheme.Opens.ι_preimage_self] at h2
  exact h2

theorem affineClosureChartLift_isIso [IsNoetherianRing A] {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) : IsIso (affineClosureChartLift π) := by
  have := affineClosureChartLift_isClosedImmersion π hπ
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot _).mp (affineClosureChartLift_appTop_injective π),
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

/-- `Spec A` is an open subscheme of its projective closure. -/
theorem affineClosure_toImage_isOpenImmersion [IsNoetherianRing A] {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) : IsOpenImmersion (affineClosureToImage π) := by
  have := affineClosureChartLift_isIso π hπ
  rw [← affineClosureChartLift_fac π]
  infer_instance

/-- Its image is the part of the closure over the chart `X₀ ≠ 0`. -/
theorem affineClosure_toImage_range [IsNoetherianRing A] {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) :
    Set.range (affineClosureToImage π) = (affineClosureChartPart π : Set (affineClosure π)) := by
  have := affineClosureChartLift_isIso π hπ
  have hsurj : Function.Surjective (affineClosureChartLift π) := fun x =>
    ⟨(inv (affineClosureChartLift π)) x, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
  rw [← affineClosureChartLift_fac π, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, Scheme.Opens.range_ι]

/-- The closure lies over `K` through `ℙ^r`. -/
noncomputable instance affineClosureOver {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (affineClosure π).Over (Spec (CommRingCat.of K)) :=
  ⟨affineClosureι π ≫ polynomialProjectiveToBase (r + 1) K⟩

theorem affineClosure_over_eq {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (affineClosure π ↘ Spec (CommRingCat.of K)) =
      affineClosureι π ≫ polynomialProjectiveToBase (r + 1) K := rfl

instance affineClosure_isProper {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    IsProper (affineClosure π ↘ Spec (CommRingCat.of K)) := by
  have := polynomialProjectiveToBase_isProper (r + 1) K
  rw [affineClosure_over_eq]
  infer_instance

attribute [local instance] specAlgebraOver in
/-- `Spec A → X̄₀` is a morphism over `K`. -/
theorem affineClosureToImage_isOver {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (affineClosureToImage π).IsOver (Spec (CommRingCat.of K)) := by
  constructor
  change affineClosureToImage π ≫ affineClosureι π ≫ polynomialProjectiveToBase (r + 1) K =
    Spec.map (CommRingCat.ofHom (algebraMap K A))
  rw [Scheme.Hom.toImage_imageι_assoc]
  change (affineClosureChartMap π ≫ (affineClosureChart (K := K) r).ι) ≫
    polynomialProjectiveToBase (r + 1) K = _
  rw [Category.assoc, polynomialProjectiveAffineChart_toBase]
  unfold affineClosureChartMap
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  congr 1
  ext c
  exact affineClosureCoordHom_C π c

end Closure

section ChartImage

variable {K : Type u} [Field K] {n : ℕ} {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z]
  [X.Over (Spec (CommRingCat.of K))] [Z.Over (Spec (CommRingCat.of K))]
  (j : Z ⟶ X) [IsOpenImmersion j] [IsDominant j] [j.IsOver (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra

/-- Restriction of sections between nonempty opens as a `K`-algebra map. -/
noncomputable def sectionsRestrictAlgHom {W V : Z.Opens} [Nonempty W] [Nonempty V] (h : V ≤ W) :
    Γ(Z, W) →ₐ[K] Γ(Z, V) where
  toRingHom := (Z.presheaf.map (homOfLE h).op).hom
  commutes' k := by
    apply Z.germToFunctionField_injective V
    change Z.germToFunctionField V (Z.presheaf.map (homOfLE h).op (algebraMap K Γ(Z, W) k)) = _
    rw [germToFunctionField_restrict]
    change sectionGermAlgHom (K := K) W (algebraMap K Γ(Z, W) k) =
      sectionGermAlgHom (K := K) V (algebraMap K Γ(Z, V) k)
    simp only [AlgHom.commutes]

/-- Transport a chart of an open subscheme to the ambient scheme. -/
noncomputable def etaleChartImageOfOpenImmersion (c : EtaleChart K Z n) : EtaleChart K X n := by
  have hpre : j ⁻¹ᵁ (j ''ᵁ c.U) = c.U := j.preimage_image_eq c.U
  have : Nonempty c.U := c.nonempty
  have : Nonempty (j ⁻¹ᵁ (j ''ᵁ c.U)) := by rw [hpre]; exact c.nonempty
  have : Nonempty (j ''ᵁ c.U) := by
    obtain ⟨⟨z, hz⟩⟩ := c.nonempty
    exact ⟨⟨j z, z, hz, rfl⟩⟩
  have hle : j ''ᵁ c.U ≤ j.opensRange := by
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have : IsIso (j.app (j ''ᵁ c.U)) := j.isIso_app _ hle
  have hbij : Function.Bijective (dominantSectionsAlgHom (K := K) j (j ''ᵁ c.U)) :=
    ConcreteCategory.bijective_of_isIso (j.app (j ''ᵁ c.U))
  let e := AlgEquiv.ofBijective (dominantSectionsAlgHom (K := K) j (j ''ᵁ c.U)) hbij
  let res := sectionsRestrictAlgHom (K := K) (Z := Z) (W := c.U) (V := j ⁻¹ᵁ (j ''ᵁ c.U))
    (le_of_eq hpre)
  have hres : Function.Bijective res := by
    have : IsIso (Z.presheaf.map (homOfLE (le_of_eq hpre)).op) := by
      have : homOfLE (le_of_eq hpre) = eqToHom hpre := rfl
      rw [this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso (Z.presheaf.map (homOfLE (le_of_eq hpre)).op)
  refine ⟨j ''ᵁ c.U, (j.isAffineOpen_iff_of_isOpenImmersion).mpr c.isAffine, inferInstance,
    (e.symm.toAlgHom.comp res).comp c.coords, ?_⟩
  refine RingHom.FormallyEtale.comp c.formallyEtale ?_
  refine RingHom.FormallyEtale.comp
    (ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective hres)) ?_
  exact ringHom_formallyEtale_of_etale _ (RingHom.Etale.of_bijective e.symm.bijective)

theorem etaleChartImageOfOpenImmersion_U (c : EtaleChart K Z n) :
    (etaleChartImageOfOpenImmersion j c).U = j ''ᵁ c.U := rfl

end ChartImage

section Hyperplane

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [IsNoetherianRing A]

attribute [local instance] specAlgebraOver

omit [IsNoetherianRing A] in
theorem affineClosureChartPart_nonempty {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    Nonempty (affineClosureChartPart π) := by
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  have hx : affineClosureToImage π x ∈ Set.range (affineClosureChartPart π).ι :=
    affineClosure_range_toImage_subset π ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι] at hx
  exact ⟨⟨_, hx⟩⟩

/-- The hyperplane `X₀ = 0` does not contain the closure. -/
theorem affineClosure_X0_notMem_generic {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (MvPolynomial.X 0 : MvPolynomial (Fin (r + 1)) K) ∉
      (affineClosureι π (genericPoint (affineClosure π))).asHomogeneousIdeal := by
  have := affineClosureChartPart_nonempty π
  have hgen : genericPoint (affineClosure π) ∈ affineClosureChartPart π := genericPoint_mem _
  exact hgen

/-- The hyperplane at infinity `X₀ = 0` of the closure. -/
noncomputable abbrev affineClosureInfinity {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    CartierDivisor (affineClosure π) :=
  projectiveHyperplaneCartier (affineClosureι π) (MvPolynomial.X 0)
    (MvPolynomial.isHomogeneous_X K 0) (affineClosure_X0_notMem_generic π)

theorem affineClosureInfinity_isEffective {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (affineClosureInfinity π).IsEffective :=
  projectivePullbackHomogeneousCartier_isEffective (affineClosureι π) 1 (MvPolynomial.X 0)
    (MvPolynomial.isHomogeneous_X K 0) Nat.one_pos (affineClosure_X0_notMem_generic π)

theorem affineClosureInfinity_globallyGenerated {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    CartierIsGloballyGenerated (affineClosureInfinity π) :=
  projectiveHyperplaneCartier_globallyGenerated (affineClosureι π) (MvPolynomial.X 0)
    (MvPolynomial.isHomogeneous_X K 0) (affineClosure_X0_notMem_generic π)

theorem affineClosureInfinity_isAmpleProj {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    CartierIsAmpleProj K (affineClosureInfinity π) := by
  refine ⟨1, le_rfl, r + 1, affineClosureι π, inferInstance, rfl, MvPolynomial.X 0,
    MvPolynomial.isHomogeneous_X K 0, affineClosure_X0_notMem_generic π, 1, ?_⟩
  rw [one_nsmul, principalCartierDivisor_one, add_zero]

/-- `1` is a local equation of the hyperplane at infinity exactly over the chart `X₀ ≠ 0`. -/
theorem affineClosureInfinity_isLocalEquationAt_one_iff {r : ℕ}
    (π : MvPolynomial (Fin r) K →ₐ[K] A) (x : affineClosure π) :
    (affineClosureInfinity π).IsLocalEquationAt x 1 ↔ x ∈ affineClosureChartPart π := by
  obtain ⟨k, hk⟩ := polynomialProjective_exists_coordinate_chart (r + 1) K (affineClosureι π x)
  haveI : Nonempty (projectivePullbackCoordinateOpen (affineClosureι π) k) := ⟨⟨x, hk⟩⟩
  let kk : {k : Fin (r + 1) // Nonempty (projectivePullbackCoordinateOpen (affineClosureι π) k)} :=
    ⟨k, ⟨⟨x, hk⟩⟩⟩
  have hx : x ∈ projectivePullbackNonemptyCoordinateOpen (affineClosureι π) kk := hk
  let s := projectivePullbackHomogeneousEquation (affineClosureι π) k 1 (MvPolynomial.X 0)
    (MvPolynomial.isHomogeneous_X K 0)
  have hs0 : s ≠ 0 := projectivePullbackHomogeneousEquation_ne_zero _ k 1 _ _ Nat.one_pos
    (affineClosure_X0_notMem_generic π)
  have hrest := projectivePullbackHomogeneousCartier_restrict (affineClosureι π) 1
    (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X K 0) Nat.one_pos
    (affineClosure_X0_notMem_generic π) kk
  have hu : ∀ y ∈ projectivePullbackNonemptyCoordinateOpen (affineClosureι π) kk,
      (affineClosureInfinity π).IsLocalEquationAt y (regularEquationRationalUnit _ _ s hs0) :=
    fun y hy => CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hrest.symm hy
  have hsu : ((regularEquationRationalUnit _ _ s hs0 : (affineClosure π).functionFieldˣ) :
      (affineClosure π).functionField) =
      (affineClosure π).germToFunctionField
        (projectivePullbackNonemptyCoordinateOpen (affineClosureι π) kk) s :=
    regularEquationRationalUnit_val _ _ s hs0
  have hbasic := projectivePullbackHomogeneousEquation_basicOpen (affineClosureι π) k 1
    (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X K 0) Nat.one_pos
  constructor
  · intro h1
    have hb := mem_basicOpen_of_isLocalEquationAt_one s _ hu hsu hx h1
    change x ∈ (affineClosure π).basicOpen s at hb
    rw [hbasic] at hb
    exact hb.2
  · intro hc
    apply isLocalEquationAt_one_of_mem_basicOpen s _ hu hsu
    rw [hbasic]
    exact ⟨hx, hc⟩

omit [IsDomain A] in
theorem affineClosure_toImage_isDominant {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    IsDominant (affineClosureToImage π) := inferInstance

/-- The closure has the dimension of `A`. -/
theorem affineClosure_topologicalKrullDim {n r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) (cX : EtaleChart K (Spec (CommRingCat.of A)) n) :
    topologicalKrullDim (affineClosure π) = n := by
  have := affineClosure_toImage_isOpenImmersion π hπ
  have := affineClosureToImage_isOver π
  have : LocallyOfFiniteType (affineClosure π ↘ Spec (CommRingCat.of K)) := inferInstance
  let c' : EtaleChart K (affineClosure π) n :=
    etaleChartImageOfOpenImmersion (affineClosureToImage π) cX
  exact etaleChart_topologicalKrullDim c'

/-- The hyperplane at infinity is big. -/
theorem affineClosureInfinity_isBig [Infinite K] {n r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (hπ : Function.Surjective π) (cX : EtaleChart K (Spec (CommRingCat.of A)) n) (hn : 1 ≤ n) :
    CartierIsBig K (affineClosureInfinity π) :=
  cartierIsAmpleProj_isBig (affineClosure_topologicalKrullDim π hπ cX) hn
    (affineClosureInfinity_isAmpleProj π)

end Hyperplane

end MixedFujita
