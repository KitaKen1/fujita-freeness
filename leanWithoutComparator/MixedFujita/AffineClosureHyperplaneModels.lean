/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineProjectiveClosure
public import MixedFujita.CartierSectionsEmbedding
public import MixedFujita.CartierSectionsAtlas
public import MixedFujita.ProjectiveFormSectionSpaces
public import MixedFujita.ProjectivePullbackFixedClass
public import MixedFujita.NondegenerateFunctionSNCModel
public import MixedFujita.PrincipalCartierGlobalGeneration

/-!
Hyperplane sections of the projective closure through given functions (step 9, compactified
principalizing models).

Finitely many elements `b_i` of a finitely generated `K`-algebra `A` can be taken among the images
of the variables of a surjection `π` from a polynomial ring
(`exists_surjective_mvPolynomial_with_values`). In the projective closure `X̄₀` of `Spec A` for such
a `π`, the hyperplane `X_{i+1} = 0` cuts an effective Cartier divisor `H_i` whenever `π(X_i) ≠ 0`
(`affineClosureHyperplane`), and on `Spec A` it is the divisor of the function `π(X_i)`
(`cartierPullback_affineClosureHyperplane`): the closure map is the affine chart of `X₀`
composed with `Spec` of the evaluation `x_j ↦ π(X_{j-1})` (`affineClosureMap_eq_awayι`), so the
chart equation `X_{i+1}/X₀` restricts to `π(X_i)`. The hyperplane at infinity `D_∞ = {X₀ = 0}`
restricts to zero, and `H_i - D_∞` is principal, so `D_∞ - H_i` is globally generated
(`cartierIsGloballyGenerated_affineClosureInfinity_sub_hyperplane`). These are the inputs of the
sum-principalizing model on `X̄₀` whose restriction to `Spec A` is the original principalizing
model of the functions `b_i`.
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

section Generators

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- Finitely many elements of a finitely generated algebra are images of variables of a
surjection from a polynomial ring. -/
theorem exists_surjective_mvPolynomial_with_values [Algebra.FiniteType K A] {ι : Type*}
    [Finite ι] (b : ι → A) :
    ∃ (r : ℕ) (π : MvPolynomial (Fin r) K →ₐ[K] A) (idx : ι → Fin r),
      Function.Surjective π ∧ ∀ i, π (MvPolynomial.X (idx i)) = b i := by
  obtain ⟨r₀, π₀, hπ₀⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  let e := Finite.equivFin ι
  let a : Fin (r₀ + Nat.card ι) → A :=
    Fin.append (fun i => π₀ (MvPolynomial.X i)) (fun k => b (e.symm k))
  refine ⟨r₀ + Nat.card ι, MvPolynomial.aeval a, fun i => Fin.natAdd r₀ (e i), ?_, ?_⟩
  · intro y
    obtain ⟨p, rfl⟩ := hπ₀ y
    refine ⟨MvPolynomial.rename (Fin.castAdd (Nat.card ι)) p, ?_⟩
    have ha : a ∘ Fin.castAdd (Nat.card ι) = π₀ ∘ MvPolynomial.X := by
      funext i
      simp [a, Fin.append_left]
    rw [MvPolynomial.aeval_rename, ha]
    exact (DFunLike.congr_fun (MvPolynomial.aeval_unique π₀) p).symm
  · intro i
    simp [a, Fin.append_right]

end Generators

section Chart

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]

/-- The degree-zero localization at `X₀` evaluated on `A`: `X_j / X₀ ↦ π(X_{j-1})`. -/
noncomputable def affineClosureChartEval {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)
      (MvPolynomial.X 0) →+* Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp
    ((affineClosureCoordHom π).comp (projectiveChartRingEquiv K (0 : Fin (r + 1))).toRingHom)

/-- The closure map is `Spec` of the chart evaluation followed by the affine chart of `X₀`. -/
theorem affineClosureMap_eq_awayι {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    affineClosureMap π = (Spec (CommRingCat.of A)).toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (affineClosureChartEval π)) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) (MvPolynomial.X 0)
          (MvPolynomial.isHomogeneous_X K 0) Nat.zero_lt_one := by
  have h1 : CommRingCat.ofHom (affineClosureChartEval π) =
      CommRingCat.ofHom (projectiveChartRingEquiv K (0 : Fin (r + 1))).toRingHom ≫
        CommRingCat.ofHom (affineClosureCoordHom π) ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv :=
    rfl
  rw [h1]
  simp only [Spec.map_comp, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
  unfold affineClosureMap affineClosureChartMap polynomialProjectiveAffineChartIso
  rw [Iso.trans_inv, Category.assoc, Category.assoc]
  have h2 : (Scheme.Spec.mapIso
      (projectiveChartRingEquiv K (0 : Fin (r + 1))).symm.toCommRingCatIso.op).inv =
      Spec.map (CommRingCat.ofHom (projectiveChartRingEquiv K (0 : Fin (r + 1))).toRingHom) := rfl
  have h3 : (polynomialProjectiveCoordinateChartIso (r + 1) K 0).inv ≫
      (affineClosureChart (K := K) r).ι =
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) (MvPolynomial.X 0)
        (MvPolynomial.isHomogeneous_X K 0) Nat.zero_lt_one := rfl
  rw [h2, h3]

/-- Pulling the chart functions of `X₀` back to `Spec A` is the chart evaluation. -/
theorem affineClosureMap_appLE_awayToSection {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (z : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)
      (MvPolynomial.X 0))
    (e : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      affineClosureMap π ⁻¹ᵁ affineClosureChart (K := K) r) :
    (affineClosureMap π).appLE (affineClosureChart (K := K) r) ⊤ e
        (Proj.awayToSection _ (MvPolynomial.X 0) z) = affineClosureChartEval π z := by
  have hφ := affineClosureMap_eq_awayι π
  have e' : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      ((Spec (CommRingCat.of A)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (affineClosureChartEval π)) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K) (MvPolynomial.X 0)
          (MvPolynomial.isHomogeneous_X K 0) Nat.zero_lt_one) ⁻¹ᵁ
        affineClosureChart (K := K) r := hφ ▸ e
  rw [schemeHom_appLE_congr_hom hφ _ ⊤ e e']
  exact proj_awayι_appLE_awayToSection _ (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X K 0)
    Nat.zero_lt_one (affineClosureChartEval π) z e'

/-- The chart equation `X_{i+1}/X₀` pulls back to `π(X_i)` on `Spec A`. -/
theorem affineClosureMap_appLE_homogeneousEquation_X {r : ℕ}
    (π : MvPolynomial (Fin r) K →ₐ[K] A) (i : Fin r)
    (e : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      affineClosureMap π ⁻¹ᵁ affineClosureChart (K := K) r) :
    (affineClosureMap π).appLE (affineClosureChart (K := K) r) ⊤ e
        (projectiveHomogeneousEquation K (0 : Fin (r + 1)) 1 (MvPolynomial.X i.succ)
          (MvPolynomial.isHomogeneous_X K i.succ)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (π (MvPolynomial.X i)) := by
  rw [projectiveHomogeneousEquation, affineClosureMap_appLE_awayToSection]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv (affineClosureCoordHom π
    (projectiveChartLocalizationToAffine K 0 _)) = _
  rw [projectiveChartLocalizationToAffine_mk K 0 1 _ (MvPolynomial.isHomogeneous_X K i.succ),
    projectiveDehomogenize_X_other K 0 ⟨i.succ, Fin.succ_ne_zero i⟩]
  simp [affineClosureCoordHom]

/-- The chart equation of `X_{i+1}` on the closure restricts to `π(X_i)` on `Spec A`. -/
theorem affineClosureToImage_appLE_chartEquation {r : ℕ}
    (π : MvPolynomial (Fin r) K →ₐ[K] A) (i : Fin r)
    (e : (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      affineClosureToImage π ⁻¹ᵁ projectivePullbackCoordinateOpen (affineClosureι π) 0) :
    (affineClosureToImage π).appLE (projectivePullbackCoordinateOpen (affineClosureι π) 0) ⊤ e
        (projectivePullbackHomogeneousEquation (affineClosureι π) 0 1 (MvPolynomial.X i.succ)
          (MvPolynomial.isHomogeneous_X K i.succ)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (π (MvPolynomial.X i)) := by
  have h := Scheme.Hom.comp_appLE (affineClosureToImage π) (affineClosureι π)
    (affineClosureChart (K := K) r) ⊤ e
  have h2 := ConcreteCategory.congr_hom h
    (projectiveHomogeneousEquation K (0 : Fin (r + 1)) 1 (MvPolynomial.X i.succ)
      (MvPolynomial.isHomogeneous_X K i.succ))
  rw [CommRingCat.comp_apply] at h2
  rw [projectivePullbackHomogeneousEquation]
  refine h2.symm.trans ?_
  rw [schemeHom_appLE_congr_hom (Scheme.Hom.toImage_imageι (affineClosureMap π))
    (affineClosureChart (K := K) r) ⊤ e e]
  exact affineClosureMap_appLE_homogeneousEquation_X π i e

end Chart

section Hyperplanes

variable {K : Type u} [Field K] {A : Type u} [CommRing A] [IsDomain A] [Algebra K A]
  [IsNoetherianRing A]

attribute [local instance] specAlgebraOver

omit [IsDomain A] [IsNoetherianRing A] in
theorem affineClosureToImage_top_le_chart {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    (⊤ : (Spec (CommRingCat.of A)).Opens) ≤
      affineClosureToImage π ⁻¹ᵁ projectivePullbackCoordinateOpen (affineClosureι π) 0 := by
  intro x _
  have hx := affineClosure_range_toImage_subset π ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι] at hx
  exact hx

/-- The hyperplane `X_{i+1} = 0` does not contain the closure when `π(X_i) ≠ 0`. -/
theorem affineClosure_Xsucc_notMem_generic {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) :
    (MvPolynomial.X i.succ : MvPolynomial (Fin (r + 1)) K) ∉
      (affineClosureι π (genericPoint (affineClosure π))).asHomogeneousIdeal := by
  haveI : Nonempty (projectivePullbackCoordinateOpen (affineClosureι π) (0 : Fin (r + 1))) :=
    affineClosureChartPart_nonempty π
  intro h
  have h0 := (projectivePullbackHomogeneousEquation_eq_zero_iff (affineClosureι π)
    (0 : Fin (r + 1)) 1 (MvPolynomial.X i.succ) (MvPolynomial.isHomogeneous_X K i.succ)).mpr h
  apply hi
  have h1 := affineClosureToImage_appLE_chartEquation π i (affineClosureToImage_top_le_chart π)
  rw [h0, map_zero] at h1
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom h1
  rw [map_zero, Iso.inv_hom_id_apply] at h2
  exact h2.symm

/-- The hyperplane section `X_{i+1} = 0` of the closure. -/
noncomputable abbrev affineClosureHyperplane {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) : CartierDivisor (affineClosure π) :=
  projectiveHyperplaneCartier (affineClosureι π) (MvPolynomial.X i.succ)
    (MvPolynomial.isHomogeneous_X K i.succ) (affineClosure_Xsucc_notMem_generic π i hi)

theorem affineClosureHyperplane_isEffective {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) : (affineClosureHyperplane π i hi).IsEffective :=
  projectivePullbackHomogeneousCartier_isEffective (affineClosureι π) 1 (MvPolynomial.X i.succ)
    (MvPolynomial.isHomogeneous_X K i.succ) Nat.one_pos (affineClosure_Xsucc_notMem_generic π i hi)

/-- The equation of the hyperplane section on the chart `X₀ ≠ 0` restricts to the function
`π(X_i)` on `Spec A`. -/
theorem affineClosureToImage_hyperplaneUnit {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) :
    Units.map (dominantFunctionFieldMap (affineClosureToImage π)).hom.toMonoidHom
        (projectiveHyperplaneUnit (affineClosureι π) (MvPolynomial.X i.succ)
          (MvPolynomial.isHomogeneous_X K i.succ) (affineClosure_Xsucc_notMem_generic π i hi)
          ⟨0, affineClosureChartPart_nonempty π⟩) =
      specFunctionRationalUnit (π (MvPolynomial.X i)) hi := by
  haveI : Nonempty (projectivePullbackCoordinateOpen (affineClosureι π) (0 : Fin (r + 1))) :=
    affineClosureChartPart_nonempty π
  apply Units.ext
  rw [Units.coe_map]
  change (dominantFunctionFieldMap (affineClosureToImage π)).hom
      ((affineClosure π).germToFunctionField
        (projectivePullbackCoordinateOpen (affineClosureι π) (0 : Fin (r + 1)))
        (projectivePullbackHomogeneousEquation (affineClosureι π) 0 1 (MvPolynomial.X i.succ)
          (MvPolynomial.isHomogeneous_X K i.succ))) = _
  rw [dominantFunctionFieldMap_germ (affineClosureToImage π) _ ⊤
      (affineClosureToImage_top_le_chart π),
    affineClosureToImage_appLE_chartEquation π i (affineClosureToImage_top_le_chart π)]
  rfl

/-- The hyperplane section `X_{i+1} = 0` restricts to the divisor of `π(X_i)` on `Spec A`. -/
theorem cartierPullback_affineClosureHyperplane {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A)
    (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) :
    cartierPullback (affineClosureToImage π) (affineClosureHyperplane π i hi) =
      principalCartierDivisor (Spec (CommRingCat.of A))
        (specFunctionRationalUnit (π (MvPolynomial.X i)) hi) := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  refine ⟨specFunctionRationalUnit (π (MvPolynomial.X i)) hi, ?_,
    CartierDivisor.isLocalEquationAt_principalCartierDivisor t _⟩
  have hz : affineClosureToImage π t ∈
      projectivePullbackCoordinateOpen (affineClosureι π) (0 : Fin (r + 1)) :=
    affineClosureToImage_top_le_chart π (Opens.mem_top t)
  have h := cartierPullback_isLocalEquationAt (affineClosureToImage π)
    (affineClosureHyperplane π i hi) t
    (projectiveHyperplane_isLocalEquationAt (affineClosureι π) (MvPolynomial.X i.succ)
      (MvPolynomial.isHomogeneous_X K i.succ) (affineClosure_Xsucc_notMem_generic π i hi)
      ⟨0, affineClosureChartPart_nonempty π⟩ _ hz)
  rwa [affineClosureToImage_hyperplaneUnit π i hi] at h

/-- The hyperplane at infinity restricts to zero on `Spec A`. -/
theorem cartierPullback_affineClosureInfinity {r : ℕ} (π : MvPolynomial (Fin r) K →ₐ[K] A) :
    cartierPullback (affineClosureToImage π) (affineClosureInfinity π) = 0 := by
  apply cartierDivisor_eq_of_isLocalEquationAt
  intro t
  refine ⟨1, ?_, CartierDivisor.isLocalEquationAt_zero t⟩
  have h1 := (affineClosureInfinity_isLocalEquationAt_one_iff π (affineClosureToImage π t)).mpr
    (affineClosureToImage_top_le_chart π (Opens.mem_top t))
  simpa using cartierPullback_isLocalEquationAt (affineClosureToImage π) _ t h1

/-- A hyperplane section differs from the hyperplane at infinity by a principal divisor. -/
theorem exists_affineClosureHyperplane_eq_add_principal {r : ℕ}
    (π : MvPolynomial (Fin r) K →ₐ[K] A) (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) :
    ∃ u : (affineClosure π).functionFieldˣ,
      affineClosureHyperplane π i hi =
        affineClosureInfinity π + principalCartierDivisor (affineClosure π) u :=
  ⟨_, projectivePullbackHomogeneousCartier_eq_principalShift (affineClosureι π)
    ⟨0, affineClosureChartPart_nonempty π⟩ 1 (MvPolynomial.X i.succ)
    (MvPolynomial.isHomogeneous_X K i.succ) (MvPolynomial.X 0) (MvPolynomial.isHomogeneous_X K 0)
    Nat.one_pos (affineClosure_Xsucc_notMem_generic π i hi) (affineClosure_X0_notMem_generic π)⟩

/-- The hyperplane at infinity minus a hyperplane section is globally generated. -/
theorem cartierIsGloballyGenerated_affineClosureInfinity_sub_hyperplane {r : ℕ}
    (π : MvPolynomial (Fin r) K →ₐ[K] A) (i : Fin r) (hi : π (MvPolynomial.X i) ≠ 0) :
    CartierIsGloballyGenerated (affineClosureInfinity π - affineClosureHyperplane π i hi) := by
  obtain ⟨u, hu⟩ := exists_affineClosureHyperplane_eq_add_principal π i hi
  rw [hu, sub_add_cancel_left, ← principalCartierDivisor_inv]
  exact principalCartierDivisor_globallyGenerated _

end Hyperplanes

end MixedFujita
