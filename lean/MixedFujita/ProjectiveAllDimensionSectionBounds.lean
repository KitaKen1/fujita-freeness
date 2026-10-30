module
public import MixedFujita.ProjectiveAffineSectionBounds
public import MixedFujita.SmoothProperCurveSections
public import MixedFujita.ZeroDimensionalCartierFreeness

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower

/-- Proper integral schemes of dimension zero have finite-dimensional Cartier
sections over the actual base field. No algebraic closure or smoothness is required. -/
theorem properZeroDimensional_finiteDimensional_cartierSections
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X) :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  letI : ∀ y : CodimensionOnePoint X,
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)) := fun y => by
    have hle := TauCeti.coheight_le_topologicalKrullDim (y : X)
    rw [y.property, hdim] at hle
    norm_num at hle
  have hle (x : X) : Order.coheight x ≤ 1 := by
    have hbound : (Order.coheight x : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) :=
      (TauCeti.coheight_le_topologicalKrullDim x).trans (hdim.le.trans (by norm_num))
    exact_mod_cast hbound
  have h := TauCeti.AlgebraicGeometry.InvertibleSheaf.finiteDimensional_cohomology_zero
    K hle D.toInvertibleSheaf
  rw [CartierDivisor.toInvertibleSheaf_obj] at h
  letI := h
  exact Module.Finite.equiv (Scheme.Modules.cohomologyZeroBaseLinearEquiv K X D.sheaf)

/-- An actual projective Cartier embedding supplies properness, also in dimension zero. -/
theorem isProper_structureMap_of_exists_ample_cartier
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H) :
    IsProper (X ↘ Spec (CommRingCat.of K)) := by
  obtain ⟨H, m, hm, N, e, he, hbase, g, hg, hggen, f, hH⟩ := hProj
  letI := he
  have := polynomialProjectiveToBase_isProper N K
  rw [← hbase]
  infer_instance

/-- Every Cartier section space on the same integral projective base is finite,
including dimension zero; no positivity of the specified divisor is required. -/
theorem cartier_finiteDimensional_sections_of_projective_all_dimensions
    [Infinite K] {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H) (D : CartierDivisor X) :
    FiniteDimensional K Γ(D.sheaf, ⊤) := by
  by_cases hn : n = 0
  · subst n
    letI := isProper_structureMap_of_exists_ample_cartier hProj
    exact properZeroDimensional_finiteDimensional_cartierSections hdim D
  · obtain ⟨H, hH⟩ := hProj
    exact cartier_finiteDimensional_sections_of_ample hdim (by omega) hH D

/-- The affine Cartier sequence has a single polynomial upper bound in every
base dimension. In dimension zero the actual Cartier divisors vanish. -/
theorem cartier_affineMultiples_finrank_polynomial_upper_all_dimensions
    [Infinite K] {n : ℕ} (hdim : topologicalKrullDim X = n)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H) (D F : CartierDivisor X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, (Module.finrank K Γ((j • D + F).sheaf, ⊤) : ℝ) ≤
      C * ((j : ℝ) + 1) ^ n := by
  by_cases hn : n = 0
  · subst n
    refine ⟨(Module.finrank K Γ((0 : CartierDivisor X).sheaf, ⊤) : ℝ), by positivity,
      fun j => ?_⟩
    rw [zeroDimensional_cartierDivisor_eq_zero hdim (j • D + F)]
    simp only [pow_zero, mul_one, le_refl]
  · exact cartier_affineMultiples_finrank_polynomial_upper_of_projective hdim (by omega)
      hProj D F

/-- Zero-dimensional proper bases provide a genuine Iitaka exponent, rather
than a conditional assertion with finite dimensionality supplied separately. -/
theorem properZeroDimensional_cartierIitakaDimension
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = 0) (D : CartierDivisor X) :
    CartierIitakaDimension K D 0 :=
  zeroDimensional_cartierIitakaDimension_of_finiteDimensional hdim D
    (properZeroDimensional_finiteDimensional_cartierSections hdim D)

end MixedFujita
