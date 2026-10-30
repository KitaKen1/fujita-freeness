/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RegularFunctionGluing
public import MixedFujita.ProjectiveFormSectionSpaces

/-!
Extension of local sections after twisting by a hyperplane divisor (step 4). Let X be an
integral closed subscheme of projective space, compact, J the hyperplane divisor of a degree-one
form g, A a Cartier divisor, and F a form of degree d ≥ 1 not vanishing identically on X such that
A has the single equation g_β on the principal open X_F. Then for all large k the rational
function g_β⁻¹ (F/g^d)^k is an actual global section of A + k d J: the generator g_β⁻¹ of the
sheaf of A on X_F extends to X after multiplication by a power of F. Locally, on a basic open W
of an affine chart where A has an equation g_z, the ratio g_z/g_β is a regular function on the
basic open of F in W, so a power of the chart function of F clears its denominator; compactness
gives a uniform exponent. No cohomology and no coherence statement is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- The chart computation for a twisted ratio: the powers of the chart equation of g cancel. -/
theorem twist_local_identity {L : Type*} [Field L] (a b Φ v : L) (hv : v ≠ 0) (k d : ℕ) :
    (a * v ^ (k * d)) * (b * (Φ * (v⁻¹) ^ d) ^ k) = a * b * Φ ^ k := by
  have h : v ^ (k * d) * ((v⁻¹) ^ d) ^ k = 1 := by
    rw [← pow_mul, mul_comm d k, ← mul_pow, mul_inv_cancel₀ hv, one_pow]
  calc (a * v ^ (k * d)) * (b * (Φ * (v⁻¹) ^ d) ^ k)
      = a * b * Φ ^ k * (v ^ (k * d) * ((v⁻¹) ^ d) ^ k) := by
        rw [mul_pow]
        ring
    _ = a * b * Φ ^ k := by rw [h, mul_one]

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})
  (A : CartierDivisor X) {d : ℕ} (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
  (gβ : X.functionFieldˣ)

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- Near every point a power of F clears the denominator of the generator g_β⁻¹. -/
theorem twistedRatio_local_regular (hd : 0 < d)
    (hFgen : F ∉ (e (genericPoint X)).asHomogeneousIdeal)
    (hβ : ∀ y ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F,
      A.IsLocalEquationAt y gβ) (z : X) :
    ∃ (W : X.Opens) (_ : z ∈ W) (k : ℕ), ∀ k', k ≤ k' → ∀ y ∈ W,
      ∃ f : X.functionFieldˣ,
        (A + (k' * d) • projectiveHyperplaneCartier e g hg hggen).IsLocalEquationAt y f ∧
        (f : X.functionField) * (((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
          projectiveFormRatio e g hg hggen j₀ d F hF ^ k') ∈
          (algebraMap (X.presheaf.stalk y) X.functionField).range := by
  obtain ⟨j, hzj⟩ := polynomialProjective_exists_coordinate_chart n K (e z)
  have hUne : Nonempty (projectivePullbackCoordinateOpen e j) := ⟨⟨z, hzj⟩⟩
  have hU : IsAffineOpen (projectivePullbackCoordinateOpen e j) :=
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X K j) Nat.zero_lt_one).preimage e
  obtain ⟨V, hVU, hzV, gz, hV⟩ :=
    A.exists_localEquation_le (projectivePullbackCoordinateOpen e j) hzj
  have hVne : Nonempty V := ⟨⟨z, hzV⟩⟩
  obtain ⟨b, hbV, hzb⟩ := hU.exists_basicOpen_le ⟨z, hzV⟩ hzj
  have hWne : Nonempty (X.basicOpen b) := ⟨⟨z, hzb⟩⟩
  have hW : IsAffineOpen (X.basicOpen b) := hU.basicOpen b
  have hWU : X.basicOpen b ≤ projectivePullbackCoordinateOpen e j := X.basicOpen_le b
  obtain ⟨φ, hφdef⟩ : ∃ φ : Γ(X, projectivePullbackCoordinateOpen e j),
      φ = projectivePullbackHomogeneousEquation e j d F hF := ⟨_, rfl⟩
  obtain ⟨φW, hφWdef⟩ : ∃ φW : Γ(X, X.basicOpen b),
      φW = X.presheaf.map (homOfLE hWU).op φ := ⟨_, rfl⟩
  have hW'W : X.basicOpen φW ≤ X.basicOpen b := X.basicOpen_le φW
  have hW'eq : X.basicOpen φW = X.basicOpen b ⊓ (projectivePullbackCoordinateOpen e j ⊓
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F) := by
    rw [hφWdef, Scheme.basicOpen_res, hφdef,
      projectivePullbackHomogeneousEquation_basicOpen e j d F hF hd]
  have hgenb : genericPoint X ∈ X.basicOpen b := integral_genericPoint_mem_nonempty_open _
  have hgenU : genericPoint X ∈ projectivePullbackCoordinateOpen e j :=
    integral_genericPoint_mem_nonempty_open _
  have hgenF : genericPoint X ∈
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F := hFgen
  have hW'ne : Nonempty (X.basicOpen φW) :=
    ⟨⟨genericPoint X, by rw [hW'eq]; exact ⟨hgenb, hgenU, hgenF⟩⟩⟩
  -- the ratio of the two equations is a regular function on the basic open of F in W
  obtain ⟨ρ, hρ⟩ := exists_section_of_forall_mem_stalk_range (X.basicOpen φW)
    ((gz : X.functionField) * ((gβ⁻¹ : X.functionFieldˣ) : X.functionField)) (by
      intro y hy
      rw [hW'eq] at hy
      obtain ⟨hyb, -, hyF⟩ := hy
      have hgz : A.IsLocalEquationAt y gz :=
        CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV (hbV hyb)
      obtain ⟨w, hw⟩ := hgz.exists_unit_mul_eq (hβ y hyF)
      refine ⟨(w : X.presheaf.stalk y), ?_⟩
      rw [← hw, Units.val_inv_eq_inv_val, mul_assoc, mul_inv_cancel₀ (Units.ne_zero gβ),
        mul_one])
  obtain ⟨k, r, hkr⟩ := affine_basicOpen_section_clear hW φW hW'W rfl ρ
  have hΦ : X.germToFunctionField (X.basicOpen b) φW =
      X.germToFunctionField (projectivePullbackCoordinateOpen e j) φ := by
    rw [hφWdef]
    exact germToFunctionField_restrict X hWU φ
  have hkr' : (gz : X.functionField) * ((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
      X.germToFunctionField (projectivePullbackCoordinateOpen e j) φ ^ k =
        X.germToFunctionField (X.basicOpen b) r := by
    have h1 := congrArg (X.germToFunctionField (X.basicOpen φW)) hkr
    rw [germToFunctionField_restrict X hW'W r] at h1
    refine Eq.trans ?_ h1
    refine Eq.trans ?_ (map_mul _ _ _).symm
    rw [hρ]
    refine congrArg _ ?_
    refine Eq.trans ?_ (map_pow _ _ _).symm
    rw [germToFunctionField_restrict X hW'W φW, hΦ]
  have hR : projectiveFormRatio e g hg hggen j₀ d F hF =
      X.germToFunctionField (projectivePullbackCoordinateOpen e j) φ *
        ((projectiveHyperplaneUnit e g hg hggen ⟨j, hUne⟩ : X.functionFieldˣ) :
          X.functionField)⁻¹ ^ d := by
    rw [projectiveFormRatio_chart_independent e g hg hggen j₀ ⟨j, hUne⟩, hφdef]
    unfold projectiveFormRatio
    rw [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  refine ⟨X.basicOpen b, hzb, k, fun k' hk' y hy => ?_⟩
  have hgz : A.IsLocalEquationAt y gz :=
    CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV (hbV hy)
  have hJ := cartierLocalEquation_pow (projectiveHyperplaneCartier e g hg hggen) y _
    (projectiveHyperplane_isLocalEquationAt e g hg hggen ⟨j, hUne⟩ y (hWU hy)) (k' * d)
  refine ⟨gz * projectiveHyperplaneUnit e g hg hggen ⟨j, hUne⟩ ^ (k' * d), hgz.mul hJ, ?_⟩
  refine ⟨X.presheaf.germ (X.basicOpen b) y hy (r * φW ^ (k' - k)), ?_⟩
  rw [X.algebraMap_germ_eq_germToFunctionField hy, Units.val_mul, Units.val_pow_eq_pow_val, hR,
    twist_local_identity _ _ _ _ (Units.ne_zero _)]
  calc X.germToFunctionField (X.basicOpen b) (r * φW ^ (k' - k))
      = X.germToFunctionField (X.basicOpen b) r *
          X.germToFunctionField (X.basicOpen b) φW ^ (k' - k) :=
        (map_mul _ _ _).trans (congrArg _ (map_pow _ _ _))
    _ = (gz : X.functionField) * ((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
          X.germToFunctionField (projectivePullbackCoordinateOpen e j) φ ^ k' := by
        rw [← hkr', hΦ, mul_assoc, ← pow_add, Nat.add_sub_cancel' hk']

/-- For all large k the rational function g_β⁻¹ (F/g^d)^k is a global section of A + k d J. -/
theorem twistedRatio_mem_sections [CompactSpace X] (hd : 0 < d)
    (hFgen : F ∉ (e (genericPoint X)).asHomogeneousIdeal)
    (hβ : ∀ y ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F,
      A.IsLocalEquationAt y gβ) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      (rationalFunctionsEquiv (X := X) ⊤).symm
        (((gβ⁻¹ : X.functionFieldˣ) : X.functionField) *
          projectiveFormRatio e g hg hggen j₀ d F hF ^ k) ∈
        (A + (k * d) • projectiveHyperplaneCartier e g hg hggen).sections ⊤ := by
  choose W hzW kz hW using twistedRatio_local_regular e g hg hggen j₀ A F hF gβ hd hFgen hβ
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun z => (W z : Set X))
    (fun z => (W z).isOpen) (fun z _ => Set.mem_iUnion.mpr ⟨z, hzW z⟩)
  refine ⟨t.sup kz, fun k hk => ?_⟩
  apply CartierDivisor.mem_sections_iff_exists.mpr
  intro y _
  obtain ⟨z, hzt, hyz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ y))
  obtain ⟨f, hf, hmem⟩ := hW z k ((Finset.le_sup hzt).trans hk) y hyz
  refine ⟨f, hf, ?_⟩
  rw [LinearEquiv.apply_symm_apply]
  exact hmem

end MixedFujita
