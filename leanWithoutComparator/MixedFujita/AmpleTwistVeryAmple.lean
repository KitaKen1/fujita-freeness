/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedSectionFamily
public import MixedFujita.CartierSectionsEmbedding
public import MixedFujita.ProjectiveBaseConstants

/-!
A Cartier divisor plus every large multiple of a very ample divisor is very ample (step 4). Let X be
an integral closed subscheme of projective space over a field, J the hyperplane divisor of a
degree-one form, and A a Cartier divisor. Every point has a principal open X_F, F = X_i P, inside
a coordinate chart on which A has one equation; finitely many cover X. For each of them the
generator of A on X_F, multiplied by a power of F, is a global section of a twist, and with forms
of the complementary degree this gives sections of A + N J for every large common N: one generating
exactly on X_F, sections whose ratios to it are the affine coordinates x_l/x_i, and one whose
ratio is the inverse of the chart function of F. These ratios generate the functions on the
affine open X_F, so by the criterion for sections A + N J is very ample in the projective sense.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- The forms of degree d + (r + 1) attached to a principal open X_F inside the chart of X_i:
F X_i^(r+1), X_i^(d+r+1), and F X_i^r X_l. -/
noncomputable def twistChartForm {K : Type u} [Field K] {n : ℕ} (i : Fin n)
    (F : MvPolynomial (Fin n) K) (d r : ℕ) :
    Option (Option (Fin n)) → MvPolynomial (Fin n) K
  | none => F * MvPolynomial.X i ^ (r + 1)
  | some none => MvPolynomial.X i ^ (d + (r + 1))
  | some (some l) => F * (MvPolynomial.X i ^ r * MvPolynomial.X l)

theorem twistChartForm_isHomogeneous {K : Type u} [Field K] {n : ℕ} (i : Fin n)
    (F : MvPolynomial (Fin n) K) (d r : ℕ) (hF : F.IsHomogeneous d)
    (o : Option (Option (Fin n))) : (twistChartForm i F d r o).IsHomogeneous (d + (r + 1)) := by
  rcases o with _ | _ | l
  · exact hF.mul (MvPolynomial.isHomogeneous_X_pow i (r + 1))
  · exact MvPolynomial.isHomogeneous_X_pow i (d + (r + 1))
  · exact hF.mul ((MvPolynomial.isHomogeneous_X_pow i r).mul (MvPolynomial.isHomogeneous_X K l))

/-- Dehomogenizing F X_i^(r+1) on the chart of X_i gives the dehomogenization of F. -/
theorem projectiveDehomogenize_twistChartForm_none {K : Type u} [Field K] {n : ℕ} (i : Fin n)
    (F : MvPolynomial (Fin n) K) (d r : ℕ) :
    projectiveDehomogenize K i (twistChartForm i F d r none) = projectiveDehomogenize K i F := by
  change projectiveDehomogenize K i (F * MvPolynomial.X i ^ (r + 1)) = _
  rw [map_mul, map_pow, projectiveDehomogenize_X_self, one_pow, mul_one]

/-- Dehomogenizing a power of X_i on the chart of X_i gives 1. -/
theorem projectiveDehomogenize_twistChartForm_inv {K : Type u} [Field K] {n : ℕ} (i : Fin n)
    (F : MvPolynomial (Fin n) K) (d r : ℕ) :
    projectiveDehomogenize K i (twistChartForm i F d r (some none)) = 1 := by
  change projectiveDehomogenize K i (MvPolynomial.X i ^ (d + (r + 1))) = _
  rw [map_pow, projectiveDehomogenize_X_self, one_pow]

/-- Dehomogenizing F X_i^r X_l on the chart of X_i. -/
theorem projectiveDehomogenize_twistChartForm_coord {K : Type u} [Field K] {n : ℕ} (i : Fin n)
    (F : MvPolynomial (Fin n) K) (d r : ℕ) (l : Fin n) :
    projectiveDehomogenize K i (twistChartForm i F d r (some (some l))) =
      projectiveDehomogenize K i F * projectiveDehomogenize K i (MvPolynomial.X l) := by
  change projectiveDehomogenize K i (F * (MvPolynomial.X i ^ r * MvPolynomial.X l)) = _
  rw [map_mul, map_mul, map_pow, projectiveDehomogenize_X_self, one_pow, one_mul]

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))]
  (e : X ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

omit [X.Over (Spec (CommRingCat.of K))] in
/-- Every point has a principal open X_F inside a coordinate chart on which a Cartier divisor has
a single equation. -/
theorem exists_principalOpen_localEquation (A : CartierDivisor X) (x : X) :
    ∃ (i : Fin n) (d : ℕ) (F : MvPolynomial (Fin n) K) (_ : F.IsHomogeneous d)
      (gx : X.functionFieldˣ), 0 < d ∧
      x ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F ∧
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F ≤
        projectivePullbackCoordinateOpen e i ∧
      ∀ y ∈ e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) F,
        A.IsLocalEquationAt y gx := by
  obtain ⟨i, hxi⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  have hU' := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) Nat.zero_lt_one
  have hU : IsAffineOpen (projectivePullbackCoordinateOpen e i) := hU'.preimage e
  obtain ⟨V, hVU, hxV, gx, hV⟩ :=
    A.exists_localEquation_le (projectivePullbackCoordinateOpen e i) hxi
  have hVne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨b, hbV, hxb⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hxi
  have ha : Function.Surjective (Proj.awayToSection
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X i)) := by
    simpa only [Proj.basicOpenIsoAway_hom] using
      (ConcreteCategory.bijective_of_isIso (Proj.basicOpenIsoAway
        (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X K i) Nat.zero_lt_one).hom).2
  obtain ⟨s, hs⟩ := e.app_surjective _ hU' b
  obtain ⟨z, hz⟩ := ha s
  obtain ⟨δ, P, hP, hmk⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.isHomogeneous_X K i) z
  have hP' : P.IsHomogeneous δ := by simpa using hP
  have hb : b = projectivePullbackHomogeneousEquation e i δ P hP' := by
    rw [← hs, ← hz, ← hmk]
    rfl
  have hF : (MvPolynomial.X i * P).IsHomogeneous (δ + 1) := by
    simpa [add_comm] using (MvPolynomial.isHomogeneous_X K i).mul hP'
  have hFU : e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K)
      (MvPolynomial.X i * P) ≤ projectivePullbackCoordinateOpen e i := by
    rw [Proj.basicOpen_mul]
    exact fun y ⟨hy, _⟩ => hy
  have hbF : X.basicOpen b = e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K)
      (MvPolynomial.X i * P) := by
    rw [hb, ← projectivePullbackHomogeneousEquation_X_mul e i δ P hP',
      projectivePullbackHomogeneousEquation_basicOpen e i (δ + 1) (MvPolynomial.X i * P) _
        (Nat.succ_pos δ)]
    exact inf_eq_right.mpr hFU
  refine ⟨i, δ + 1, MvPolynomial.X i * P, hF, gx, Nat.succ_pos δ, hbF ▸ hxb, hFU, fun y hy => ?_⟩
  exact CartierDivisor.isLocalEquationAt_of_rationalUnitClass_eq hV (hbV (hbF ▸ hy))

omit [IsIntegral X] in
/-- The constants of a scheme over a field, in the two notations used here. -/
theorem schemeBaseScalars_apply (c : K) :
    schemeBaseScalars K X c = Scheme.Modules.baseRingToGlobalSections K X c := by
  rw [Scheme.Modules.baseRingToGlobalSections_apply]
  rfl

include he in
/-- Generation of the functions on a principal open of a chart by ratios of sections: the
affine coordinates and the inverse of the chart function. -/
theorem eval₂Hom_ratio_surjective_of_chart (D : CartierDivisor X) {M : ℕ}
    (t : Fin M → Γ(D.sheaf, ⊤)) (q₀ : Fin M) (h₀ : t q₀ ≠ 0) (i : Fin n)
    [Nonempty (projectivePullbackCoordinateOpen e i)] {d : ℕ}
    (F : MvPolynomial (Fin n) K) (hF : F.IsHomogeneous d)
    (hV : cartierSectionNonvanishingOpen D (t q₀) =
      X.basicOpen (projectivePullbackHomogeneousEquation e i d F hF))
    (hcoord : ∀ l : Fin n, ∃ q, (cartierSectionRational D (t q₀))⁻¹ *
        cartierSectionRational D (t q) =
      X.germToFunctionField (projectivePullbackCoordinateOpen e i)
        (projectivePullbackHomogeneousEquation e i 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)))
    (hinv : ∃ q, (cartierSectionRational D (t q₀))⁻¹ * cartierSectionRational D (t q) =
      (X.germToFunctionField (projectivePullbackCoordinateOpen e i)
        (projectivePullbackHomogeneousEquation e i d F hF))⁻¹) :
    Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top :
        cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (fun q => cartierSectionRatio D (t q₀) h₀ (t q))) := by
  have hVne : Nonempty (cartierSectionNonvanishingOpen D (t q₀)) :=
    (cartierSectionNonvanishingOpen_nonempty_iff D (t q₀)).mpr h₀
  have hU : IsAffineOpen (projectivePullbackCoordinateOpen e i) :=
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X K i) Nat.zero_lt_one).preimage e
  have hVU : cartierSectionNonvanishingOpen D (t q₀) ≤ projectivePullbackCoordinateOpen e i :=
    hV.le.trans (X.basicOpen_le _)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : MvPolynomial (Fin M) K →+* Γ(X, cartierSectionNonvanishingOpen D (t q₀)),
      Φ = MvPolynomial.eval₂Hom
        ((X.presheaf.map (homOfLE (le_top :
          cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
        (fun q => cartierSectionRatio D (t q₀) h₀ (t q)) := ⟨_, rfl⟩
  rw [← hΦ]
  have hX : ∀ q, cartierSectionRatio D (t q₀) h₀ (t q) ∈ Φ.range := fun q =>
    ⟨MvPolynomial.X q, by rw [hΦ, MvPolynomial.eval₂Hom_X']⟩
  -- the affine coordinates
  have hcoordS : ∀ l : Fin n, X.presheaf.map (homOfLE hVU).op
      (projectivePullbackHomogeneousEquation e i 1 (MvPolynomial.X l)
        (MvPolynomial.isHomogeneous_X K l)) ∈ Φ.range := by
    intro l
    obtain ⟨q, hq⟩ := hcoord l
    have heq : X.presheaf.map (homOfLE hVU).op
        (projectivePullbackHomogeneousEquation e i 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)) = cartierSectionRatio D (t q₀) h₀ (t q) := by
      apply X.germToFunctionField_injective (cartierSectionNonvanishingOpen D (t q₀))
      rw [germToFunctionField_restrict X hVU, cartierSectionRatio_germToFunctionField, hq]
    rw [heq]
    exact hX q
  -- all functions of the chart
  have hpoly : ∀ p : MvPolynomial {j : Fin n // j ≠ i} K,
      X.presheaf.map (homOfLE hVU).op (projectivePullbackAffinePolynomialMap e i p) ∈ Φ.range := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨MvPolynomial.C c, ?_⟩
      apply X.germToFunctionField_injective (cartierSectionNonvanishingOpen D (t q₀))
      have htop : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
      have hL : X.germToFunctionField (cartierSectionNonvanishingOpen D (t q₀))
            (Φ (MvPolynomial.C c)) =
          X.germToFunctionField ⊤ (schemeBaseScalars K X c) := by
        rw [hΦ, MvPolynomial.eval₂Hom_C]
        exact germToFunctionField_restrict X
          (le_top : cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤) (schemeBaseScalars K X c)
      have hR : X.germToFunctionField (cartierSectionNonvanishingOpen D (t q₀))
            (X.presheaf.map (homOfLE hVU).op
              (projectivePullbackAffinePolynomialMap e i (MvPolynomial.C c))) =
          X.germToFunctionField ⊤ (Scheme.Modules.baseRingToGlobalSections K X c) := by
        rw [germToFunctionField_restrict X hVU,
          projectivePullbackAffinePolynomialMap_C e he i c]
        exact germToFunctionField_restrict X
          (le_top : projectivePullbackCoordinateOpen e i ≤ ⊤) _
      rw [hL, hR, schemeBaseScalars_apply]
    | add p q hp hq =>
      rw [map_add, map_add]
      exact Φ.range.add_mem hp hq
    | mul_X p l hp =>
      rw [map_mul, map_mul]
      refine Φ.range.mul_mem hp ?_
      have hl : projectivePullbackAffinePolynomialMap e i (MvPolynomial.X l) =
          projectivePullbackHomogeneousEquation e i 1 (MvPolynomial.X l.val)
            (MvPolynomial.isHomogeneous_X K l.val) := by
        rw [projectivePullbackHomogeneousEquation_eq_affine, projectiveDehomogenize_X_other]
      rw [hl]
      exact hcoordS l.val
  have hres : ∀ r : Γ(X, projectivePullbackCoordinateOpen e i),
      X.presheaf.map (homOfLE hVU).op r ∈ Φ.range := by
    intro r
    obtain ⟨p, rfl⟩ := projectivePullbackAffinePolynomialMap_surjective e i r
    exact hpoly p
  -- the inverse of the chart function
  obtain ⟨qi, hqi⟩ := hinv
  have ha0 : X.germToFunctionField (projectivePullbackCoordinateOpen e i)
      (projectivePullbackHomogeneousEquation e i d F hF) ≠ 0 := by
    intro h0
    have hz : projectivePullbackHomogeneousEquation e i d F hF = 0 :=
      X.germToFunctionField_injective _ (h0.trans (map_zero _).symm)
    rw [hz, Scheme.basicOpen_zero] at hV
    obtain ⟨⟨y, hy⟩⟩ := hVne
    rw [hV] at hy
    simp at hy
  have hinvS : X.presheaf.map (homOfLE hVU).op
        (projectivePullbackHomogeneousEquation e i d F hF) *
      cartierSectionRatio D (t q₀) h₀ (t qi) = 1 := by
    apply X.germToFunctionField_injective (cartierSectionNonvanishingOpen D (t q₀))
    refine Eq.trans (map_mul _ _ _) ?_
    rw [germToFunctionField_restrict X hVU, cartierSectionRatio_germToFunctionField, hqi,
      mul_inv_cancel₀ ha0, map_one]
  intro ξ
  obtain ⟨m, r, hmr⟩ := affine_basicOpen_section_clear hU
    (projectivePullbackHomogeneousEquation e i d F hF) hVU hV ξ
  have hξ : ξ = X.presheaf.map (homOfLE hVU).op r *
      cartierSectionRatio D (t q₀) h₀ (t qi) ^ m := by
    rw [← hmr, mul_assoc, ← mul_pow, hinvS, one_pow, mul_one]
  have hmem : ξ ∈ Φ.range := by
    rw [hξ]
    exact Φ.range.mul_mem (hres r) (Φ.range.pow_mem (hX qi) m)
  exact RingHom.mem_range.mp hmem

variable (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal) (A : CartierDivisor X)

include he in
/-- A Cartier divisor plus every sufficiently large multiple of the hyperplane divisor is very
ample. -/
theorem eventually_nsmul_add_cartierIsVeryAmpleProj :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      CartierIsVeryAmpleProj K (A + N • projectiveHyperplaneCartier e g hg hggen) := by
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← he]
    have := polynomialProjectiveToBase_isProper n K
    infer_instance
  have hcompact : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (CommRingCat.of K))
  obtain ⟨jg, hjg⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint X))
  have j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨jg, ⟨⟨genericPoint X, hjg⟩⟩⟩
  choose i d F hF gx hd hxF hFU hloc using exists_principalOpen_localEquation e A
  have hne : ∀ x, Nonempty (e ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x) : X.Opens) := fun x => ⟨⟨x, hxF x⟩⟩
  have hFgen : ∀ x, F x ∉ (e (genericPoint X)).asHomogeneousIdeal := fun x =>
    haveI := hne x
    integral_genericPoint_mem_nonempty_open (e ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x))
  have hine : ∀ x, Nonempty (projectivePullbackCoordinateOpen e (i x)) := fun x =>
    ⟨⟨x, hFU x (hxF x)⟩⟩
  choose k₀ hk₀ using fun x =>
    twistedRatio_mem_sections e g hg hggen j₀ A (F x) (hF x) (gx x) (hd x) (hFgen x) (hloc x)
  obtain ⟨B, hB⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x) : Set X))
    (fun x => (e ⁻¹ᵁ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x)).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxF x⟩)
  refine ⟨B.sup (fun x => k₀ x * d x + (d x + 1)), fun N hN => ?_⟩
  have hNx : ∀ x ∈ B, k₀ x * d x + (d x + 1) ≤ N := fun x hx =>
    (Finset.le_sup (f := fun x => k₀ x * d x + (d x + 1)) hx).trans hN
  obtain ⟨r, hr⟩ : ∃ r : X → ℕ, ∀ x ∈ B, k₀ x * d x + (d x + (r x + 1)) = N :=
    ⟨fun x => N - (k₀ x * d x + (d x + 1)), fun x hx => by
      have := hNx x hx
      show k₀ x * d x + (d x + (N - (k₀ x * d x + (d x + 1)) + 1)) = N
      omega⟩
  -- the sections
  let sec : (x : {x // x ∈ B}) → Option (Option (Fin n)) →
      Γ((A + N • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := fun x o =>
    twistedFormSection e g hg hggen j₀ A (F x.val) (hF x.val) (gx x.val) (hr x.val x.property)
      (hk₀ x.val (k₀ x.val) le_rfl) (twistChartForm (i x.val) (F x.val) (d x.val) (r x.val) o)
      (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val) o)
  -- generating open of the chosen section
  have hsecV : ∀ x : {x // x ∈ B}, cartierSectionNonvanishingOpen
      (A + N • projectiveHyperplaneCartier e g hg hggen) (sec x none) =
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x.val) := by
    intro x
    have h1 := twistedFormSection_nonvanishingOpen e g hg hggen j₀ A (F x.val) (hF x.val)
      (gx x.val) (hr x.val x.property) (hk₀ x.val (k₀ x.val) le_rfl) (hd x.val) (hloc x.val)
      (Nat.add_pos_left (hd x.val) _) (MvPolynomial.X (i x.val) ^ (r x.val + 1))
      (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val) none)
    rw [Proj.basicOpen_pow _ _ _ (Nat.succ_pos _)] at h1
    exact h1.trans (inf_eq_left.mpr (hFU x.val))
  have hsecne : ∀ x : {x // x ∈ B}, sec x none ≠ 0 := fun x =>
    (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp (by
      rw [hsecV x]
      exact hne x.val)
  -- chart functions of the forms
  have hchart : ∀ x : {x // x ∈ B},
      projectivePullbackHomogeneousEquation e (i x.val) (d x.val + (r x.val + 1))
        (twistChartForm (i x.val) (F x.val) (d x.val) (r x.val) none)
        (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val) none) =
      projectivePullbackHomogeneousEquation e (i x.val) (d x.val) (F x.val) (hF x.val) := by
    intro x
    rw [projectivePullbackHomogeneousEquation_eq_affine,
      projectivePullbackHomogeneousEquation_eq_affine]
    exact congrArg _ (projectiveDehomogenize_twistChartForm_none (i x.val) (F x.val) (d x.val)
      (r x.val))
  have hchartl : ∀ (x : {x // x ∈ B}) (l : Fin n),
      projectivePullbackHomogeneousEquation e (i x.val) (d x.val + (r x.val + 1))
        (twistChartForm (i x.val) (F x.val) (d x.val) (r x.val) (some (some l)))
        (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val)
          (some (some l))) =
      projectivePullbackHomogeneousEquation e (i x.val) (d x.val) (F x.val) (hF x.val) *
        projectivePullbackHomogeneousEquation e (i x.val) 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l) := by
    intro x l
    rw [projectivePullbackHomogeneousEquation_eq_affine,
      projectivePullbackHomogeneousEquation_eq_affine,
      projectivePullbackHomogeneousEquation_eq_affine]
    exact (congrArg _ (projectiveDehomogenize_twistChartForm_coord (i x.val) (F x.val) (d x.val)
      (r x.val) l)).trans (map_mul _ _ _)
  have hchartinv : ∀ x : {x // x ∈ B},
      projectivePullbackHomogeneousEquation e (i x.val) (d x.val + (r x.val + 1))
        (twistChartForm (i x.val) (F x.val) (d x.val) (r x.val) (some none))
        (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val)
          (some none)) = 1 := by
    intro x
    rw [projectivePullbackHomogeneousEquation_eq_affine]
    exact (congrArg _ (projectiveDehomogenize_twistChartForm_inv (i x.val) (F x.val) (d x.val)
      (r x.val))).trans (map_one _)
  have hΦ0 : ∀ x : {x // x ∈ B}, X.germToFunctionField (projectivePullbackCoordinateOpen e (i x.val))
      (projectivePullbackHomogeneousEquation e (i x.val) (d x.val) (F x.val) (hF x.val)) ≠ 0 := by
    intro x h0
    have := hine x.val
    exact projectivePullbackHomogeneousEquation_ne_zero e (i x.val) (d x.val) (F x.val) (hF x.val)
      (hd x.val) (hFgen x.val)
      (X.germToFunctionField_injective _ (h0.trans (map_zero _).symm))
  -- the family indexed by a finite type
  obtain ⟨eqv⟩ : Nonempty ({x // x ∈ B} × Option (Option (Fin n)) ≃
      Fin (Fintype.card ({x // x ∈ B} × Option (Option (Fin n))))) := ⟨Fintype.equivFin _⟩
  obtain ⟨t, ht⟩ : ∃ t : Fin (Fintype.card ({x // x ∈ B} × Option (Option (Fin n)))) →
      Γ((A + N • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      ∀ x o, t (eqv (x, o)) = sec x o :=
    ⟨fun q => sec (eqv.symm q).1 (eqv.symm q).2, fun x o => by
      simp only [Equiv.symm_apply_apply]⟩
  have hV : ∀ x : {x // x ∈ B}, cartierSectionNonvanishingOpen
      (A + N • projectiveHyperplaneCartier e g hg hggen) (t (eqv (x, none))) =
      e ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x.val) := fun x => by
    rw [ht]
    exact hsecV x
  have htne : ∀ x : {x // x ∈ B}, t (eqv (x, none)) ≠ 0 := fun x => by
    rw [ht]
    exact hsecne x
  have hcover : (⨆ x : {x // x ∈ B}, cartierSectionNonvanishingOpen
      (A + N • projectiveHyperplaneCartier e g hg hggen) (t (eqv (x, none)))) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, hxB, hyx⟩ := Set.mem_iUnion₂.mp (hB (Set.mem_univ y))
    refine Opens.mem_iSup.mpr ⟨⟨x, hxB⟩, ?_⟩
    rw [hV]
    exact hyx
  refine cartierIsVeryAmpleProj_of_sections (A + N • projectiveHyperplaneCartier e g hg hggen) t
    (fun x : {x // x ∈ B} => eqv (x, none)) htne hcover ?_ ?_
  · intro x
    rw [hV]
    exact (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n) K) (F x.val)
      (hF x.val) (hd x.val)).preimage e
  · intro x
    have := hine x.val
    have hratio := fun o => twistedFormSection_ratio e g hg hggen j₀ A (F x.val) (hF x.val)
      (gx x.val) (hr x.val x.property) (hk₀ x.val (k₀ x.val) le_rfl) (hFgen x.val)
      ⟨i x.val, hine x.val⟩
      (twistChartForm (i x.val) (F x.val) (d x.val) (r x.val) none)
      (twistChartForm (i x.val) (F x.val) (d x.val) (r x.val) o)
      (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val) none)
      (twistChartForm_isHomogeneous (i x.val) (F x.val) (d x.val) (r x.val) (hF x.val) o)
    refine eval₂Hom_ratio_surjective_of_chart e he _ t (eqv (x, none)) (htne x) (i x.val)
      (F x.val) (hF x.val) ?_ ?_ ?_
    · rw [hV, projectivePullbackHomogeneousEquation_basicOpen e (i x.val) (d x.val) (F x.val)
        (hF x.val) (hd x.val)]
      exact (inf_eq_right.mpr (hFU x.val)).symm
    · intro l
      refine ⟨eqv (x, some (some l)), ?_⟩
      rw [ht, ht]
      refine (hratio (some (some l))).trans ?_
      rw [hchart, hchartl]
      refine Eq.trans (congrArg _ (map_mul _ _ _)) ?_
      rw [← mul_assoc, inv_mul_cancel₀ (hΦ0 x), one_mul]
    · refine ⟨eqv (x, some none), ?_⟩
      rw [ht, ht]
      refine (hratio (some none)).trans ?_
      rw [hchart, hchartinv, map_one, mul_one]

include he in
/-- A Cartier divisor plus a suitable multiple of the hyperplane divisor is very ample. -/
theorem exists_nsmul_add_cartierIsVeryAmpleProj :
    ∃ N : ℕ, CartierIsVeryAmpleProj K (A + N • projectiveHyperplaneCartier e g hg hggen) := by
  obtain ⟨N₀, h⟩ := eventually_nsmul_add_cartierIsVeryAmpleProj e he g hg hggen A
  exact ⟨N₀, h N₀ le_rfl⟩

end MixedFujita
