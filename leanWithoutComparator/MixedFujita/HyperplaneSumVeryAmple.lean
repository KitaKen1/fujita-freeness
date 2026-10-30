/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AffineOpensInfGeneration
public import MixedFujita.AmpleCoprimeBridgeProof
public import MixedFujita.ProjectivePullbackFixedClass

/-!
The sum of two hyperplane divisors is very ample, and an ample sum is ample (step 4: the Segre
embedding, written through sections).

Let X be an integral scheme with closed immersions e₁, e₂ over a field K into projective spaces
with coordinates x_a and y_b, and hyperplane divisors H₁, H₂. The products x_a y_b of the
coordinate sections are sections of H₁ + H₂. The product x_a y_b generates on U_a ∩ W_b, the
intersection of the charts of x_a and y_b. These opens cover X and are affine, since X is
separated over K. The ratios of the products with denominator x_a y_b include x_l/x_a and y_l/y_b.
These generate the functions on the two charts over K, and the functions on U_a ∩ W_b are generated
by those on U_a and W_b (`affineOpens_res_range_sup_eq_top_of_eq_inf`). So the criterion
`cartierIsVeryAmpleProj_of_sections` applies, and H₁ + H₂ is very ample: X embeds into the
projective space with coordinates z_{ab}.

Very ample divisors are closed under principal shifts, so the sum of two very ample divisors is very
ample. Hence positive combinations Σ c_i H_i of hyperplane divisors are very ample, and an ample
sum (m A ∼ Σ c_i H_i) is ample. For an ample divisor A and a point x, a positive multiple of A is
linearly equivalent to the hyperplane divisor of a closed immersion cut by a coordinate that does
not vanish at x.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- Cancelling a common nonzero right factor in a ratio. -/
theorem ratio_cancel_right {L : Type*} [Field L] (a c b : L) (hb : b ≠ 0) :
    (a * b)⁻¹ * (c * b) = a⁻¹ * c := by
  calc (a * b)⁻¹ * (c * b) = a⁻¹ * c * (b⁻¹ * b) := by rw [mul_inv]; ring
    _ = a⁻¹ * c := by rw [inv_mul_cancel₀ hb, mul_one]

/-- Cancelling a common nonzero left factor in a ratio. -/
theorem ratio_cancel_left {L : Type*} [Field L] (a c b : L) (ha : a ≠ 0) :
    (a * b)⁻¹ * (a * c) = b⁻¹ * c := by
  calc (a * b)⁻¹ * (a * c) = b⁻¹ * c * (a⁻¹ * a) := by rw [mul_inv]; ring
    _ = b⁻¹ * c := by rw [inv_mul_cancel₀ ha, mul_one]

section Coordinates

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  (e : X ⟶ polynomialProjectiveScheme n K)
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal)
  (j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)})

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- The section of the hyperplane divisor given by the coordinate x_a generates exactly on the
chart of x_a. -/
theorem projectiveCoordinateSection_nonvanishingOpen (a : Fin n) :
    cartierSectionNonvanishingOpen (1 • projectiveHyperplaneCartier e g hg hggen)
        (projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X a)
          (MvPolynomial.isHomogeneous_X K a)) =
      projectivePullbackCoordinateOpen e a :=
  projectiveFormSection_nonvanishingOpen e g hg hggen j₀ Nat.one_pos _ _

/-- The ratio of the coordinate sections x_l and x_a is the affine coordinate x_l/x_a on the chart
of x_a. -/
theorem projectiveCoordinateSection_ratio (a : Fin n)
    [Nonempty (projectivePullbackCoordinateOpen e a)] (l : Fin n) :
    (cartierSectionRational (1 • projectiveHyperplaneCartier e g hg hggen)
        (projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X a)
          (MvPolynomial.isHomogeneous_X K a)))⁻¹ *
      cartierSectionRational (1 • projectiveHyperplaneCartier e g hg hggen)
        (projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)) =
      X.germToFunctionField (projectivePullbackCoordinateOpen e a)
        (projectivePullbackHomogeneousEquation e a 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)) := by
  have hself : projectivePullbackHomogeneousEquation e a 1 (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X K a) = 1 := by
    rw [projectivePullbackHomogeneousEquation_eq_affine, projectiveDehomogenize_X_self, map_one]
  rw [projectiveFormSection_rational, projectiveFormSection_rational,
    projectiveFormRatio_chart_independent e g hg hggen j₀ ⟨a, inferInstance⟩,
    projectiveFormRatio_chart_independent e g hg hggen j₀ ⟨a, inferInstance⟩]
  unfold projectiveFormRatio
  rw [hself, map_one, one_mul]
  have hu : (((projectiveHyperplaneUnit e g hg hggen ⟨a, inferInstance⟩)⁻¹ ^ 1 :
      X.functionFieldˣ) : X.functionField) ≠ 0 := Units.ne_zero _
  rw [inv_mul_eq_iff_eq_mul₀ hu, mul_comm]

/-- The coordinate sections of the hyperplane divisor of a morphism to projective space: the
section of x_a generates exactly on the chart of x_a, and the ratio of the sections of x_l and x_a
is the affine coordinate x_l/x_a there. -/
theorem exists_projectiveCoordinateSections :
    ∃ s : Fin n → Γ((1 • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      (∀ a, cartierSectionNonvanishingOpen (1 • projectiveHyperplaneCartier e g hg hggen) (s a) =
        projectivePullbackCoordinateOpen e a) ∧
      ∀ (a : Fin n) [Nonempty (projectivePullbackCoordinateOpen e a)] (l : Fin n),
        (cartierSectionRational (1 • projectiveHyperplaneCartier e g hg hggen) (s a))⁻¹ *
            cartierSectionRational (1 • projectiveHyperplaneCartier e g hg hggen) (s l) =
          X.germToFunctionField (projectivePullbackCoordinateOpen e a)
            (projectivePullbackHomogeneousEquation e a 1 (MvPolynomial.X l)
              (MvPolynomial.isHomogeneous_X K l)) := by
  obtain ⟨jg, hjg⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint X))
  let j₀ : {k : Fin n // Nonempty (projectivePullbackCoordinateOpen e k)} :=
    ⟨jg, ⟨⟨genericPoint X, hjg⟩⟩⟩
  exact ⟨fun a => projectiveFormSection e g hg hggen j₀ 1 (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X K a),
    fun a => projectiveCoordinateSection_nonvanishingOpen e g hg hggen j₀ a,
    fun a _ l => projectiveCoordinateSection_ratio e g hg hggen j₀ a l⟩

end Coordinates

section Chart

variable {K : Type u} [Field K] {n : ℕ} {X : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] (e : X ⟶ polynomialProjectiveScheme n K)

/-- On an open V inside the chart of x_i, a subring of the functions on V containing the constants
and the restrictions of the affine coordinates contains the restrictions of all functions on the
chart. -/
theorem projectiveChart_restrict_mem_of_coordinates [IsClosedImmersion e]
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K)) (i : Fin n)
    {V : X.Opens} [Nonempty V] (hVU : V ≤ projectivePullbackCoordinateOpen e i)
    (S : Subring Γ(X, V))
    (hC : ∀ c : K, X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (schemeBaseScalars K X c) ∈ S)
    (hX : ∀ l : Fin n, X.presheaf.map (homOfLE hVU).op
      (projectivePullbackHomogeneousEquation e i 1 (MvPolynomial.X l)
        (MvPolynomial.isHomogeneous_X K l)) ∈ S)
    (r : Γ(X, projectivePullbackCoordinateOpen e i)) :
    X.presheaf.map (homOfLE hVU).op r ∈ S := by
  have hUne : Nonempty (projectivePullbackCoordinateOpen e i) := by
    obtain ⟨⟨y, hy⟩⟩ := (inferInstance : Nonempty V)
    exact ⟨⟨y, hVU hy⟩⟩
  have htop : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  obtain ⟨p, rfl⟩ := projectivePullbackAffinePolynomialMap_surjective e i r
  induction p using MvPolynomial.induction_on with
  | C c =>
    have heq : X.presheaf.map (homOfLE hVU).op
        (projectivePullbackAffinePolynomialMap e i (MvPolynomial.C c)) =
        X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (schemeBaseScalars K X c) := by
      apply X.germToFunctionField_injective V
      rw [germToFunctionField_restrict X hVU, projectivePullbackAffinePolynomialMap_C e he i c,
        germToFunctionField_restrict X (le_top : projectivePullbackCoordinateOpen e i ≤ ⊤),
        germToFunctionField_restrict X (le_top : V ≤ ⊤), schemeBaseScalars_apply]
    rw [heq]
    exact hC c
  | add p q hp hq =>
    rw [map_add, map_add]
    exact S.add_mem hp hq
  | mul_X p l hp =>
    rw [map_mul, map_mul]
    refine S.mul_mem hp ?_
    have hl : projectivePullbackAffinePolynomialMap e i (MvPolynomial.X l) =
        projectivePullbackHomogeneousEquation e i 1 (MvPolynomial.X l.val)
          (MvPolynomial.isHomogeneous_X K l.val) := by
      rw [projectivePullbackHomogeneousEquation_eq_affine, projectiveDehomogenize_X_other]
    rw [hl]
    exact hX l.val

end Chart

section Segre

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower

/-- Generation of the functions on the generating open of a section t₀ by the ratios with
denominator t₀, when this open is the intersection of a chart of x_{i₁} for e₁ and a chart of
y_{i₂} for e₂, and the affine coordinates of both charts are among the ratios. -/
theorem eval₂Hom_ratio_surjective_of_inf_charts (D : CartierDivisor X) {M : ℕ}
    (t : Fin M → Γ(D.sheaf, ⊤)) (q₀ : Fin M) (h₀ : t q₀ ≠ 0) {n₁ n₂ : ℕ}
    (e₁ : X ⟶ polynomialProjectiveScheme n₁ K) [IsClosedImmersion e₁]
    (he₁ : e₁ ≫ polynomialProjectiveToBase n₁ K = X ↘ Spec (CommRingCat.of K))
    (e₂ : X ⟶ polynomialProjectiveScheme n₂ K) [IsClosedImmersion e₂]
    (he₂ : e₂ ≫ polynomialProjectiveToBase n₂ K = X ↘ Spec (CommRingCat.of K))
    (i₁ : Fin n₁) (i₂ : Fin n₂) [Nonempty (projectivePullbackCoordinateOpen e₁ i₁)]
    [Nonempty (projectivePullbackCoordinateOpen e₂ i₂)]
    (hV : cartierSectionNonvanishingOpen D (t q₀) =
      projectivePullbackCoordinateOpen e₁ i₁ ⊓ projectivePullbackCoordinateOpen e₂ i₂)
    (hcoord₁ : ∀ l : Fin n₁, ∃ q, (cartierSectionRational D (t q₀))⁻¹ *
        cartierSectionRational D (t q) =
      X.germToFunctionField (projectivePullbackCoordinateOpen e₁ i₁)
        (projectivePullbackHomogeneousEquation e₁ i₁ 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)))
    (hcoord₂ : ∀ l : Fin n₂, ∃ q, (cartierSectionRational D (t q₀))⁻¹ *
        cartierSectionRational D (t q) =
      X.germToFunctionField (projectivePullbackCoordinateOpen e₂ i₂)
        (projectivePullbackHomogeneousEquation e₂ i₂ 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l))) :
    Function.Surjective (MvPolynomial.eval₂Hom
      ((X.presheaf.map (homOfLE (le_top :
        cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
      (fun q => cartierSectionRatio D (t q₀) h₀ (t q))) := by
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← he₁]
    have := polynomialProjectiveToBase_isProper n₁ K
    infer_instance
  have hVne : Nonempty (cartierSectionNonvanishingOpen D (t q₀)) :=
    (cartierSectionNonvanishingOpen_nonempty_iff D (t q₀)).mpr h₀
  have hU₁ : IsAffineOpen (projectivePullbackCoordinateOpen e₁ i₁) :=
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n₁) K)
      (MvPolynomial.X i₁) (MvPolynomial.isHomogeneous_X K i₁) Nat.zero_lt_one).preimage e₁
  have hU₂ : IsAffineOpen (projectivePullbackCoordinateOpen e₂ i₂) :=
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n₂) K)
      (MvPolynomial.X i₂) (MvPolynomial.isHomogeneous_X K i₂) Nat.zero_lt_one).preimage e₂
  have hV₁ : cartierSectionNonvanishingOpen D (t q₀) ≤ projectivePullbackCoordinateOpen e₁ i₁ :=
    hV.le.trans inf_le_left
  have hV₂ : cartierSectionNonvanishingOpen D (t q₀) ≤ projectivePullbackCoordinateOpen e₂ i₂ :=
    hV.le.trans inf_le_right
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : MvPolynomial (Fin M) K →+* Γ(X, cartierSectionNonvanishingOpen D (t q₀)),
      Φ = MvPolynomial.eval₂Hom
        ((X.presheaf.map (homOfLE (le_top :
          cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤)).op).hom.comp (schemeBaseScalars K X))
        (fun q => cartierSectionRatio D (t q₀) h₀ (t q)) := ⟨_, rfl⟩
  rw [← hΦ]
  have hX : ∀ q, cartierSectionRatio D (t q₀) h₀ (t q) ∈ Φ.range := fun q =>
    ⟨MvPolynomial.X q, by rw [hΦ, MvPolynomial.eval₂Hom_X']⟩
  have hC : ∀ c : K, X.presheaf.map (homOfLE (le_top :
      cartierSectionNonvanishingOpen D (t q₀) ≤ ⊤)).op (schemeBaseScalars K X c) ∈ Φ.range :=
    fun c => ⟨MvPolynomial.C c, by rw [hΦ, MvPolynomial.eval₂Hom_C]; rfl⟩
  -- the affine coordinates of the two charts are ratios
  have hcoordS₁ : ∀ l : Fin n₁, X.presheaf.map (homOfLE hV₁).op
      (projectivePullbackHomogeneousEquation e₁ i₁ 1 (MvPolynomial.X l)
        (MvPolynomial.isHomogeneous_X K l)) ∈ Φ.range := by
    intro l
    obtain ⟨q, hq⟩ := hcoord₁ l
    have heq : X.presheaf.map (homOfLE hV₁).op
        (projectivePullbackHomogeneousEquation e₁ i₁ 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)) = cartierSectionRatio D (t q₀) h₀ (t q) := by
      apply X.germToFunctionField_injective (cartierSectionNonvanishingOpen D (t q₀))
      rw [germToFunctionField_restrict X hV₁, cartierSectionRatio_germToFunctionField, hq]
    rw [heq]
    exact hX q
  have hcoordS₂ : ∀ l : Fin n₂, X.presheaf.map (homOfLE hV₂).op
      (projectivePullbackHomogeneousEquation e₂ i₂ 1 (MvPolynomial.X l)
        (MvPolynomial.isHomogeneous_X K l)) ∈ Φ.range := by
    intro l
    obtain ⟨q, hq⟩ := hcoord₂ l
    have heq : X.presheaf.map (homOfLE hV₂).op
        (projectivePullbackHomogeneousEquation e₂ i₂ 1 (MvPolynomial.X l)
          (MvPolynomial.isHomogeneous_X K l)) = cartierSectionRatio D (t q₀) h₀ (t q) := by
      apply X.germToFunctionField_injective (cartierSectionNonvanishingOpen D (t q₀))
      rw [germToFunctionField_restrict X hV₂, cartierSectionRatio_germToFunctionField, hq]
    rw [heq]
    exact hX q
  -- all functions of the two charts, and then all functions on the intersection
  have hres₁ := projectiveChart_restrict_mem_of_coordinates e₁ he₁ i₁ hV₁ Φ.range hC hcoordS₁
  have hres₂ := projectiveChart_restrict_mem_of_coordinates e₂ he₂ i₂ hV₂ Φ.range hC hcoordS₂
  have hgen := affineOpens_res_range_sup_eq_top_of_eq_inf (X ↘ Spec (CommRingCat.of K)) hU₁ hU₂
    hV hV₁ hV₂
  intro ξ
  have hξ : ξ ∈ (⊤ : Subring Γ(X, cartierSectionNonvanishingOpen D (t q₀))) := Subring.mem_top ξ
  rw [← hgen] at hξ
  have hle : (X.presheaf.map (homOfLE hV₁).op).hom.range ⊔
      (X.presheaf.map (homOfLE hV₂).op).hom.range ≤ Φ.range := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hy
      exact hres₁ r
    · intro y hy
      obtain ⟨r, rfl⟩ := RingHom.mem_range.mp hy
      exact hres₂ r
  exact RingHom.mem_range.mp (hle hξ)

/-- The sum of the hyperplane divisors of two closed immersions over K into projective spaces is
very ample (the Segre embedding). -/
theorem projectiveHyperplane_add_cartierIsVeryAmpleProj {n₁ n₂ : ℕ}
    (e₁ : X ⟶ polynomialProjectiveScheme n₁ K) [IsClosedImmersion e₁]
    (he₁ : e₁ ≫ polynomialProjectiveToBase n₁ K = X ↘ Spec (CommRingCat.of K))
    (g₁ : MvPolynomial (Fin n₁) K) (hg₁ : g₁.IsHomogeneous 1)
    (hggen₁ : g₁ ∉ (e₁ (genericPoint X)).asHomogeneousIdeal)
    (e₂ : X ⟶ polynomialProjectiveScheme n₂ K) [IsClosedImmersion e₂]
    (he₂ : e₂ ≫ polynomialProjectiveToBase n₂ K = X ↘ Spec (CommRingCat.of K))
    (g₂ : MvPolynomial (Fin n₂) K) (hg₂ : g₂.IsHomogeneous 1)
    (hggen₂ : g₂ ∉ (e₂ (genericPoint X)).asHomogeneousIdeal) :
    CartierIsVeryAmpleProj K (projectiveHyperplaneCartier e₁ g₁ hg₁ hggen₁ +
      projectiveHyperplaneCartier e₂ g₂ hg₂ hggen₂) := by
  have hproper : IsProper (X ↘ Spec (CommRingCat.of K)) := by
    rw [← he₁]
    have := polynomialProjectiveToBase_isProper n₁ K
    infer_instance
  obtain ⟨s₁, hs₁V, hs₁R⟩ := exists_projectiveCoordinateSections e₁ g₁ hg₁ hggen₁
  obtain ⟨s₂, hs₂V, hs₂R⟩ := exists_projectiveCoordinateSections e₂ g₂ hg₂ hggen₂
  -- the products of the coordinate sections
  obtain ⟨t, ht⟩ : ∃ t : Fin (n₁ * n₂) → Γ((1 • projectiveHyperplaneCartier e₁ g₁ hg₁ hggen₁ +
      1 • projectiveHyperplaneCartier e₂ g₂ hg₂ hggen₂).sheaf, ⊤),
      ∀ a b, t (finProdFinEquiv (a, b)) = cartierSectionProduct _ _ (s₁ a) (s₂ b) :=
    ⟨fun q => cartierSectionProduct _ _ (s₁ (finProdFinEquiv.symm q).1)
      (s₂ (finProdFinEquiv.symm q).2), fun a b => by simp only [Equiv.symm_apply_apply]⟩
  have htV : ∀ a b, cartierSectionNonvanishingOpen _ (t (finProdFinEquiv (a, b))) =
      projectivePullbackCoordinateOpen e₁ a ⊓ projectivePullbackCoordinateOpen e₂ b := by
    intro a b
    rw [ht, cartierSectionNonvanishingOpen_product, hs₁V, hs₂V]
  -- every point lies in the generating open of a product
  have hpt : ∀ x : X, ∃ a b, x ∈ projectivePullbackCoordinateOpen e₁ a ⊓
      projectivePullbackCoordinateOpen e₂ b := by
    intro x
    obtain ⟨a, ha⟩ := polynomialProjective_exists_coordinate_chart n₁ K (e₁ x)
    obtain ⟨b, hb⟩ := polynomialProjective_exists_coordinate_chart n₂ K (e₂ x)
    exact ⟨a, b, ha, hb⟩
  choose a b hab using hpt
  have hne : ∀ x, t (finProdFinEquiv (a x, b x)) ≠ 0 := by
    intro x
    apply (cartierSectionNonvanishingOpen_nonempty_iff _ _).mp
    rw [htV]
    exact ⟨⟨x, hab x⟩⟩
  have hcover : (⨆ x, cartierSectionNonvanishingOpen _ (t (finProdFinEquiv (a x, b x)))) = ⊤ := by
    apply top_unique
    intro x _
    refine Opens.mem_iSup.mpr ⟨x, ?_⟩
    rw [htV]
    exact hab x
  have key : CartierIsVeryAmpleProj K (1 • projectiveHyperplaneCartier e₁ g₁ hg₁ hggen₁ +
      1 • projectiveHyperplaneCartier e₂ g₂ hg₂ hggen₂) := by
    refine cartierIsVeryAmpleProj_of_sections _ t (fun x => finProdFinEquiv (a x, b x)) hne
      hcover ?_ ?_
    · intro x
      rw [htV]
      exact isAffineOpen_inf_of_isSeparated (X ↘ Spec (CommRingCat.of K))
        ((Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n₁) K)
          (MvPolynomial.X (a x)) (MvPolynomial.isHomogeneous_X K (a x)) Nat.zero_lt_one).preimage
            e₁)
        ((Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin n₂) K)
          (MvPolynomial.X (b x)) (MvPolynomial.isHomogeneous_X K (b x)) Nat.zero_lt_one).preimage
            e₂)
    · intro x
      have hUa : Nonempty (projectivePullbackCoordinateOpen e₁ (a x)) := ⟨⟨x, (hab x).1⟩⟩
      have hUb : Nonempty (projectivePullbackCoordinateOpen e₂ (b x)) := ⟨⟨x, (hab x).2⟩⟩
      have hr : cartierSectionRational _ (t (finProdFinEquiv (a x, b x))) ≠ 0 :=
        (map_ne_zero_iff _ (cartierSectionRational_injective _)).mpr (hne x)
      rw [ht, cartierSectionProduct_rational] at hr
      obtain ⟨hr₁, hr₂⟩ := mul_ne_zero_iff.mp hr
      refine eval₂Hom_ratio_surjective_of_inf_charts _ t _ (hne x) e₁ he₁ e₂ he₂ (a x) (b x)
        (htV _ _) ?_ ?_
      · intro l
        refine ⟨finProdFinEquiv (l, b x), ?_⟩
        rw [ht, ht, cartierSectionProduct_rational, cartierSectionProduct_rational,
          ratio_cancel_right _ _ _ hr₂]
        exact hs₁R (a x) l
      · intro l
        refine ⟨finProdFinEquiv (a x, l), ?_⟩
        rw [ht, ht, cartierSectionProduct_rational, cartierSectionProduct_rational,
          ratio_cancel_left _ _ _ hr₁]
        exact hs₂R (b x) l
  simpa only [one_nsmul] using key

/-- The hyperplane divisor of a closed immersion over K into projective space is very ample. -/
theorem projectiveHyperplane_cartierIsVeryAmpleProj {n : ℕ}
    (e : X ⟶ polynomialProjectiveScheme n K) (hci : IsClosedImmersion e)
    (he : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))
    (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
    (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal) :
    CartierIsVeryAmpleProj K (projectiveHyperplaneCartier e g hg hggen) :=
  ⟨n, e, hci, he, g, hg, hggen, 1, by rw [principalCartierDivisor_one, add_zero]⟩

/-- The sum of two very ample divisors is very ample. -/
theorem cartierIsVeryAmpleProj_add {A₁ A₂ : CartierDivisor X} (h₁ : CartierIsVeryAmpleProj K A₁)
    (h₂ : CartierIsVeryAmpleProj K A₂) : CartierIsVeryAmpleProj K (A₁ + A₂) := by
  obtain ⟨n₁, e₁, hci₁, he₁, g₁, hg₁, hggen₁, f₁, hA₁⟩ := h₁
  obtain ⟨n₂, e₂, hci₂, he₂, g₂, hg₂, hggen₂, f₂, hA₂⟩ := h₂
  have h := cartierIsVeryAmpleProj_add_principal
    (projectiveHyperplane_add_cartierIsVeryAmpleProj e₁ he₁ g₁ hg₁ hggen₁ e₂ he₂ g₂ hg₂ hggen₂)
    (f₁ * f₂)
  rw [hA₁, hA₂]
  convert h using 1
  rw [principalCartierDivisor_mul]
  abel

/-- A positive multiple of a very ample divisor is very ample. -/
theorem cartierIsVeryAmpleProj_nsmul {A : CartierDivisor X} (h : CartierIsVeryAmpleProj K A)
    {c : ℕ} (hc : 1 ≤ c) : CartierIsVeryAmpleProj K (c • A) := by
  induction c, hc using Nat.le_induction with
  | base => rwa [one_nsmul]
  | succ c _ ih =>
    rw [succ_nsmul]
    exact cartierIsVeryAmpleProj_add ih h

/-- A sum of finitely many, at least one, very ample divisors is very ample. -/
theorem cartierIsVeryAmpleProj_sum {s : ℕ} (hs : 1 ≤ s) (A : Fin s → CartierDivisor X)
    (h : ∀ i, CartierIsVeryAmpleProj K (A i)) : CartierIsVeryAmpleProj K (∑ i, A i) := by
  induction s, hs using Nat.le_induction with
  | base =>
    rw [Fin.sum_univ_one]
    exact h 0
  | succ s _ ih =>
    rw [Fin.sum_univ_castSucc]
    exact cartierIsVeryAmpleProj_add (ih (fun i => A i.castSucc) (fun i => h i.castSucc))
      (h (Fin.last s))

/-- An ample sum is ample: a positive combination of hyperplane divisors of finitely many closed
immersions is very ample. -/
theorem cartierIsAmpleProj_of_isAmpleSum {A : CartierDivisor X} (h : CartierIsAmpleSum K A) :
    CartierIsAmpleProj K A := by
  obtain ⟨m, hm, s, hs, N, e, hci, he, g, hg, hggen, c, hc, f, hmA⟩ := h
  have hJ : CartierIsVeryAmpleProj K
      (∑ i, c i • projectiveHyperplaneCartier (e i) (g i) (hg i) (hggen i)) :=
    cartierIsVeryAmpleProj_sum hs _ fun i => cartierIsVeryAmpleProj_nsmul
      (projectiveHyperplane_cartierIsVeryAmpleProj (e i) (hci i) (he i) (g i) (hg i) (hggen i))
      (hc i)
  obtain ⟨n, e', hci', he', g', hg', hggen', f', hJ'⟩ := hJ
  exact ⟨m, hm, n, e', hci', he', g', hg', hggen', f' * f, by
    rw [hmA, hJ', principalCartierDivisor_mul, add_assoc]⟩

/-- For an ample divisor A and a point x, a positive multiple of A is linearly equivalent to the
hyperplane divisor of a closed immersion over K cut by a coordinate that does not vanish at x. -/
theorem cartierIsAmpleProj_exists_hyperplane_nonvanishing {A : CartierDivisor X}
    (hA : CartierIsAmpleProj K A) (x : X) :
    ∃ (l : ℕ) (_ : 1 ≤ l) (n : ℕ) (e : X ⟶ polynomialProjectiveScheme n K)
      (_ : IsClosedImmersion e)
      (_ : e ≫ polynomialProjectiveToBase n K = X ↘ Spec (CommRingCat.of K))
      (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
      (hggen : g ∉ (e (genericPoint X)).asHomogeneousIdeal) (_ : g ∉ (e x).asHomogeneousIdeal)
      (φ : X.functionFieldˣ),
      l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor X φ := by
  obtain ⟨m, hm, n, e, hci, he, g, hg, hggen, f, hmA⟩ := hA
  obtain ⟨i, hi⟩ := polynomialProjective_exists_coordinate_chart n K (e x)
  have hne : Nonempty (projectivePullbackCoordinateOpen e i) := ⟨⟨x, hi⟩⟩
  have hgen : MvPolynomial.X i ∉ (e (genericPoint X)).asHomogeneousIdeal :=
    integral_genericPoint_mem_nonempty_open (projectivePullbackCoordinateOpen e i)
  have hshift : projectiveHyperplaneCartier e g hg hggen =
      projectiveHyperplaneCartier e (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) hgen +
        principalCartierDivisor X (projectivePullbackHomogeneousRatio e ⟨i, hne⟩ 1 g hg
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X K i) Nat.one_pos hggen hgen) :=
    projectivePullbackHomogeneousCartier_eq_principalShift e ⟨i, hne⟩ 1 g hg (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X K i) Nat.one_pos hggen hgen
  refine ⟨m, hm, n, e, hci, he, MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i, hgen, hi,
    projectivePullbackHomogeneousRatio e ⟨i, hne⟩ 1 g hg (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X K i) Nat.one_pos hggen hgen * f, ?_⟩
  rw [hmA, hshift, principalCartierDivisor_mul, add_assoc]

end Segre

end MixedFujita
