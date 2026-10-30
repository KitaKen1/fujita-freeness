/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ChartwiseSNCAtlas
public import MixedFujita.CocycleCartierDivisor
public import MixedFujita.CartierSectionDivisor

/-!
Simple normal crossing atlases trivializing a Cartier divisor, and its normalization by a cocycle
(step 10, R4-3).

* `exists_isSNCChart_basicOpen_isLocalEquationAt_of_mem_chart`: refining check 531, every point of
  a standard chart lies in a simple normal crossing chart, basic in that chart, on which a given
  Cartier divisor `D` has a single local equation (a local equation at a point is one on a
  neighbourhood, by TauCeti's definition).
* `exists_finite_snc_chart_span_isLocalEquationAt`: finitely many of these charts cover the
  standard chart; their defining functions span its unit ideal.
* `exists_unit_germ_eq_of_isLocalEquationAt`: on a nonempty open `U` of an integral scheme, two
  local equations `g, g'` of `D` differ by a unit of `Γ(X, U)` (at each stalk they differ by a unit,
  and TauCeti's `exists_germToFunctionField_eq_of_forall_mem_range` gives sections).
* `isCocycleZero_of_germ`: transition units with germs `g_i g_j⁻¹` form a cocycle (check 529).
* `isLocalEquationAt_shift_cocycleEquation`: the shift `D − div(g_0)` has the local equations
  `w_{i0}` of check 529 (`cocycleEquation`); its sheaf is that of `D`
  (`cartierSheafPrincipalShiftIso`).

On `T_K` this replaces `Q` by the divisor with local equations `w_{i0}`, whose transition units
spread to the closure `T_A` (check 533) and give `Q_A` and `Q_κ` (check 529).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

section Atlas

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {d n : ℕ} (e : X ⟶ polynomialProjectiveScheme n K) {r : ℕ} {ξ : Fin r → X}

/-- **A simple normal crossing chart through a point of a standard chart, basic in that chart, on
which a Cartier divisor has one local equation.** -/
theorem exists_isSNCChart_basicOpen_isLocalEquationAt_of_mem_chart [IsClosedImmersion e]
    (hsnc : IsSNCFamily K d ξ) (D : CartierDivisor X) (k : Fin n) (x : X)
    (hx : x ∈ projectivePullbackCoordinateOpen e k) :
    ∃ (c : EtaleChart K X d) (σ : Fin r → Option (Fin d))
      (s : Γ(X, projectivePullbackCoordinateOpen e k)) (g : X.functionFieldˣ),
      x ∈ c.U ∧ IsSNCChart c ξ σ ∧ c.U = X.basicOpen s ∧ ∀ y ∈ c.U, D.IsLocalEquationAt y g := by
  obtain ⟨c₀, σ, hx₀, hc₀⟩ := hsnc x
  obtain ⟨g, hg⟩ := D.exists_isLocalEquationAt x
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hg
  obtain ⟨t₀, ht₀W, hxt₀⟩ := c₀.isAffine.exists_basicOpen_le ⟨x, hxW⟩ hx₀
  let c₁ := etaleChartBasicOpen c₀ t₀ ⟨⟨x, hxt₀⟩⟩
  have hc₁ : IsSNCChart c₁ ξ σ := isSNCChart_basicOpen hc₀ t₀ ⟨⟨x, hxt₀⟩⟩
  obtain ⟨t, s, hts, hxt⟩ := exists_basicOpen_le_affine_inter c₁.isAffine
    (projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion e k) x ⟨hxt₀, hx⟩
  refine ⟨etaleChartBasicOpen c₁ t ⟨⟨x, hxt⟩⟩, σ, s, g, hxt,
    isSNCChart_basicOpen hc₁ t ⟨⟨x, hxt⟩⟩, hts, fun y hy => ?_⟩
  have hyW : y ∈ W := ht₀W (X.basicOpen_le t hy)
  exact CartierDivisor.isLocalEquationAt_iff.mpr ⟨W, hyW, hW⟩

/-- **Finitely many simple normal crossing charts, basic in a standard chart and trivializing a
Cartier divisor, cover the standard chart**: their defining functions span the unit ideal. -/
theorem exists_finite_snc_chart_span_isLocalEquationAt [IsClosedImmersion e]
    (hsnc : IsSNCFamily K d ξ) (D : CartierDivisor X) (k : Fin n) :
    ∃ (m : ℕ) (c : Fin m → EtaleChart K X d) (σ : Fin m → Fin r → Option (Fin d))
      (s : Fin m → Γ(X, projectivePullbackCoordinateOpen e k)) (g : Fin m → X.functionFieldˣ),
      (∀ j, IsSNCChart (c j) ξ (σ j)) ∧ (∀ j, (c j).U = X.basicOpen (s j)) ∧
        Ideal.span (Set.range s) = ⊤ ∧ ∀ j, ∀ y ∈ (c j).U, D.IsLocalEquationAt y (g j) := by
  classical
  let V := projectivePullbackCoordinateOpen e k
  have hV : IsAffineOpen V := projectivePullbackCoordinateOpen_isAffineOpen_of_isClosedImmersion e k
  choose c σ s g hxc hc hU hg using fun x : V =>
    exists_isSNCChart_basicOpen_isLocalEquationAt_of_mem_chart e hsnc D k x x.2
  -- the basic opens cover the chart
  have hcov : ⨆ f : Set.range s, X.basicOpen (f : Γ(X, V)) = V := by
    apply le_antisymm
    · exact iSup_le fun f => X.basicOpen_le _
    · intro z hz
      rw [Opens.mem_iSup]
      refine ⟨⟨s ⟨z, hz⟩, ⟨_, rfl⟩⟩, ?_⟩
      have := hxc ⟨z, hz⟩
      rw [hU] at this
      exact this
  have hspan : Ideal.span (Set.range s) = ⊤ := (hV.iSup_basicOpen_eq_self_iff).1 hcov
  -- a finite subfamily spans
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite (Set.range s)).1 hspan
  choose w hw using fun f : t => hts f.2
  let f : Fin t.card → V := fun j => w (t.equivFin.symm j)
  refine ⟨t.card, fun j => c (f j), fun j => σ (f j), fun j => s (f j), fun j => g (f j),
    fun j => hc (f j), fun j => hU (f j), ?_, fun j => hg (f j)⟩
  rw [eq_top_iff, ← ht, Ideal.span_le]
  intro a ha
  apply Ideal.subset_span
  refine ⟨t.equivFin ⟨a, ha⟩, ?_⟩
  simp only [f, Equiv.symm_apply_apply]
  exact hw ⟨a, ha⟩

end Atlas

section Transition

variable {X : Scheme.{u}} [IsIntegral X]

/-- **Two local equations of a Cartier divisor on an open differ by a unit of its functions.** -/
theorem exists_unit_germ_eq_of_isLocalEquationAt {D : CartierDivisor X} {U : X.Opens} [Nonempty U]
    {g g' : X.functionFieldˣ} (hg : ∀ y ∈ U, D.IsLocalEquationAt y g)
    (hg' : ∀ y ∈ U, D.IsLocalEquationAt y g') :
    ∃ w : Γ(X, U)ˣ, X.germToFunctionField U (w : Γ(X, U)) =
      ((g * g'⁻¹ : X.functionFieldˣ) : X.functionField) := by
  have hmem : ∀ a b : X.functionFieldˣ, (∀ y ∈ U, D.IsLocalEquationAt y a) →
      (∀ y ∈ U, D.IsLocalEquationAt y b) → ∀ y ∈ U,
        ((a * b⁻¹ : X.functionFieldˣ) : X.functionField) ∈
          (algebraMap (X.presheaf.stalk y) X.functionField).range := by
    intro a b ha hb y hy
    obtain ⟨v, hv⟩ := (ha y hy).exists_unit_mul_eq (hb y hy)
    refine ⟨v, ?_⟩
    rw [Units.val_mul, ← hv, mul_assoc, Units.val_inv_eq_inv_val,
      mul_inv_cancel₀ b.ne_zero, mul_one]
  obtain ⟨a, ha⟩ := exists_germToFunctionField_eq_of_forall_mem_range (hmem g g' hg hg')
  obtain ⟨b, hb⟩ := exists_germToFunctionField_eq_of_forall_mem_range (hmem g' g hg' hg)
  have hab : a * b = 1 := by
    apply Scheme.germToFunctionField_injective X U
    rw [map_mul, ha, hb, map_one, ← Units.val_mul]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  exact ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, ha⟩

variable {N : ℕ} (U : Fin (N + 1) → X.Opens) [∀ i, Nonempty (U i)]

/-- **Transition units of local equations form a cocycle.** -/
theorem isCocycleZero_of_germ (g : Fin (N + 1) → X.functionFieldˣ) (w : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (hw : ∀ i j, letI := integral_opens_inter_nonempty X (U i) (U j)
      X.germToFunctionField (U i ⊓ U j) (w i j : Γ(X, U i ⊓ U j)) =
        ((g i * (g j)⁻¹ : X.functionFieldˣ) : X.functionField)) :
    IsCocycleZero U w := by
  intro i j
  let _ := integral_opens_inter_nonempty X (U i) (U j)
  let _ := integral_opens_inter_nonempty X (U i) (U 0)
  let _ := integral_opens_inter_nonempty X (U j) (U 0)
  let _ := integral_opens_inter_nonempty X (U i ⊓ U j) (U 0)
  apply Scheme.germToFunctionField_injective X (U i ⊓ U j ⊓ U 0)
  rw [map_mul, germToFunctionField_restrict, germToFunctionField_restrict,
    germToFunctionField_restrict, hw, hw, hw, ← Units.val_mul]
  congr 1
  group

/-- **The shift `D − div(g_0)` has the cocycle local equations `w_{i0}`.** -/
theorem isLocalEquationAt_shift_cocycleEquation {D : CartierDivisor X}
    (g : Fin (N + 1) → X.functionFieldˣ) (hg : ∀ i, ∀ y ∈ U i, D.IsLocalEquationAt y (g i))
    (w : ∀ i j, Γ(X, U i ⊓ U j)ˣ)
    (hw : ∀ i j, letI := integral_opens_inter_nonempty X (U i) (U j)
      X.germToFunctionField (U i ⊓ U j) (w i j : Γ(X, U i ⊓ U j)) =
        ((g i * (g j)⁻¹ : X.functionFieldˣ) : X.functionField))
    (i : Fin (N + 1)) :
    ∀ y ∈ U i, (D + principalCartierDivisor X (g 0)⁻¹).IsLocalEquationAt y
      (cocycleEquation U w i) := by
  intro y hy
  have h1 := (hg i y hy).mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor y (g 0)⁻¹)
  have h2 : cocycleEquation U w i = g i * (g 0)⁻¹ := Units.ext (hw i 0)
  rw [h2]
  exact h1

end Transition

end MixedFujita
