/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.KltMinimizerDataShift
public import MixedFujita.ProjectiveHyperplaneMinimizerStrict

/-!
The data of the minimizer for a divisor A whose multiple l A is linearly equivalent to the
hyperplane class J of a closed immersion, from the hypotheses of S-NF for A (steps 11 and 14).

* The restriction of sections to the closure of a point does not change under the principal
  shift: multiplication by g identifies the sections of D + div g with those of D, and a section
  vanishes at η exactly when its shift does (the local coefficients agree for the matching local
  equations). So the restricted dimensions of corresponding subspaces agree.
* If l A = L + div φ, the numerical hypothesis for A with constant c, at the degrees l j, gives the
  numerical hypothesis for L with constant l^d c: the sections of (l j) A are the principal
  shifts of the sections of j L.
* For the hyperplane class J with l A = J + div φ: the numerical hypothesis for A (constant
  (m + 1)^d) gives that for J with s = l (m + 1), hence the degree condition of section 5; the
  volume inequality J^m > (l (m + 1))^m, that is A^m > (m + 1)^m, gives the interior condition
  (7) with b = 1/l; (6) follows from the closedness of the realization sets in the point. So the
  data of the minimizer for A exist at every closed point where g does not vanish, for every
  m₀ ≥ 1, from the numerical hypothesis for A, the strict volume inequality and the closedness of
  the realization sets of J in the tuple and in the point.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Shift

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- A section of D + div g vanishes at η exactly when its principal shift, a section of D, does. -/
theorem mem_cartierSectionsVanishingAt_principalShift (D : CartierDivisor Y)
    (g : Y.functionFieldˣ) (η : Y) (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    s ∈ cartierSectionsVanishingAt K (D + principalCartierDivisor Y g) η ↔
      cartierPrincipalShiftLinear (K := K) D g s ∈ cartierSectionsVanishingAt K D η := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt η
  have hfg : (D + principalCartierDivisor Y g).IsLocalEquationAt η (f * g) :=
    hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor η g)
  rw [mem_cartierSectionsVanishingAt_iff _ η (f * g) hfg,
    mem_cartierSectionsVanishingAt_iff _ η f hf]
  have hcoef : cartierLocalCoefficient (D + principalCartierDivisor Y g) η (f * g) hfg s =
      cartierLocalCoefficient D η f hf (cartierPrincipalShiftLinear (K := K) D g s) := by
    apply IsFractionRing.injective (Y.presheaf.stalk η) Y.functionField
    rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image,
      cartierPrincipalShiftLinear_rational, Units.val_mul, mul_assoc]
  rw [hcoef]

/-- The restricted dimension of a subspace does not change under the principal shift. -/
theorem cartierRestrictedSubspaceDim_principalShift (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (η : Y) (V : Submodule K Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    cartierRestrictedSubspaceDim K D η (V.map (cartierPrincipalShiftLinear (K := K) D g)) =
      cartierRestrictedSubspaceDim K (D + principalCartierDivisor Y g) η V := by
  have hmap : (cartierSectionsVanishingAt K (D + principalCartierDivisor Y g) η).map
      ((cartierPrincipalShiftEquiv (K := K) D g : _ ≃ₗ[K] _) : _ →ₗ[K] _) =
      cartierSectionsVanishingAt K D η := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (mem_cartierSectionsVanishingAt_principalShift D g η s).mp hs
    · intro ht
      refine ⟨(cartierPrincipalShiftEquiv (K := K) D g).symm t,
        (mem_cartierSectionsVanishingAt_principalShift D g η _).mpr ?_,
        (cartierPrincipalShiftEquiv (K := K) D g).apply_symm_apply t⟩
      have h1 : cartierPrincipalShiftLinear (K := K) D g
          ((cartierPrincipalShiftEquiv (K := K) D g).symm t) = t :=
        (cartierPrincipalShiftEquiv (K := K) D g).apply_symm_apply t
      rw [h1]
      exact ht
  set Qe := Submodule.Quotient.equiv
    (cartierSectionsVanishingAt K (D + principalCartierDivisor Y g) η)
    (cartierSectionsVanishingAt K D η) (cartierPrincipalShiftEquiv (K := K) D g) hmap with hQe
  have hcomp : (cartierSectionsVanishingAt K D η).mkQ ∘ₗ cartierPrincipalShiftLinear (K := K) D g =
      (Qe : _ →ₗ[K] _) ∘ₗ
        (cartierSectionsVanishingAt K (D + principalCartierDivisor Y g) η).mkQ := by
    ext s
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, hQe,
      LinearEquiv.coe_coe, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
    rfl
  unfold cartierRestrictedSubspaceDim
  rw [← Submodule.map_comp, hcomp, Submodule.map_comp, LinearEquiv.finrank_map_eq]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- A subspace of the sections of a divisor gives one of an equal divisor with the same restricted
dimension. -/
theorem exists_restrictedSubspace_of_eq [Y.Over (Spec (CommRingCat.of K))]
    {D₁ D₂ : CartierDivisor Y} (h : D₁ = D₂) (η : Y)
    (V : Submodule K Γ(D₁.sheaf, ⊤)) [FiniteDimensional K V] :
    ∃ V₂ : Submodule K Γ(D₂.sheaf, ⊤), FiniteDimensional K V₂ ∧
      cartierRestrictedSubspaceDim K D₂ η V₂ = cartierRestrictedSubspaceDim K D₁ η V := by
  subst h
  exact ⟨V, inferInstance, rfl⟩

/-- The numerical hypothesis passes from A to L when l A = L + div φ: the constant is multiplied
by l^d. -/
theorem restrictedGrowth_of_nsmul_eq_add_principal (A L : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l)
    (φ : Y.functionFieldˣ) (hlA : l • A = L + principalCartierDivisor Y φ) (η : Y) {d : ℕ}
    {c : ℝ} (hgrow : ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
      Γ((j • A).sheaf, ⊤), FiniteDimensional K V ∧
        (c - ε) * (j : ℝ) ^ d / d.factorial ≤ cartierRestrictedSubspaceDim K (j • A) η V) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • L).sheaf, ⊤),
      FiniteDimensional K V ∧ ((l : ℝ) ^ d * c - ε) * (j : ℝ) ^ d / d.factorial ≤
        cartierRestrictedSubspaceDim K (j • L) η V := by
  intro ε hε
  have hl0 : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hld : (0 : ℝ) < (l : ℝ) ^ d := pow_pos (by positivity) d
  have hmul : Tendsto (fun j : ℕ => l * j) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left j hl) tendsto_id
  filter_upwards [hmul.eventually (hgrow (ε / (l : ℝ) ^ d) (div_pos hε hld))] with j hj
  obtain ⟨V, hV, hle⟩ := hj
  have hE : (l * j) • A = j • L + principalCartierDivisor Y (φ ^ j) := by
    rw [mul_comm, ← smul_smul, hlA, smul_add, principalCartierDivisor_power]
  obtain ⟨V₂, hV₂, hdim₂⟩ := exists_restrictedSubspace_of_eq hE η V
  refine ⟨V₂.map (cartierPrincipalShiftLinear (K := K) (j • L) (φ ^ j)), inferInstance, ?_⟩
  rw [cartierRestrictedSubspaceDim_principalShift, hdim₂]
  have heq : ((l : ℝ) ^ d * c - ε) * (j : ℝ) ^ d / d.factorial =
      (c - ε / (l : ℝ) ^ d) * ((l * j : ℕ) : ℝ) ^ d / d.factorial := by
    push_cast
    field_simp
    ring
  rw [heq]
  exact hle

end Shift

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

/-- The data of the minimizer at x for a divisor A with l A = J + div φ, with zero boundary, for
every m₀ ≥ 1, from the numerical hypothesis for A, the strict volume inequality
J^m > (l (m + 1))^m and the closedness of the realization sets of J in the tuple and in the point
at all large degrees. -/
theorem projectiveHyperplane_ample_kltIsolationMinimizerData_of_strictVolume
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (A : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l) (φ : Y.functionFieldˣ)
    (hlA : l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (hvol : ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
        Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop
        (𝓝 ((r : ℝ) / m.factorial)) → (l * (m + 1)) ^ m < r)
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • projectiveHyperplaneCartier e g hg hggen)
        (Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  have hklt := smooth_logPairIsKlt_boundary_zero cY (1 : Y.functionFieldˣ) 1 le_rfl
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hl0 : (l : ℝ) ≠ 0 := hlr.ne'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- every multiple of J has a nonzero section
  have hsec : ∀ q : ℕ, 0 ≤ q → ∃ σ : Γ((q • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      σ ≠ 0 := by
    intro q _
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x q
    refine ⟨σ₀, ?_⟩
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  have hNpos : ∀ j : ℕ, 0 < Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    intro j
    obtain ⟨σ, hσ⟩ := hsec j (Nat.zero_le j)
    have := hfin j
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ, hσ⟩
  -- the numerical hypothesis for J with s = l (m + 1), and the degree condition
  have hgrowJ : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K
        Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), FiniteDimensional K V ∧
          ((((l * (m + 1) : ℕ) : ℕ) : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
            cartierRestrictedSubspaceDim K (j • projectiveHyperplaneCartier e g hg hggen) η V := by
    intro η d hd hd1 ε hε
    have h := restrictedGrowth_of_nsmul_eq_add_principal A
      (projectiveHyperplaneCartier e g hg hggen) hl φ hlA η (hgrow η d hd hd1) ε hε
    have hc : (((l * (m + 1) : ℕ) : ℕ) : ℝ) ^ d = (l : ℝ) ^ d * ((m : ℝ) + 1) ^ d := by
      push_cast
      rw [mul_pow]
    rw [hc]
    exact h
  have := hfin
  have hdeg := projectiveHyperplane_degreeCondition_of_restrictedGrowth e g hg hggen he x
    (l * (m + 1)) hgrowJ
  -- the interior condition (7) with b = 1/l, from the strict volume inequality
  obtain ⟨r, -, -, hlim, hstart⟩ := projectiveHyperplane_multiple_interior_start e g hg hggen he
    hdimY hm (projectiveHyperplaneCartier e g hg hggen) (k := 1) one_pos (one_nsmul _) 0 hsec
  have hlim' : Tendsto (fun D : ℕ => (Module.finrank K
      Γ((D • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) : ℝ) / (D : ℝ) ^ m) atTop
      (𝓝 ((r : ℝ) / m.factorial)) := by
    simpa using hlim
  have hvolr : ((l : ℝ) * ((m : ℝ) + 1)) ^ m < (r : ℝ) := by exact_mod_cast hvol r hlim'
  have hroot : (l : ℝ) * ((m : ℝ) + 1) < (r : ℝ) ^ ((m : ℝ)⁻¹) := by
    rw [Real.lt_rpow_inv_iff_of_pos (by positivity) (by positivity) hm0, Real.rpow_natCast]
    exact hvolr
  have hb : (m : ℝ) / (1 / l) <
      (m : ℝ) / (m + 1) * ((r : ℝ) / ((1 : ℕ) : ℝ) ^ m) ^ (m : ℝ)⁻¹ := by
    rw [Nat.cast_one, one_pow, div_one, div_div_eq_mul_div, div_one, div_mul_eq_mul_div,
      lt_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨t₀, -, ht₀b, ζ, hζ, δ, hδ, hev⟩ := hstart (b := 1 / l) (one_div_pos.mpr hlr) hb x hxc
  -- the data of the minimizer for A
  refine projectiveHyperplane_kltIsolationMinimizerData_shift_of_degree_sequence e g hg hggen he hm
    cY x hxc hgx (b := 1 / l) (t₀ := t₀) (δ := min δ (1 / 2)) (one_div_pos.mpr hlr)
    (l * (m + 1)) (le_trans (by norm_num) (Nat.mul_le_mul hl (Nat.le_add_left 1 m)))
    (by push_cast; field_simp) ht₀b (lt_min hδ (by norm_num))
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    (fun w _ => exists_nat_topologicalKrullDim_closure_eq hdimY w) hdeg hclosed ?_ ?_ A φ hlA
    (le_of_eq (mul_one_div_cancel hl0)) m₀ hm₀
  · filter_upwards [hev] with j hj t ht₀t htb
    obtain ⟨B, hB⟩ := hj t ht₀t htb.le
    exact ⟨B, ζ, hζ.le, hB.trans (by linarith [min_le_left δ (1 / 2)])⟩
  · filter_upwards [hclosedPt, eventually_ge_atTop 1] with j hj hj1
    intro t _ _ w hwx _
    obtain ⟨Z, hZ, hwZ, hZ6⟩ := sncWeight_specialization_comparison_of_closed cY
      (1 : Y.functionFieldˣ) le_rfl
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • projectiveHyperplaneCartier e g hg hggen) hklt (hNpos j) hj1 t hj hwx
    refine ⟨⋂ i, (Z i)ᶜ, closedPointsDenseOver_of_countable Z hZ hwZ,
      fun y hyc hyG _ => hZ6 y ?_ (fun i => Set.mem_iInter.mp hyG i)⟩
    have := hfin j
    obtain ⟨p, hp, -⟩ := exists_sncWeightProfile_le_of_smooth_point hm cY
      (j • projectiveHyperplaneCartier e g hg hggen)
      (fun i => Module.finBasis K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) i)
      (fun i => (Module.finBasis K _).ne_zero i) y hyc one_pos (j := (j : ℝ)) (by positivity)
      (le_refl (0 : ℝ))
    exact ⟨_, Module.finBasis K _, p, hp, rfl⟩

end Hyperplane

end MixedFujita
