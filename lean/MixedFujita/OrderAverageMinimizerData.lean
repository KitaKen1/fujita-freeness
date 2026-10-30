/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.AmpleSumMinimizerData
public import MixedFujita.InteriorStartBound

/-!
The data of the minimizer from the bound (33) on vanishing orders at the point (steps 13 and 14).

The bound (33) of Lemma 5 says that the average total degree of the initial exponents of the
sections of j A at x, divided by j, stays above some σ > n. The sum of the total degrees of the
initial exponents is the largest value of Σ_i ord_x(s_i) over the bases (s_i), so (33) is written
here without coordinates: for all large j some basis of the sections of j A has
Σ_i ord_x(s_i) ≥ σ j N_j. Vanishing orders at a point do not change under a principal shift, so for
l A = J + div φ the bases of (j l) A give bases of j J with the same orders, and the average for J
is above l σ > n/b with b = 1/l. With the uniform order bound ord_x ≤ C j this is the interior
condition (7) for v = ζ ord_x (`uniform_interior_start`).

So the data of the minimizer at x exist for an ample sum A from the numerical hypothesis, (33) at x
and the closedness of the realization sets of A. Lemma 5 of the manuscript proves (33) at every
closed point where K_X + A + N is not generated; the case where the volume inequality is strict was
done before without (33). Hence the minimizer statement used by S-NF for ample sums, and with it
F1 (given the sum form of the Kawamata–Viehweg statement), follows from the closedness of the
realization sets and from (33) at the non-generated closed points in the equality case.
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

/-- The interior start of `uniform_interior_start` for families indexed by `Fin N_j`. -/
theorem uniform_interior_start_fin (N : ℕ → ℕ) (a : ∀ j, Fin (N j) → ℝ) {A₀ b C σ : ℝ}
    (hA₀ : 0 < A₀) (hb : 0 < b) (hC : 0 ≤ C) (hσ : A₀ / b < σ)
    (hN : ∀ᶠ j in atTop, 0 < N j)
    (ha : ∀ᶠ j in atTop, ∀ i, 0 ≤ a j i ∧ a j i ≤ C)
    (hmean : ∀ᶠ j in atTop, σ * N j ≤ ∑ i, a j i) :
    ∃ t₀, 0 < t₀ ∧ t₀ < b ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j in atTop, ∀ t, t₀ ≤ t → t ≤ b →
      (∑ i, Real.exp (ζ * A₀ / t - ζ * a j i)) / N j ≤ 1 - δ := by
  obtain ⟨a', ha'⟩ : ∃ a' : ℕ → ℕ → ℝ, ∀ j (i : Fin (N j)), a' j i = a j i :=
    ⟨fun j k => if h : k < N j then a j ⟨k, h⟩ else 0, fun j i => by simp⟩
  have hsum : ∀ j, ∑ k ∈ Finset.range (N j), a' j k = ∑ i, a j i := fun j => by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => ha' j i
  have hsumexp : ∀ j (ζ t : ℝ), ∑ k ∈ Finset.range (N j), Real.exp (ζ * A₀ / t - ζ * a' j k) =
      ∑ i, Real.exp (ζ * A₀ / t - ζ * a j i) := fun j ζ t => by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun i _ => by rw [ha' j i]
  have hE : ∀ᶠ j in atTop, (Finset.range (N j)).Nonempty := by
    filter_upwards [hN] with j hj
    exact Finset.nonempty_range_iff.mpr hj.ne'
  have ha'' : ∀ᶠ j in atTop, ∀ k ∈ Finset.range (N j), 0 ≤ a' j k ∧ a' j k ≤ C := by
    filter_upwards [ha] with j hj k hk
    have hk' := Finset.mem_range.mp hk
    have h := ha' j ⟨k, hk'⟩
    simp only at h
    rw [h]
    exact hj ⟨k, hk'⟩
  have hmean' : ∀ᶠ j in atTop,
      σ ≤ (∑ k ∈ Finset.range (N j), a' j k) / (Finset.range (N j)).card := by
    filter_upwards [hmean, hN] with j hj hNj
    rw [hsum, Finset.card_range, le_div_iff₀ (by exact_mod_cast hNj)]
    exact hj
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hev⟩ := uniform_interior_start
    (fun j => Finset.range (N j)) a' hA₀ hb hC hσ hE ha'' hmean'
  refine ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, ?_⟩
  filter_upwards [hev] with j hj t ht₀t htb
  have h := hj t ht₀t htb
  rwa [hsumexp, Finset.card_range] at h

section Shift

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The vanishing order at a point of a section of D + div g is that of its principal shift. -/
theorem cartierSectionVanishingOrder_principalShift (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (x : Y) (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    cartierSectionVanishingOrder D x (cartierPrincipalShiftLinear (K := K) D g s) =
      cartierSectionVanishingOrder (D + principalCartierDivisor Y g) x s := by
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x
  have hfg : (D + principalCartierDivisor Y g).IsLocalEquationAt x (f * g) :=
    hf.mul (CartierDivisor.isLocalEquationAt_principalCartierDivisor x g)
  have hcoef : cartierLocalCoefficient (D + principalCartierDivisor Y g) x (f * g) hfg s =
      cartierLocalCoefficient D x f hf (cartierPrincipalShiftLinear (K := K) D g s) := by
    apply IsFractionRing.injective (Y.presheaf.stalk x) Y.functionField
    rw [cartierLocalCoefficient_image, cartierLocalCoefficient_image,
      cartierPrincipalShiftLinear_rational, Units.val_mul, mul_assoc]
  rw [cartierSectionVanishingOrder_eq_localCoefficient D x f hf,
    cartierSectionVanishingOrder_eq_localCoefficient _ x (f * g) hfg, hcoef]

/-- If E = D + div g, a basis of the sections of D gives a basis of the sections of E, with the
same index type and the same vanishing orders at x. -/
theorem exists_basis_vanishingOrder_of_eq_add_principal {E D : CartierDivisor Y}
    {g : Y.functionFieldˣ} (h : E = D + principalCartierDivisor Y g) (x : Y) {ι : Type*}
    (B : Module.Basis ι K Γ(D.sheaf, ⊤)) :
    ∃ B' : Module.Basis ι K Γ(E.sheaf, ⊤), ∀ i,
      cartierSectionVanishingOrder E x (B' i) = cartierSectionVanishingOrder D x (B i) := by
  subst h
  refine ⟨B.map (cartierPrincipalShiftEquiv (K := K) D g).symm, fun i => ?_⟩
  rw [Module.Basis.map_apply, ← cartierSectionVanishingOrder_principalShift (K := K)]
  congr 1
  exact (cartierPrincipalShiftEquiv (K := K) D g).apply_symm_apply (B i)

end Shift

section Hyperplane

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {n m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]
  (e : Y ⟶ polynomialProjectiveScheme n K) [IsClosedImmersion e]
  (g : MvPolynomial (Fin n) K) (hg : g.IsHomogeneous 1)
  (hggen : g ∉ (e (genericPoint Y)).asHomogeneousIdeal)

omit [CharZero K] [Uncountable K] in
/-- The interior condition (7) for the hyperplane class J at b = 1/l, at a closed point x, from
the bound (33) for A at x when l A = J + div φ: some σ > m and, for all large j, a basis of the
sections of j A with Σ_i ord_x(s_i) ≥ σ j N_j. -/
theorem projectiveHyperplane_start_of_orderAverage
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (hdimY : topologicalKrullDim Y = m) (A : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l)
    (φ : Y.functionFieldˣ)
    (hlA : l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (x : Y) (hxc : IsClosed ({x} : Set Y))
    (havg : ∃ σ : ℝ, (m : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
          ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) :
    ∃ t₀, 0 < t₀ ∧ t₀ < 1 / (l : ℝ) ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t, t₀ ≤ t →
      t ≤ 1 / (l : ℝ) →
      ∃ B : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B i)).toNat : ℝ)) ≤ 1 - δ := by
  obtain ⟨σ, hσ, hev⟩ := havg
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hprop : IsProper (Y ↘ Spec (CommRingCat.of K)) := by
    have := polynomialProjectiveToBase_isProper n K
    rw [← he]
    infer_instance
  obtain ⟨r₀, -, hfin, -⟩ := projectiveHyperplane_hilbert_leading e g hg hggen he hdimY hm
  have := hfin
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- the uniform order bound for the sections of the multiples of J
  obtain ⟨C, hC⟩ := cartierMultiple_vanishingOrder_le e g hg hggen he hdimY hm
    (projectiveHyperplaneCartier e g hg hggen) le_rfl (1 : Y.functionFieldˣ)
    (by rw [one_nsmul, principalCartierDivisor_one, add_zero])
  -- every multiple of J has a nonzero section
  have hNpos : ∀ j : ℕ, 0 < Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    intro j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, ?_⟩
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
    rw [map_zero] at hu
    exact not_isUnit_zero hu
  -- bases of j J from the bases of (j l) A
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  have hJ : ∀ᶠ j : ℕ in atTop, ∃ B : Module.Basis (Fin (Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
      σ * l * j * Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤
        ∑ i, ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
          (B i)).toNat : ℝ) := by
    filter_upwards [htend.eventually hev] with j hj
    obtain ⟨B, hB⟩ := hj
    obtain ⟨B', hB'⟩ := exists_basis_vanishingOrder_of_eq_add_principal (K := K)
      (nsmul_eq_nsmul_mul_add_principal hlA j) x B
    have hN : Module.finrank K Γ(((j * l) • A).sheaf, ⊤) =
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) :=
      (finrank_nsmul_eq_of_nsmul_eq hlA j).symm
    refine ⟨B'.reindex (finCongr hN), ?_⟩
    have hsum : ∑ i, ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen)
        x ((B'.reindex (finCongr hN)) i)).toNat : ℝ) =
        ∑ i, ((cartierSectionVanishingOrder ((j * l) • A) x (B i)).toNat : ℝ) := by
      simp only [Module.Basis.reindex_apply]
      rw [Equiv.sum_comp (finCongr hN).symm (fun i => ((cartierSectionVanishingOrder
        (j • projectiveHyperplaneCartier e g hg hggen) x (B' i)).toNat : ℝ))]
      exact Finset.sum_congr rfl fun i _ => by rw [hB' i]
    rw [hsum, ← hN]
    calc σ * l * j * Module.finrank K Γ(((j * l) • A).sheaf, ⊤) =
        σ * ((j * l : ℕ) : ℝ) * Module.finrank K Γ(((j * l) • A).sheaf, ⊤) := by
          push_cast
          ring
      _ ≤ _ := hB
  -- choose the bases
  obtain ⟨j₁, hj₁⟩ := Filter.eventually_atTop.mp hJ
  have hchoice : ∀ j : ℕ, ∃ B : Module.Basis (Fin (Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤), j₁ ≤ j →
      σ * l * j * Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤
        ∑ i, ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
          (B i)).toNat : ℝ) := by
    intro j
    by_cases h : j₁ ≤ j
    · obtain ⟨B, hB⟩ := hj₁ j h
      exact ⟨B, fun _ => hB⟩
    · exact ⟨Module.finBasis K _, fun h' => absurd h' h⟩
  choose Bf hBf using hchoice
  -- the interior start
  have hσl : (m : ℝ) / (1 / (l : ℝ)) < σ * l := by
    rw [div_div_eq_mul_div, div_one]
    exact mul_lt_mul_of_pos_right hσ hlr
  have hbound : ∀ᶠ j : ℕ in atTop, ∀ i, 0 ≤ ((cartierSectionVanishingOrder
      (j • projectiveHyperplaneCartier e g hg hggen) x (Bf j i)).toNat : ℝ) / j ∧
      ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
        (Bf j i)).toNat : ℝ) / j ≤ C := by
    filter_upwards [eventually_ge_atTop 1] with j hj i
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    refine ⟨div_nonneg (Nat.cast_nonneg _) hj0.le, ?_⟩
    rw [div_le_iff₀ hj0]
    have hle := hC x hxc j hj (Bf j i) ((Bf j).ne_zero i)
    have hnat : (cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
        (Bf j i)).toNat ≤ C * j := ENat.toNat_le_of_le_natCast hle
    calc ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
          (Bf j i)).toNat : ℝ) ≤ ((C * j : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (C : ℝ) * j := by push_cast; ring
  have hmean : ∀ᶠ j : ℕ in atTop, σ * l * Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) ≤
      ∑ i, ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
        (Bf j i)).toNat : ℝ) / j := by
    filter_upwards [eventually_ge_atTop (max j₁ 1)] with j hj
    have hj1 : j₁ ≤ j := le_of_max_le_left hj
    have hj0 : (0 : ℝ) < j := by exact_mod_cast (le_of_max_le_right hj)
    have hB := hBf j hj1
    rw [← Finset.sum_div, le_div_iff₀ hj0]
    calc σ * l * Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) *
          j = σ * l * j * Module.finrank K
            Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by ring
      _ ≤ _ := hB
  obtain ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, hstart⟩ := uniform_interior_start_fin
    (fun j => Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))
    (fun j i => ((cartierSectionVanishingOrder (j • projectiveHyperplaneCartier e g hg hggen) x
      (Bf j i)).toNat : ℝ) / j) (A₀ := m) (b := 1 / (l : ℝ)) (C := C) (σ := σ * l) hm0
    (one_div_pos.mpr hlr) (Nat.cast_nonneg C) hσl (Filter.Eventually.of_forall hNpos) hbound
    hmean
  refine ⟨t₀, ht₀, ht₀b, ζ, hζ, δ, hδ, ?_⟩
  filter_upwards [hstart] with j hj t ht₀t htb
  refine ⟨Bf j, ?_⟩
  have h := hj t ht₀t htb
  have heq : minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
      (j • projectiveHyperplaneCartier e g hg hggen) x (Bf j i)).toNat : ℝ)) =
      (∑ i, Real.exp (ζ * m / t - ζ * (((cartierSectionVanishingOrder
        (j • projectiveHyperplaneCartier e g hg hggen) x (Bf j i)).toNat : ℝ) / j))) /
        Module.finrank K Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    unfold minimizationFunctional
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ring
  rw [heq]
  exact h

/-- The data of the minimizer at x for a divisor A with l A = J + div φ, with zero boundary, for
every m₀ ≥ 1, from the numerical hypothesis for A, the interior condition (7) for J at b = 1/l and
the closedness of the realization sets of J in the tuple and in the point at all large degrees. -/
theorem projectiveHyperplane_ample_kltIsolationMinimizerData_of_start
    (he : e ≫ polynomialProjectiveToBase n K = Y ↘ Spec (CommRingCat.of K)) (hm : 1 ≤ m)
    (cY : EtaleChart K Y m) (A : CartierDivisor Y) {l : ℕ} (hl : 1 ≤ l) (φ : Y.functionFieldˣ)
    (hlA : l • A = projectiveHyperplaneCartier e g hg hggen + principalCartierDivisor Y φ)
    (x : Y) (hxc : IsClosed ({x} : Set Y)) (hgx : g ∉ (e x).asHomogeneousIdeal)
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (hstartJ : ∃ t₀, 0 < t₀ ∧ t₀ < 1 / (l : ℝ) ∧ ∃ ζ > 0, ∃ δ > 0, ∀ᶠ j : ℕ in atTop, ∀ t,
      t₀ ≤ t → t ≤ 1 / (l : ℝ) →
      ∃ B : Module.Basis (Fin (Module.finrank K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤))) K
          Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤),
        minimizationFunctional j t (ζ * m) (fun i => ζ * ((cartierSectionVanishingOrder
          (j • projectiveHyperplaneCartier e g hg hggen) x (B i)).toNat : ℝ)) ≤ 1 - δ)
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
  -- every multiple of J has a nonzero section
  have hNpos : ∀ j : ℕ, 0 < Module.finrank K
      Γ((j • projectiveHyperplaneCartier e g hg hggen).sheaf, ⊤) := by
    intro j
    have := hfin j
    obtain ⟨σ₀, hσ₀⟩ := projectiveHyperplane_exists_section_nonvanishing e g hg hggen x j
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨σ₀, ?_⟩
    rintro rfl
    obtain ⟨f, hf, hu⟩ := (mem_cartierSectionNonvanishingOpen _ 0 x).mp hσ₀
    rw [map_zero] at hu
    exact not_isUnit_zero hu
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
  obtain ⟨t₀, -, ht₀b, ζ, hζ, δ, hδ, hev⟩ := hstartJ
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

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] {m : ℕ}
  {Y : Scheme.{u}} [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension m (Y ↘ Spec (CommRingCat.of K))]

/-- The data of the minimizer at a closed point x for an ample sum A, with zero boundary, for every
m₀ ≥ 1, from the numerical hypothesis for A, the bound (33) at x (some σ > m and, for all large j,
a basis of the sections of j A with Σ_i ord_x(s_i) ≥ σ j N_j) and the closedness of the
realization sets of A in the tuple and in the point at all large degrees. -/
theorem ampleSum_kltIsolationMinimizerData_of_orderAverage (hm : 1 ≤ m) (cY : EtaleChart K Y m)
    (A : CartierDivisor Y) (hA : CartierIsAmpleSum K A) (x : Y) (hxc : IsClosed ({x} : Set Y))
    (hgrow : ∀ (η : Y) (d : ℕ), topologicalKrullDim (closure ({η} : Set Y)) = d → 1 ≤ d →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
        FiniteDimensional K V ∧ ((m + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
          cartierRestrictedSubspaceDim K (j • A) η V)
    (havg : ∃ σ : ℝ, (m : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
      ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K Γ((j • A).sheaf, ⊤),
        σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
          ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ))
    (hclosed : ∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
      (j • A) x)
    (hclosedPt : ∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY
        (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ)))
        (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y})
    (m₀ : ℕ) (hm₀ : 1 ≤ m₀) :
    KltIsolationMinimizerData cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) A m₀
      x := by
  have hsm : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth m _
  have hdimY : topologicalKrullDim Y = m := etaleChart_topologicalKrullDim cY
  obtain ⟨l, hl, n, e, hci, he, g, hg, hggen, hgx, φ, hlA⟩ :=
    cartierIsAmpleProj_exists_hyperplane_nonvanishing (cartierIsAmpleProj_of_isAmpleSum hA) x
  have htend : Tendsto (fun j : ℕ => j * l) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_right j hl) tendsto_id
  refine projectiveHyperplane_ample_kltIsolationMinimizerData_of_start e g hg hggen he hm cY A hl
    φ hlA x hxc hgx hgrow
    (projectiveHyperplane_start_of_orderAverage e g hg hggen he hm hdimY A hl φ hlA x hxc havg)
    ?_ ?_ m₀ hm₀
  · filter_upwards [htend.eventually hclosed] with j hj
    exact realizationSetsZariskiClosed_of_nsmul_eq cY _ 1 _ hlA x j hj
  · filter_upwards [htend.eventually hclosedPt] with j hj
    exact normalizedProfiles_isClosed_of_nsmul_eq cY _ 1 _ hlA j hj

end Assembly

/-- The minimizer statement used by S-NF for ample sums follows from the closedness of the
realization sets of ample sums at closed points (in the tuple and in the point, at all large
degrees) and from the bound (33) of Lemma 5 at the closed points where K_X + A + N is not
generated, when the volume inequality is not strict. -/
theorem smoothMinimizerDataStatement_of_closed_of_orderAverage
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosed {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hfive : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
      topologicalKrullDim X = n → 1 ≤ n →
      ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
        (c₀ : EtaleChart K X n) (A N : CartierDivisor X), CartierIsAmpleSum K A →
        CartierIsNef K N →
        (∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
            FiniteDimensional K V ∧ ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
              cartierRestrictedSubspaceDim K (j • A) η V) →
        ¬ (∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ n) atTop (𝓝 ((r : ℝ) / n.factorial)) →
          (l * (n + 1)) ^ n < r) →
        ∀ x : X, IsClosed ({x} : Set X) →
          (¬ ∃ (f : X.functionFieldˣ)
            (hf : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f)
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f hf t)) →
          ∃ σ : ℝ, (n : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
            ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K
              Γ((j • A).sheaf, ⊤),
              σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
                ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) :
    SmoothMinimizerDataStatement.{u} := by
  intro K _ _ _ _ X _ _ n hdim hn _ _ c₀ A N hA hN hnum m₀ hm₀ x hx hnf
  obtain ⟨h1, h2⟩ := hcl K X n c₀ A hA x hx
  by_cases hvol : ∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
      Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ n) atTop (𝓝 ((r : ℝ) / n.factorial)) →
      (l * (n + 1)) ^ n < r
  · exact ampleSum_kltIsolationMinimizerData_of_strictVolume hn c₀ A hA x hx hnum hvol h1 h2 m₀
      hm₀
  · exact ampleSum_kltIsolationMinimizerData_of_orderAverage hn c₀ A hA x hx hnum
      (hfive K X n hdim hn c₀ A N hA hN hnum hvol x hx hnf) h1 h2 m₀ hm₀

/-- F1, the mixed Fujita freeness, follows from the sum form of the Kawamata–Viehweg statement,
the closedness of the realization sets of ample sums at closed points, and the bound (33) of
Lemma 5 at the non-generated closed points when the volume inequality is not strict. -/
theorem mixedFujitaFreeness_of_kawamataViehwegSum_of_closed_of_orderAverage
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hcl : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K] (X : Scheme.{u})
      [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ)
      [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] (c₀ : EtaleChart K X n)
      (A : CartierDivisor X), CartierIsAmpleSum K A → ∀ x : X, IsClosed ({x} : Set X) →
      (∀ᶠ j : ℕ in atTop, RealizationSetsZariskiClosed c₀ (1 : X.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
        (j • A) x) ∧
      (∀ᶠ j : ℕ in atTop, ∀ α : Fin (Module.finrank K Γ((j • A).sheaf, ⊤)) → ℚ,
        IsClosed {y : X | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles c₀
          (1 : X.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor c₀ + principalCartierDivisor X (1 : X.functionFieldˣ)))
          (j • A) (Module.finrank K Γ((j • A).sheaf, ⊤)) y}))
    (hfive : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] [Uncountable K]
      (X : Scheme.{u}) [IsIntegral X] [X.Over (Spec (CommRingCat.of K))] (n : ℕ),
      topologicalKrullDim X = n → 1 ≤ n →
      ∀ [SmoothOfRelativeDimension n (X ↘ Spec (CommRingCat.of K))] [IsLocallyNoetherian X]
        (c₀ : EtaleChart K X n) (A N : CartierDivisor X), CartierIsAmpleSum K A →
        CartierIsNef K N →
        (∀ (η : X) (d : ℕ), topologicalKrullDim (closure ({η} : Set X)) = d → 1 ≤ d →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∃ V : Submodule K Γ((j • A).sheaf, ⊤),
            FiniteDimensional K V ∧ ((n + 1 : ℝ) ^ d - ε) * (j : ℝ) ^ d / d.factorial ≤
              cartierRestrictedSubspaceDim K (j • A) η V) →
        ¬ (∀ l : ℕ, 1 ≤ l → ∀ r : ℕ, Tendsto (fun D : ℕ => (Module.finrank K
          Γ(((D * l) • A).sheaf, ⊤) : ℝ) / (D : ℝ) ^ n) atTop (𝓝 ((r : ℝ) / n.factorial)) →
          (l * (n + 1)) ^ n < r) →
        ∀ x : X, IsClosed ({x} : Set X) →
          (¬ ∃ (f : X.functionFieldˣ)
            (hf : (smoothCanonicalDivisor c₀ + A + N).IsLocalEquationAt x f)
            (t : Γ((smoothCanonicalDivisor c₀ + A + N).sheaf, ⊤)),
            IsUnit (cartierLocalCoefficient (smoothCanonicalDivisor c₀ + A + N) x f hf t)) →
          ∃ σ : ℝ, (n : ℝ) < σ ∧ ∀ᶠ j : ℕ in atTop,
            ∃ B : Module.Basis (Fin (Module.finrank K Γ((j • A).sheaf, ⊤))) K
              Γ((j • A).sheaf, ⊤),
              σ * j * Module.finrank K Γ((j • A).sheaf, ⊤) ≤
                ∑ i, ((cartierSectionVanishingOrder (j • A) x (B i)).toNat : ℝ)) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kawamataViehwegSum_of_minimizerData hKV
    (smoothMinimizerDataStatement_of_closed_of_orderAverage hcl hfive)

end MixedFujita
