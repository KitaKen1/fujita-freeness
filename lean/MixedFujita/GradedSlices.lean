/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.LatticeBrunnMinkowski
public import MixedFujita.WeightedGrowth
public import Lean.Elab.Tactic.Omega

/-!
The finite slice-growth step in Section 4. The graded exponent family and
its central-slice lower bound are explicit inputs. Constructing those inputs
from spaces of sections is a separate geometric task.
-/

@[expose] public section

namespace MixedFujita

open scoped Pointwise

/-- Multiplication of sections must supply this addition law for exponents. -/
def GradedExponentSemigroup {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) : Prop :=
  ∀ ⦃j h a b⦄, a ∈ Γ j → b ∈ Γ h → a + b ∈ Γ (j + h)

noncomputable def exponentSlice {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (p : Fin r → ℤ) : Finset (Fin (d + 1) → ℤ) := by
  classical
  exact ((Γ j).filter (fun a => a.1 = p)).image Prod.snd

theorem mem_exponentSlice {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (p : Fin r → ℤ) (γ : Fin (d + 1) → ℤ) :
    γ ∈ exponentSlice Γ j p ↔ (p, γ) ∈ Γ j := by
  classical
  simp only [exponentSlice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨q, δ⟩, ⟨ha, hp⟩, hγ⟩
    change q = p at hp
    change δ = γ at hγ
    simpa only [hp, hγ] using ha
  · intro ha
    exact ⟨(p, γ), ⟨ha, rfl⟩, rfl⟩

theorem exponentSlice_add_subset {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (j h : ℕ) (p q : Fin r → ℤ) :
    exponentSlice Γ j p + exponentSlice Γ h q ⊆ exponentSlice Γ (j + h) (p + q) := by
  intro γ hγ
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hγ
  exact (mem_exponentSlice Γ _ _ _).mpr
    (hΓ ((mem_exponentSlice Γ _ _ _).mp ha) ((mem_exponentSlice Γ _ _ _).mp hb))

theorem thickened_exponentSlice_subset {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (j q h₀ : ℕ) (p : Fin r → ℤ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0) :
    thickenedSum (exponentSlice Γ j p) (exponentSlice Γ q 0) ⊆
      exponentSlice Γ (j + q + h₀) p := by
  intro γ hγ
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hγ
  have ha' := exponentSlice_add_subset Γ hΓ j q p 0 ha
  have h := exponentSlice_add_subset Γ hΓ (j + q) h₀ (p + 0) 0
    (Finset.mem_add.mpr ⟨a, ha', b, hcube hb, rfl⟩)
  simpa only [add_zero] using h

/-- The manuscript's b_p, in positive tangent dimension d+1. -/
noncomputable def sliceRadius {d : ℕ} (E : Finset (Fin (d + 1) → ℤ)) : ℝ :=
  (((d + 1).factorial : ℝ) * (E.card : ℝ)) ^ ((d : ℝ) + 1)⁻¹

theorem sliceRadius_nonneg {d : ℕ} (E : Finset (Fin (d + 1) → ℤ)) :
    0 ≤ sliceRadius E := Real.rpow_nonneg (by positivity) _

theorem sliceRadius_factor {d : ℕ} (E : Finset (Fin (d + 1) → ℤ)) :
    sliceRadius E = ((d + 1).factorial : ℝ) ^ ((d : ℝ) + 1)⁻¹ *
      (E.card : ℝ) ^ ((d : ℝ) + 1)⁻¹ :=
  Real.mul_rpow (by positivity) (by positivity)

theorem sliceRadius_empty (d : ℕ) :
    sliceRadius (∅ : Finset (Fin (d + 1) → ℤ)) = 0 := by
  simp [sliceRadius, Real.zero_rpow (by positivity : ((d : ℝ) + 1)⁻¹ ≠ 0)]

theorem nonempty_of_sliceRadius_pos {d : ℕ} {E : Finset (Fin (d + 1) → ℤ)}
    (h : 0 < sliceRadius E) : E.Nonempty := by
  by_contra he
  have he' : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  rw [he', sliceRadius_empty] at h
  exact (lt_irrefl 0) h

theorem sliceRadius_pos {d : ℕ} {E : Finset (Fin (d + 1) → ℤ)}
    (hE : E.Nonempty) : 0 < sliceRadius E := by
  have hc : 0 < (E.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hE
  exact Real.rpow_pos_of_pos (mul_pos (by positivity) hc) _

theorem sliceRadius_power {d : ℕ} (E : Finset (Fin (d + 1) → ℤ)) :
    sliceRadius E ^ (d + 1) = ((d + 1).factorial : ℝ) * (E.card : ℝ) := by
  rw [sliceRadius, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hn : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by simp
  rw [hn, inv_mul_cancel₀ (by positivity), Real.rpow_one]

theorem sliceRadius_brunn_minkowski {d : ℕ}
    (E F G : Finset (Fin (d + 1) → ℤ)) (hE : E.Nonempty) (hF : F.Nonempty)
    (hsubset : thickenedSum E F ⊆ G) :
    sliceRadius E + sliceRadius F ≤ sliceRadius G := by
  have h := mul_le_mul_of_nonneg_left
    (lattice_brunn_minkowski_of_subset E F G hE hF hsubset)
    (show 0 ≤ ((d + 1).factorial : ℝ) ^ ((d : ℝ) + 1)⁻¹ by positivity)
  simpa only [mul_add, ← sliceRadius_factor] using h

/-- The fixed cube degree is paid for in the additive error, uniformly in p. -/
theorem exponentSlice_radius_growth {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (j q h₀ : ℕ) (p : Fin r → ℤ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0)
    (hp : (exponentSlice Γ j p).Nonempty) (hq : (exponentSlice Γ q 0).Nonempty)
    {lam C : ℝ} (hlower : lam * q - C ≤ sliceRadius (exponentSlice Γ q 0)) :
    sliceRadius (exponentSlice Γ j p) + lam * ((q + h₀ : ℕ) : ℝ) - (C + lam * h₀) ≤
      sliceRadius (exponentSlice Γ (j + q + h₀) p) := by
  have h := sliceRadius_brunn_minkowski _ _ _ hp hq
    (thickened_exponentSlice_subset Γ hΓ j q h₀ p hcube)
  simp only [Nat.cast_add] at ⊢
  linarith

theorem uniform_exponentSlice_radius_growth {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤ sliceRadius (exponentSlice Γ q 0))
    (j h : ℕ) (p : Fin r → ℤ) (hh : H + h₀ ≤ h)
    (hp : (exponentSlice Γ j p).Nonempty) :
    sliceRadius (exponentSlice Γ j p) + lam * h - (C + lam * h₀) ≤
      sliceRadius (exponentSlice Γ (j + h) p) := by
  have hq : H ≤ h - h₀ := by omega
  have hh₀ : h - h₀ + h₀ = h := by omega
  have hpositive : 0 < lam * (h - h₀ : ℕ) - C := by
    have hcast : (H : ℝ) ≤ (h - h₀ : ℕ) := by exact_mod_cast hq
    have hmul := mul_le_mul_of_nonneg_left hcast hlam
    linarith
  have hnonempty := nonempty_of_sliceRadius_pos (hpositive.trans_le (hlower _ hq))
  simpa only [hh₀, Nat.add_assoc] using
    exponentSlice_radius_growth Γ hΓ j (h - h₀) h₀ p hcube hp hnonempty (hlower _ hq)

/-- Finite weighted growth on the old active slices; new slices can add only
nonnegative terms when the weights are nonnegative. -/
theorem weighted_exponentSlice_growth {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤ sliceRadius (exponentSlice Γ q 0))
    (j h : ℕ) (s : Finset (Fin r → ℤ)) (w : (Fin r → ℤ) → ℝ)
    (hh : H + h₀ ≤ h) (hr : 0 ≤ lam * h - (C + lam * h₀))
    (hw : ∀ p ∈ s, 0 ≤ w p) (hs : ∀ p ∈ s, (exponentSlice Γ j p).Nonempty) :
    (∑ p ∈ s, w p * sliceRadius (exponentSlice Γ j p) ^ (d + 2)) +
      (d + 2 : ℝ) * (lam * h - (C + lam * h₀)) *
        (∑ p ∈ s, w p * sliceRadius (exponentSlice Γ j p) ^ (d + 1)) ≤
      ∑ p ∈ s, w p * sliceRadius (exponentSlice Γ (j + h) p) ^ (d + 2) := by
  simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    add_assoc, one_add_one_eq_two] using
    weighted_power_growth s (d + 1) w
      (fun p => sliceRadius (exponentSlice Γ j p))
      (fun p => sliceRadius (exponentSlice Γ (j + h) p)) hw
      (fun p _ => sliceRadius_nonneg _) hr
      (fun p hp => by
        have h := uniform_exponentSlice_radius_growth Γ hΓ H h₀ hcube hlam hH hlower
          j h p hh (hs p hp)
        linarith)

noncomputable def exponentSupport {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) : Finset (Fin r → ℤ) := by
  classical
  exact (Γ j).image Prod.fst

theorem mem_exponentSupport {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ) (p : Fin r → ℤ) :
    p ∈ exponentSupport Γ j ↔ (exponentSlice Γ j p).Nonempty := by
  classical
  simp only [exponentSupport, Finset.mem_image, Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨⟨q, γ⟩, ha, hp⟩
    change q = p at hp
    subst q
    exact Finset.nonempty_iff_ne_empty.mp
      ⟨γ, (mem_exponentSlice Γ j p γ).mpr ha⟩
  · intro hs
    obtain ⟨γ, hγ⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    exact ⟨(p, γ), (mem_exponentSlice Γ j p γ).mp hγ, rfl⟩

theorem exponentSlice_snd_injective {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ) (p : Fin r → ℤ) :
    Set.InjOn (Prod.snd : ((Fin r → ℤ) × (Fin (d + 1) → ℤ)) → (Fin (d + 1) → ℤ))
      (↑((Γ j).filter (fun a => a.1 = p)) : Set ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) := by
  intro a ha b hb hab
  exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab

theorem exponentSlice_card {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ) (p : Fin r → ℤ) :
    (exponentSlice Γ j p).card = ((Γ j).filter (fun a => a.1 = p)).card := by
  classical
  exact Finset.card_image_of_injOn (exponentSlice_snd_injective Γ j p)

/-- Partition the entire exponent set by its normal-coordinate slice. -/
theorem sum_exponentSlices {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ)
    (f : (Fin r → ℤ) → (Fin (d + 1) → ℤ) → ℝ) :
    (∑ p ∈ exponentSupport Γ j, ∑ γ ∈ exponentSlice Γ j p, f p γ) =
      ∑ a ∈ Γ j, f a.1 a.2 := by
  classical
  calc
    _ = ∑ p ∈ exponentSupport Γ j,
        ∑ a ∈ (Γ j).filter (fun a => a.1 = p), f a.1 a.2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [exponentSlice, Finset.sum_image (exponentSlice_snd_injective Γ j p)]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (s := Γ j) (t := exponentSupport Γ j)
      (g := Prod.fst) (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      (fun a : (Fin r → ℤ) × (Fin (d + 1) → ℤ) => f a.1 a.2)

/-- Extending the sum to all new slices is justified, rather than assuming
the support remains fixed. -/
theorem full_weighted_exponentSlice_growth {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤ sliceRadius (exponentSlice Γ q 0))
    (j h : ℕ) (w : (Fin r → ℤ) → ℝ)
    (hh : H + h₀ ≤ h) (hr : 0 ≤ lam * h - (C + lam * h₀))
    (hw : ∀ p, 0 ≤ w p) :
    (∑ p ∈ exponentSupport Γ j, w p * sliceRadius (exponentSlice Γ j p) ^ (d + 2)) +
      (d + 2 : ℝ) * (lam * h - (C + lam * h₀)) *
        (∑ p ∈ exponentSupport Γ j, w p * sliceRadius (exponentSlice Γ j p) ^ (d + 1)) ≤
      ∑ p ∈ exponentSupport Γ (j + h),
        w p * sliceRadius (exponentSlice Γ (j + h) p) ^ (d + 2) := by
  classical
  have hsupport : exponentSupport Γ j ⊆ exponentSupport Γ (j + h) := by
    intro p hp
    have hp' := (mem_exponentSupport Γ j p).mp hp
    have hg := uniform_exponentSlice_radius_growth Γ hΓ H h₀ hcube hlam hH hlower
      j h p hh hp'
    have hpos := sliceRadius_pos hp'
    apply (mem_exponentSupport Γ (j + h) p).mpr
    apply nonempty_of_sliceRadius_pos
    linarith
  exact (weighted_exponentSlice_growth Γ hΓ H h₀ hcube hlam hH hlower
    j h (exponentSupport Γ j) w hh hr (fun p _ => hw p)
    (fun p hp => (mem_exponentSupport Γ j p).mp hp)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsupport
        (fun p _ _ => mul_nonneg (hw p) (pow_nonneg (sliceRadius_nonneg _) _)))

noncomputable def weightedSliceCount {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (w : (Fin r → ℤ) → ℝ) : ℝ :=
  ∑ p ∈ exponentSupport Γ j, w p * (exponentSlice Γ j p).card

theorem weightedSliceCount_eq_sum {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (w : (Fin r → ℤ) → ℝ) :
    weightedSliceCount Γ j w = ∑ a ∈ Γ j, w a.1 := by
  have h := sum_exponentSlices Γ j (fun p _ => w p)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm, weightedSliceCount] using h

theorem weightedSliceCount_one {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ))) (j : ℕ) :
    weightedSliceCount Γ j (fun _ => 1) = (Γ j).card := by
  rw [weightedSliceCount_eq_sum]
  simp

noncomputable def weightedSliceMoment {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (w : (Fin r → ℤ) → ℝ) : ℝ :=
  (∑ p ∈ exponentSupport Γ j, w p * sliceRadius (exponentSlice Γ j p) ^ (d + 2)) /
    ((d + 1).factorial : ℝ)

theorem weighted_sliceRadius_power_sum {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (j : ℕ) (w : (Fin r → ℤ) → ℝ) :
    (∑ p ∈ exponentSupport Γ j, w p * sliceRadius (exponentSlice Γ j p) ^ (d + 1)) =
      ((d + 1).factorial : ℝ) * weightedSliceCount Γ j w := by
  simp only [sliceRadius_power, weightedSliceCount, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- B_{j+h} >= B_j+(d+2)(lam*h-C')Q_j, in tangent dimension d+1. -/
theorem weightedSliceMoment_growth {r d : ℕ}
    (Γ : ℕ → Finset ((Fin r → ℤ) × (Fin (d + 1) → ℤ)))
    (hΓ : GradedExponentSemigroup Γ) (H h₀ : ℕ)
    (hcube : binaryVectors (d + 1) ⊆ exponentSlice Γ h₀ 0)
    {lam C : ℝ} (hlam : 0 ≤ lam) (hH : 0 < lam * H - C)
    (hlower : ∀ q ≥ H, lam * q - C ≤ sliceRadius (exponentSlice Γ q 0))
    (j h : ℕ) (w : (Fin r → ℤ) → ℝ)
    (hh : H + h₀ ≤ h) (hr : 0 ≤ lam * h - (C + lam * h₀))
    (hw : ∀ p, 0 ≤ w p) :
    weightedSliceMoment Γ j w + (d + 2 : ℝ) * (lam * h - (C + lam * h₀)) *
      weightedSliceCount Γ j w ≤ weightedSliceMoment Γ (j + h) w := by
  have hg := full_weighted_exponentSlice_growth Γ hΓ H h₀ hcube hlam hH hlower
    j h w hh hr hw
  rw [weighted_sliceRadius_power_sum] at hg
  have hf : 0 < ((d + 1).factorial : ℝ) := by positivity
  unfold weightedSliceMoment
  apply (le_div_iff₀ hf).mpr
  calc
    _ = (∑ p ∈ exponentSupport Γ j,
        w p * sliceRadius (exponentSlice Γ j p) ^ (d + 2)) +
      (d + 2 : ℝ) * (lam * h - (C + lam * h₀)) *
        (((d + 1).factorial : ℝ) * weightedSliceCount Γ j w) := by
      field_simp
    _ ≤ _ := hg

end MixedFujita
