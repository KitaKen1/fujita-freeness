/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
The forms of degree m in d + 1 variables have dimension (m + d).choose d: the exponents of
degree m are the finitely supported antidiagonal of m, counted by stars and bars. With a
fixed shift c, the dimension at m + c is asymptotically equivalent to m^d / d!.
-/

@[expose] public section

open MvPolynomial Finset Filter Asymptotics

namespace MixedFujita

variable (K : Type*) [Field K]

theorem finrank_homogeneousSubmodule_fin (d m : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin (d + 1)) K m) = (m + d).choose d := by
  classical
  have hset : {α : Fin (d + 1) →₀ ℕ | α.degree = m} =
      ↑((univ : Finset (Fin (d + 1))).finsuppAntidiag m) := by
    ext α
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum,
      subset_univ, and_true]
  rw [homogeneousSubmodule_eq_finsupp_supported, hset,
    LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp _), Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe]
  rw [card_finsuppAntidiag_nat_eq_choose, card_univ, Fintype.card_fin,
    show d + 1 + m - 1 = m + d by omega, Nat.choose_symm_add]

/-- With a fixed shift, (m + c + d).choose d is asymptotically m^d / d!. -/
theorem isEquivalent_choose_shift (d c : ℕ) :
    (fun m : ℕ => ((m + c + d).choose d : ℝ)) ~[atTop] (fun m : ℕ => (m ^ d / d.factorial : ℝ)) := by
  have h1 := (isEquivalent_choose d).comp_tendsto (tendsto_add_atTop_nat (c + d))
  have h2 : (fun m : ℕ => (((m + (c + d) : ℕ) : ℝ) ^ d / d.factorial)) ~[atTop]
      (fun m : ℕ => (m ^ d / d.factorial : ℝ)) := by
    refine IsEquivalent.div ?_ IsEquivalent.refl
    refine IsEquivalent.pow ?_ d
    have hz : ∀ᶠ m : ℕ in atTop, (m : ℝ) ≠ 0 :=
      eventually_atTop.mpr ⟨1, fun m hm => ne_of_gt (by exact_mod_cast hm)⟩
    rw [isEquivalent_iff_tendsto_one hz]
    have h := tendsto_natCast_div_add_atTop ((c + d : ℕ) : ℝ)
    have hinv : Tendsto (fun m : ℕ => ((m : ℝ) / (m + ((c + d : ℕ) : ℝ)))⁻¹) atTop (nhds 1) := by
      simpa using h.inv₀ one_ne_zero
    refine hinv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    simp only [Pi.div_apply, Nat.cast_add, inv_div]
  refine (h1.congr_left ?_).trans h2
  exact Eventually.of_forall fun m => by simp [Function.comp, add_assoc]

end MixedFujita
