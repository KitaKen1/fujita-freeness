/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.PWO
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Basic.Real.Basic

/-!
An actual Mathlib monomial order comparing real weight, then a natural-valued
degree, then a given monomial order. All real weights may be nonnegative,
including zero. Dickson's lemma supplies well-foundedness on the finite set
of variables, even though the ambient real lexicographic product is not
well-founded. No minimum-weight enumeration is needed.
-/

@[expose] public section

namespace MixedFujita

variable {σ : Type*} [Fintype σ]

noncomputable def realExponentWeight (w : σ → ℝ) : (σ →₀ ℕ) →+ ℝ where
  toFun a := ∑ i, w i * (a i : ℝ)
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

noncomputable def natExponentDegree (v : σ → ℕ) : (σ →₀ ℕ) →+ ℕ where
  toFun a := ∑ i, v i * a i
  map_zero' := by simp
  map_add' a b := by simp [mul_add, Finset.sum_add_distrib]

theorem realExponentWeight_monotone (w : σ → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Monotone (realExponentWeight w) := by
  intro a b hab
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hab i) (hw i)

theorem natExponentDegree_monotone (v : σ → ℕ) :
    Monotone (natExponentDegree v) := by
  intro a b hab
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (hab i)

noncomputable def weightedMonomialKey (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ) :
    (σ →₀ ℕ) →+ Lex (ℝ × Lex (ℕ × m.syn)) where
  toFun a := toLex (realExponentWeight w a, toLex (natExponentDegree v a, m.toSyn a))
  map_zero' := by simp
  map_add' a b := by simp [← toLex_add]

theorem weightedMonomialKey_injective (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ) :
    Function.Injective (weightedMonomialKey m w v) := by
  intro a b h
  exact m.toSyn.injective (congrArg (fun x => (ofLex (ofLex x).2).2) h)

theorem weightedMonomialKey_monotone (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) : Monotone (weightedMonomialKey m w v) := by
  intro a b hab
  apply Prod.Lex.toLex_le_toLex'.mpr
  refine ⟨realExponentWeight_monotone w hw hab, fun _ => ?_⟩
  exact Prod.Lex.toLex_le_toLex'.mpr
    ⟨natExponentDegree_monotone v hab, fun _ => m.toSyn_monotone hab⟩

/-- The exponent type with the order lifted from the three-level key. -/
def WeightedMonomialSyn (_m : MonomialOrder σ) (_w : σ → ℝ) (_v : σ → ℕ) := σ →₀ ℕ

noncomputable instance (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ) :
    AddCommMonoid (WeightedMonomialSyn m w v) :=
  (Equiv.refl (σ →₀ ℕ)).addCommMonoid

noncomputable instance (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ) :
    LinearOrder (WeightedMonomialSyn m w v) :=
  LinearOrder.lift' (weightedMonomialKey m w v) (weightedMonomialKey_injective m w v)

noncomputable def weightedMonomialToSyn (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ) :
    (σ →₀ ℕ) ≃+ WeightedMonomialSyn m w v where
  toEquiv := Equiv.refl _
  map_add' _ _ := rfl

noncomputable instance (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ) :
    IsOrderedAddMonoid (WeightedMonomialSyn m w v) where
  add_le_add_left a b hab c := by
    change weightedMonomialKey m w v ((weightedMonomialToSyn m w v).symm (a + c)) ≤
      weightedMonomialKey m w v ((weightedMonomialToSyn m w v).symm (b + c))
    change weightedMonomialKey m w v ((weightedMonomialToSyn m w v).symm a) ≤
      weightedMonomialKey m w v ((weightedMonomialToSyn m w v).symm b) at hab
    simp only [map_add]
    exact add_le_add hab le_rfl

theorem weightedMonomialToSyn_monotone (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) : Monotone (weightedMonomialToSyn m w v) :=
  weightedMonomialKey_monotone m w v hw

/-- Dickson's lemma transfers through the monotone identity to the lifted linear order. -/
theorem weightedMonomialSyn_wellFounded (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) : WellFoundedLT (WeightedMonomialSyn m w v) := by
  have hmono := weightedMonomialToSyn_monotone m w v hw
  have : WellQuasiOrderedLE (WeightedMonomialSyn m w v) :=
    hmono.wellQuasiOrderedLE_of_wellQuasiOrderedLE_of_surjective
      (weightedMonomialToSyn m w v).surjective
  infer_instance

noncomputable def weightedMonomialOrder (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) : MonomialOrder σ where
  syn := WeightedMonomialSyn m w v
  toSyn := weightedMonomialToSyn m w v
  toSyn_monotone := weightedMonomialToSyn_monotone m w v hw
  wellFoundedLT_syn := weightedMonomialSyn_wellFounded m w v hw

theorem weightedMonomialOrder_lt_iff (m : MonomialOrder σ) (w : σ → ℝ) (v : σ → ℕ)
    (hw : ∀ i, 0 ≤ w i) (a b : σ →₀ ℕ) :
    (weightedMonomialOrder m w v hw).toSyn a < (weightedMonomialOrder m w v hw).toSyn b ↔
      realExponentWeight w a < realExponentWeight w b ∨
        realExponentWeight w a = realExponentWeight w b ∧
          (natExponentDegree v a < natExponentDegree v b ∨
            natExponentDegree v a = natExponentDegree v b ∧ m.toSyn a < m.toSyn b) := by
  change weightedMonomialKey m w v a < weightedMonomialKey m w v b ↔ _
  simp only [weightedMonomialKey, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Prod.Lex.toLex_lt_toLex]

/-- A fixed final tie order exists on any finite variable type, including the empty type. -/
noncomputable def finiteLexMonomialOrder (ι : Type*) [Fintype ι] : MonomialOrder ι := by
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact MonomialOrder.lex

end MixedFujita
