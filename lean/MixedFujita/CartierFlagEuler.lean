/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ClosedImmersionEuler
public import MixedFujita.BoundedEulerDifference

/-!
A finite family of actual schemes and Cartier sheaves has the binomial Euler
formula when each quotient is identified with the actual next closed-immersion
pushforward and each negative twist with the next column. These are sheaf
isomorphisms, not assumed Euler recurrences. Finiteness and top-degree vanishing
are needed only in the finite triangle. This does not construct a Bertini flag
or prove geometric finiteness, vanishing, or its uniform intersection degree.
-/

@[expose] public section
open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]

theorem cartierCut_eulerRecurrence_of_sheaf_isos
    (D E F : CartierDivisor X) (hE : E.IsEffective)
    (f : Y ⟶ X) [IsClosedImmersion f] [f.IsOver (Spec (CommRingCat.of K))]
    (M : Y.Modules) (eShift : (D - E).sheaf ≅ F.sheaf)
    (eCut : (cartierCutShortComplex D E hE).X₃ ≅
      (Scheme.Modules.pushforward f).obj M) (n : ℕ)
    (hF : ∀ q < n, 0 < q → FiniteDimensional K (Scheme.Modules.Cohomology F.sheaf q))
    (hD : ∀ q < n, FiniteDimensional K (Scheme.Modules.Cohomology D.sheaf q))
    (hvan : Subsingleton (Scheme.Modules.Cohomology F.sheaf n)) :
    Scheme.Modules.eulerCharBelow K Y M n =
      Scheme.Modules.eulerCharBelow K X D.sheaf n -
        Scheme.Modules.eulerCharBelow K X F.sheaf n := by
  have hDE (q : ℕ) (hq : q < n) (hq0 : 0 < q) :
      FiniteDimensional K (Scheme.Modules.Cohomology (D - E).sheaf q) :=
    (Scheme.Modules.finiteDimensional_cohomology_congr K eShift q).mpr (hF q hq hq0)
  have hv : Subsingleton (Scheme.Modules.Cohomology (D - E).sheaf n) := by
    let := hvan
    exact (Scheme.Modules.cohomologyBaseLinearEquivOfIso K eShift n).subsingleton
  have h := cartierCut_eulerCharBelow_eq_sub D E hE n hDE hD hv
  change Scheme.Modules.eulerCharBelow K X (cartierCutShortComplex D E hE).X₃ n = _ at h
  rw [Scheme.Modules.eulerCharBelow_congr K eCut n,
    closedImmersion_eulerCharBelow_eq f K M n,
    Scheme.Modules.eulerCharBelow_congr K eShift n] at h
  exact h

theorem cartierCut_negativeGradedEulerRecurrence
    (D E : CartierDivisor X) (hE : E.IsEffective)
    [(effectiveCartierIdealSheaf E hE).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf E hE).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (j n : ℕ)
    (hF : ∀ q < n, 0 < q → FiniteDimensional K
      (Scheme.Modules.Cohomology (D - (j + 1) • E).sheaf q))
    (hD : ∀ q < n, FiniteDimensional K
      (Scheme.Modules.Cohomology (D - j • E).sheaf q))
    (hvan : Subsingleton (Scheme.Modules.Cohomology (D - (j + 1) • E).sheaf n)) :
    Scheme.Modules.eulerCharBelow K (effectiveCartierIdealSheaf E hE).subscheme
      ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj
        (D - j • E).sheaf) n =
      Scheme.Modules.eulerCharBelow K X (D - j • E).sheaf n -
        Scheme.Modules.eulerCharBelow K X (D - (j + 1) • E).sheaf n := by
  apply cartierCut_eulerRecurrence_of_sheaf_isos (D - j • E) E
    (D - (j + 1) • E) hE (effectiveCartierIdealSheaf E hE).subschemeι
    _ (eqToIso (congrArg CartierDivisor.sheaf (by
      rw [succ_nsmul, sub_add_eq_sub_sub]))) (Iso.refl _) n hF hD hvan

variable (N : ℕ) (X : Fin (N + 1) → Scheme.{u})
  [∀ r, IsIntegral (X r)] [∀ r, (X r).Over (Spec (CommRingCat.of K))]

noncomputable def finiteCartierFlagEuler
    (D : ∀ r, ℕ → CartierDivisor (X r)) (n r j : ℕ) : ℤ :=
  if h : r ≤ N then
    Scheme.Modules.eulerCharBelow K (X ⟨r, Nat.lt_succ_of_le h⟩)
      (D ⟨r, Nat.lt_succ_of_le h⟩ j).sheaf n
  else 0

theorem finiteCartierFlagEuler_at
    (D : ∀ r, ℕ → CartierDivisor (X r)) (n : ℕ) (r : Fin (N + 1)) (j : ℕ) :
    finiteCartierFlagEuler (K := K) N X D n r.val j =
      Scheme.Modules.eulerCharBelow K (X r) (D r j).sheaf n := by
  simp only [finiteCartierFlagEuler, dite_eq_left (Nat.le_of_lt_succ r.isLt)]

theorem finiteCartierFlagEuler_binomial
    (D : ∀ r, ℕ → CartierDivisor (X r))
    (E : ∀ r : Fin N, CartierDivisor (X r.castSucc))
    (hE : ∀ r, (E r).IsEffective)
    (f : ∀ r : Fin N, X r.succ ⟶ X r.castSucc)
    [∀ r, IsClosedImmersion (f r)] [∀ r, (f r).IsOver (Spec (CommRingCat.of K))]
    (eShift : ∀ (r : Fin N) (j : ℕ) (_ : r.val + j < N),
      ((D r.castSucc j - E r).sheaf ≅ (D r.castSucc (j + 1)).sheaf))
    (eCut : ∀ (r : Fin N) (j : ℕ) (_ : r.val + j < N),
      ((cartierCutShortComplex (D r.castSucc j) (E r) (hE r)).X₃ ≅
        (Scheme.Modules.pushforward (f r)).obj (D r.succ j).sheaf))
    (n : ℕ)
    (hFinite : ∀ (r : Fin (N + 1)) j, r.val + j ≤ N → ∀ q < n,
      FiniteDimensional K (Scheme.Modules.Cohomology (D r j).sheaf q))
    (hvan : ∀ (r : Fin N) j, r.val + j < N →
      Subsingleton (Scheme.Modules.Cohomology (D r.castSucc (j + 1)).sheaf n)) :
    Scheme.Modules.eulerCharBelow K (X (Fin.last N)) (D (Fin.last N) 0).sheaf n =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (N.choose k : ℤ) *
        Scheme.Modules.eulerCharBelow K (X 0) (D 0 k).sheaf n := by
  let c := finiteCartierFlagEuler (K := K) N X D n
  have hc (r j : ℕ) (hrj : r + j < N) : c (r + 1) j = c r j - c r (j + 1) := by
    let a : Fin N := ⟨r, by omega⟩
    change finiteCartierFlagEuler (K := K) N X D n a.succ.val j =
      finiteCartierFlagEuler (K := K) N X D n a.castSucc.val j -
        finiteCartierFlagEuler (K := K) N X D n a.castSucc.val (j + 1)
    rw [finiteCartierFlagEuler_at, finiteCartierFlagEuler_at, finiteCartierFlagEuler_at]
    exact cartierCut_eulerRecurrence_of_sheaf_isos
      (D a.castSucc j) (E a) (D a.castSucc (j + 1)) (hE a) (f a)
      (D a.succ j).sheaf (eShift a j hrj) (eCut a j hrj) n
      (fun q hq _ ↦ hFinite a.castSucc (j + 1) (by change r + (j + 1) ≤ N; omega) q hq)
      (hFinite a.castSucc j (by change r + j ≤ N; omega)) (hvan a j hrj)
  have h0 (j : ℕ) : c 0 j =
      Scheme.Modules.eulerCharBelow K (X 0) (D 0 j).sheaf n :=
    finiteCartierFlagEuler_at (K := K) N X D n (0 : Fin (N + 1)) j
  have h := boundedEulerCut_binomial N c hc N 0 (by omega)
  change finiteCartierFlagEuler (K := K) N X D n (Fin.last N).val 0 = _ at h
  rw [finiteCartierFlagEuler_at] at h
  simpa only [Nat.zero_add, h0] using h

end MixedFujita
