/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.ProperCartierCohomology

/-! For actual Cartier cuts on proper schemes, cohomology finiteness is internally supplied. The Euler recurrence and binomial flag formula require only the actual sheaf comparisons and a geometric dimension bound; neither finite-dimensionality nor cohomological vanishing is an extra premise. Construction of a Bertini flag and Kawamata--Viehweg vanishing remain separate obligations. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {X Y : Scheme.{u}} [IsIntegral X]
  [X.Over (Spec (CommRingCat.of K))] [Y.Over (Spec (CommRingCat.of K))]
  [IsProper (X ↘ Spec (CommRingCat.of K))]

theorem proper_cartierCut_cohomology_finite
    (D E : CartierDivisor X) (hE : E.IsEffective)
    (f : Y ⟶ X) [IsClosedImmersion f] [f.IsOver (Spec (CommRingCat.of K))]
    (M : Y.Modules)
    (eCut : (cartierCutShortComplex D E hE).X₃ ≅ (Scheme.Modules.pushforward f).obj M)
    (q : ℕ) : FiniteDimensional K (Scheme.Modules.Cohomology M q) := by
  have h := shortExact_cohomology_quotient_finite
    (cartierCutShortComplex_shortExact D E hE) q
    (proper_cartier_cohomology_finite K D q)
    (proper_cartier_cohomology_finite K (D - E) (q + 1))
  have hpush := (Scheme.Modules.finiteDimensional_cohomology_congr K eCut q).mp h
  exact (closedImmersion_cohomology_finite_iff f K M q).mp hpush

theorem proper_cartierCut_eulerRecurrence_of_sheaf_isos
    (D E F : CartierDivisor X) (hE : E.IsEffective)
    (f : Y ⟶ X) [IsClosedImmersion f] [f.IsOver (Spec (CommRingCat.of K))]
    (M : Y.Modules) (eShift : (D - E).sheaf ≅ F.sheaf)
    (eCut : (cartierCutShortComplex D E hE).X₃ ≅ (Scheme.Modules.pushforward f).obj M)
    (n : ℕ) (hn : topologicalKrullDim X < n) :
    Scheme.Modules.eulerCharBelow K Y M n =
      Scheme.Modules.eulerCharBelow K X D.sheaf n -
        Scheme.Modules.eulerCharBelow K X F.sheaf n := by
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  exact cartierCut_eulerRecurrence_of_sheaf_isos D E F hE f M eShift eCut n
    (fun q _ _ => proper_cartier_cohomology_finite K F q)
    (fun q _ => proper_cartier_cohomology_finite K D q)
    (actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt F.sheaf n hn)

theorem proper_cartierCut_negativeGradedEulerRecurrence
    (D E : CartierDivisor X) (hE : E.IsEffective)
    [(effectiveCartierIdealSheaf E hE).subscheme.Over (Spec (CommRingCat.of K))]
    [(effectiveCartierIdealSheaf E hE).subschemeι.IsOver (Spec (CommRingCat.of K))]
    (j n : ℕ) (hn : topologicalKrullDim X < n) :
    Scheme.Modules.eulerCharBelow K (effectiveCartierIdealSheaf E hE).subscheme
      ((Scheme.Modules.pullback (effectiveCartierIdealSheaf E hE).subschemeι).obj
        (D - j • E).sheaf) n =
      Scheme.Modules.eulerCharBelow K X (D - j • E).sheaf n -
        Scheme.Modules.eulerCharBelow K X (D - (j + 1) • E).sheaf n := by
  letI := properOverField_scheme_isNoetherian (K := K) (X := X)
  exact cartierCut_negativeGradedEulerRecurrence D E hE j n
    (fun q _ _ => proper_cartier_cohomology_finite K _ q)
    (fun q _ => proper_cartier_cohomology_finite K _ q)
    (actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt _ n hn)

theorem proper_finiteCartierFlagEuler_binomial
    (N : ℕ) (X : Fin (N + 1) → Scheme.{u})
    [∀ r, IsIntegral (X r)] [∀ r, (X r).Over (Spec (CommRingCat.of K))]
    [∀ r, IsProper (X r ↘ Spec (CommRingCat.of K))]
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
    (n : ℕ) (hn : ∀ r, topologicalKrullDim (X r) < n) :
    Scheme.Modules.eulerCharBelow K (X (Fin.last N)) (D (Fin.last N) 0).sheaf n =
      ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (N.choose k : ℤ) *
        Scheme.Modules.eulerCharBelow K (X 0) (D 0 k).sheaf n := by
  letI (r : Fin (N + 1)) : IsNoetherian (X r) :=
    properOverField_scheme_isNoetherian (K := K) (X := X r)
  exact finiteCartierFlagEuler_binomial N X D E hE f eShift eCut n
    (fun r j _ q _ => proper_cartier_cohomology_finite K (D r j) q)
    (fun r j _ => actualModuleCohomology_subsingleton_of_topologicalKrullDim_lt
      (D r.castSucc (j + 1)).sheaf n (hn r.castSucc))

end MixedFujita

