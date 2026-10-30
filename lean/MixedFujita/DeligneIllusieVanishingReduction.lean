/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedFormsTensor
public import MixedFujita.SGACohomologyComparison

/-!
Vanishing from the Deligne–Illusie dimension inequality (step 10).

On a proper integral scheme over `K` covered by étale charts, the cohomology of `Ω^b_X(E)` is
finite-dimensional (`twistedFormsSheaf_cohomology_finite`, from its coherence, check-419, and the
SGA finiteness theorem). The Cartier isomorphism is semilinear for the Frobenius of `K`; over a
perfect field a Frobenius-semilinear bijection preserves dimensions
(`finrank_eq_of_frobenius_semilinear`), so the dimension count does not see the Frobenius twist.

Write `twistedHodgeCount D n m = Σ_{i ≤ n} h^{m - i}(Ω^i_X(D))`. The Deligne–Illusie decomposition
of `F_* Ω^•_X(p D)` together with the filtration of its hypercohomology gives the inequality
`twistedHodgeCount D n m ≤ twistedHodgeCount (p D) n m` (`DeligneIllusieInequality`, the part of
step 10 still to be done). Iterating it (`twistedHodgeCount_le_pow`) and applying Serre vanishing to
`Ω^i_X(p^k D)` for `D` ample (`exists_twistedHodgeCount_eq_zero`) gives
**`H^j(Ω^b_X(D)) = 0` for `b ≤ n` and `b + j > n`**
(`twistedFormsSheaf_vanishing_of_deligneIllusie`), Akizuki–Nakano vanishing; for `b = n` it is
Kodaira vanishing for `Ω^n_X(D)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u v

section Frobenius

variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]
  {V W : Type v} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **A Frobenius-semilinear bijection preserves dimensions** over a perfect field. -/
theorem rank_eq_of_frobenius_semilinear (f : V ≃+ W) (hf : ∀ (c : K) (v : V), f (c • v) = c ^ p • f v) :
    Module.rank K V = Module.rank K W :=
  rank_eq_of_equiv_equiv (frobenius K p) f (bijective_frobenius K p)
    (fun c v => by rw [frobenius_def]; exact hf c v)

theorem finrank_eq_of_frobenius_semilinear (f : V ≃+ W)
    (hf : ∀ (c : K) (v : V), f (c • v) = c ^ p • f v) :
    Module.finrank K V = Module.finrank K W := by
  rw [Module.finrank, Module.finrank, rank_eq_of_frobenius_semilinear p f hf]

theorem finiteDimensional_of_frobenius_semilinear (f : V ≃+ W)
    (hf : ∀ (c : K) (v : V), f (c • v) = c ^ p • f v) [FiniteDimensional K W] :
    FiniteDimensional K V := by
  have h : Module.rank K V < Cardinal.aleph0 := by
    rw [rank_eq_of_frobenius_semilinear p f hf]
    exact Module.rank_lt_aleph0 K W
  exact Module.rank_lt_aleph0_iff.mp h

end Frobenius

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]

/-- **The cohomology of `Ω^b_X(E)` is finite-dimensional** on a proper integral scheme covered by
étale charts. -/
theorem twistedFormsSheaf_cohomology_finite {n : ℕ} [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (E : CartierDivisor X) (b i : ℕ) :
    Module.Finite K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (twistedFormsSheaf K E b) i) := by
  have := isCoherent_twistedFormsSheaf hcover E b
  exact proper_coherent_cohomology_finite K (twistedFormsSheaf K E b) i

/-- The cohomology of `Ω^b_X` is finite-dimensional on a proper integral scheme covered by étale
charts. -/
theorem differentialFormsSheaf_cohomology_finite {n : ℕ} [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (b i : ℕ) :
    Module.Finite K
      (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (differentialFormsSheaf K (X := X) b) i) := by
  have := isCoherent_differentialFormsSheaf hcover b
  exact proper_coherent_cohomology_finite K (differentialFormsSheaf K (X := X) b) i

variable (K) in
/-- The dimension count `Σ_{i ≤ n} h^{m - i}(Ω^i_X(D))` of total degree `m`. -/
noncomputable def twistedHodgeCount (D : CartierDivisor X) (n m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), Module.finrank K
    (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (twistedFormsSheaf K D i) (m - i))

variable (K) in
/-- **The Deligne–Illusie dimension inequality** for `D` in total degree `m`:
`Σ_{i ≤ n} h^{m - i}(Ω^i(D)) ≤ Σ_{i ≤ n} h^{m - i}(Ω^i(p D))`. -/
def DeligneIllusieInequality (D : CartierDivisor X) (p n m : ℕ) : Prop :=
  twistedHodgeCount K D n m ≤ twistedHodgeCount K (p • D) n m

/-- Iterating the Deligne–Illusie inequality along `D, p D, p² D, …`. -/
theorem twistedHodgeCount_le_pow (D : CartierDivisor X) (p n m : ℕ)
    (hDI : ∀ k, DeligneIllusieInequality K ((p ^ k) • D) p n m) (k : ℕ) :
    twistedHodgeCount K D n m ≤ twistedHodgeCount K ((p ^ k) • D) n m := by
  induction k with
  | zero => rw [pow_zero, one_smul]
  | succ k ih =>
    refine ih.trans ?_
    have h := hDI k
    rwa [DeligneIllusieInequality, smul_smul, ← pow_succ'] at h

/-- **Serre vanishing kills the dimension count in total degrees `m > n`** for large multiples of
an ample divisor. -/
theorem exists_twistedHodgeCount_eq_zero {n : ℕ}
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (D : CartierDivisor X)
    (hD : CartierIsAmpleProj K D) (m : ℕ) (hm : n < m) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, twistedHodgeCount K (M • D) n m = 0 := by
  choose m₀ hm₀ using fun i => twistedFormsSheaf_serreVanishing hcover D hD i
  refine ⟨(Finset.range (n + 1)).sup m₀, fun M hM => Finset.sum_eq_zero fun i hi => ?_⟩
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  have hM' : M ≥ m₀ i := le_trans (Finset.le_sup hi) hM
  obtain ⟨q, hq⟩ : ∃ q, m - i = q + 1 := ⟨m - i - 1, by omega⟩
  rw [hq]
  have := hm₀ i M hM' q
  exact Module.finrank_zero_of_subsingleton

/-- **Vanishing from the Deligne–Illusie inequality**: if the inequality holds for the multiples
`p^k D` of an ample `D` in every total degree `m > n`, then `H^j(Ω^b_X(D)) = 0` for `b ≤ n` and
`b + j > n` (Akizuki–Nakano; Kodaira vanishing for `Ω^n_X(D)` when `b = n`). -/
theorem twistedFormsSheaf_vanishing_of_deligneIllusie {n : ℕ}
    [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hcover : iSup (fun c : EtaleChart K X n => c.U) = ⊤) (p : ℕ) (hp : 2 ≤ p)
    (D : CartierDivisor X) (hD : CartierIsAmpleProj K D)
    (hDI : ∀ k m, n < m → DeligneIllusieInequality K ((p ^ k) • D) p n m)
    {b j : ℕ} (hb : b ≤ n) (hbj : n < b + j) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (twistedFormsSheaf K D b) j) := by
  obtain ⟨M₀, hM₀⟩ := exists_twistedHodgeCount_eq_zero hcover D hD (b + j) hbj
  have hk : M₀ ≤ p ^ M₀ := (Nat.lt_pow_self (by omega : 1 < p)).le
  have h0 : twistedHodgeCount K D n (b + j) = 0 :=
    Nat.eq_zero_of_le_zero ((twistedHodgeCount_le_pow D p n (b + j)
      (fun k => hDI k (b + j) hbj) M₀).trans (hM₀ _ hk).le)
  have hterm := (Finset.sum_eq_zero_iff.mp h0) b (Finset.mem_range.mpr (by omega))
  rw [show b + j - b = j by omega] at hterm
  have := twistedFormsSheaf_cohomology_finite hcover D b j
  exact Module.finrank_zero_iff.mp hterm

end MixedFujita
