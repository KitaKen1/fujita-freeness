/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.TwistedChartDISupport

/-!
The Deligne–Illusie map on Čech cochains (step 10).

The cover consists of étale charts `cs i`; a Čech intersection `U_x` carries the chart of its first
index (`cechEtaleChart`, check 442). Suppose given on every `U_x` a lift modulo `p²` with a family
of Frobenius lifts indexed by the vertices of `x`, the lifts of a face `x ∘ Fin.succAbove k`
mapping to those of `x` compatibly with the vertex map, and an equation of `D`.

For `i + a = b` and `q + a = q'` the **Deligne–Illusie map on Čech cochains**
`Ψ'^{b,a} : Č^q(Ω^b(D)) → Č^{q'}(Ω^i(p • D))` (`cechDIMap`) is
`(Ψ' y)_x = (-1)^{a q} Θ^{b,a}_{front}(y_{x_a … x_{q'}}|_{U_x})`:
the twisted Deligne–Illusie component of check 461 on `U_x`, evaluated at the front vertices
`x_0, …, x_a` (`cechFront`), of the restriction of `y` on the back face `x_a, …, x_{q'}`
(`cechBack`, through SGA's `cechMap`). Restricting a value on a face `x ∘ Fin.succAbove k` to `U_x`
gives the component on `U_x` at the face of the front vertices (`cechDIMap_face`, from checks 462
and 463).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X] [X.Over (Spec (CommRingCat.of K))]
  {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseOpenAlgebra functionFieldBaseAlgebra canonicalStalkFunctionFieldScalarTower
  canonicalOpenFunctionFieldScalarTower

/-- The front vertices `0, 1, …, q, q, …` of a simplex of length `q + 1`. -/
def cechFront (q : ℕ) : ℕ → Fin (q + 1) := fun t => ⟨min t q, by omega⟩

/-- The back face `a, a + 1, …, a + q` of a simplex of length `q' + 1`, `q + a = q'`. -/
def cechBack (a q q' : ℕ) (hq : q + a = q') : Fin (q + 1) → Fin (q' + 1) :=
  fun j => ⟨a + j, by omega⟩

theorem cechFront_val (q t : ℕ) : (cechFront q t : ℕ) = min t q := rfl

theorem cechBack_val (a q q' : ℕ) (hq : q + a = q') (j : Fin (q + 1)) :
    (cechBack a q q' hq j : ℕ) = a + j := rfl

section Cech

variable {N : ℕ} (cs : Fin N → EtaleChart K X n)
  (haff : ∀ q (x : Fin (q + 1) → Fin N),
    IsAffineOpen (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hne : ∀ q (x : Fin (q + 1) → Fin N),
    Nonempty (TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (L : ∀ q, (Fin (q + 1) → Fin N) → Type u) [∀ q x, CommRing (L q x)]
  (π : ∀ q x, L q x →+* Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))
  (hπ : ∀ q x, Function.Surjective (π q x)) (p : ℕ) [Fact p.Prime] [CharP K p]
  (F : ∀ q x, Fin (q + 1) → (L q x →+* L q x)) (hF : ∀ q x k y, π q x (F q x k y) = π q x y ^ p)
  (hker : ∀ q x y, π q x y = 0 → ∃ z, y = (p : L q x) * z)
  {D : CartierDivisor X} (g : ∀ q (_ : Fin (q + 1) → Fin N), X.functionFieldˣ)
  (hg : ∀ q x, ∀ y ∈ TopCat.Presheaf.cechOpen (fun i => (cs i).U) x,
    D.IsLocalEquationAt y (g q x))

/-- **The Deligne–Illusie map on Čech cochains**:
`(Ψ' y)_x = (-1)^{a q} Θ^{b,a}_{front}(y_{back}|_{U_x})`. -/
noncomputable def cechDIMap (b i a : ℕ) (h : i + a = b) (q q' : ℕ) (hq : q + a = q') :
    TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q →+
      TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K (p • D) i).presheaf q' :=
  AddMonoidHom.mk' (fun y x => (-1 : ℤ) ^ (a * q) • twistedChartDIComponent
    (cechEtaleChart cs haff hne q' x) (π q' x) (hπ q' x) p (F q' x) (hF q' x) (hker q' x) (hg q' x)
    b i a h (cechFront q')
    (TopCat.Presheaf.cechMap (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf
      (cechBack a q q' hq) y x)) fun y y' => by
    funext x
    rw [map_add, Pi.add_apply]
    rw [twistedChartDIComponent_add, smul_add]
    rfl

theorem cechDIMap_apply (b i a : ℕ) (h : i + a = b) (q q' : ℕ) (hq : q + a = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q' + 1) → Fin N) :
    cechDIMap cs haff hne L π hπ p F hF hker g hg b i a h q q' hq y x =
      (-1 : ℤ) ^ (a * q) • twistedChartDIComponent (cechEtaleChart cs haff hne q' x)
        (π q' x) (hπ q' x) p (F q' x) (hF q' x) (hker q' x) (hg q' x) b i a h (cechFront q')
        ((twistedFormsSheaf K D b).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp _ x
          (cechBack a q q' hq))).op (y (x ∘ cechBack a q q' hq))) :=
  rfl

theorem succAbove_cechFront_val (q : ℕ) (k : Fin (q + 2)) (t : ℕ) (ht : t ≤ q) :
    ((Fin.succAbove k (cechFront q t) : Fin (q + 2)) : ℕ) = cechFront (q + 1) (seqSkip k t) := by
  rw [cechFront_val, seqSkip]
  rcases lt_or_ge (Fin.castSucc (cechFront q t)) k with hk | hk
  · rw [Fin.succAbove_of_castSucc_lt k _ hk]
    have hk' : t < (k : ℕ) := by
      have := hk
      rw [Fin.lt_def, Fin.val_castSucc, cechFront_val] at this
      omega
    simp only [Fin.val_castSucc, cechFront_val, hk', ↓reduceIte]
    omega
  · rw [Fin.succAbove_of_le_castSucc k _ hk]
    have hk' : ¬ t < (k : ℕ) := by
      have := hk
      rw [Fin.le_def, Fin.val_castSucc, cechFront_val] at this
      omega
    simp only [Fin.val_succ, cechFront_val, hk', ↓reduceIte]
    omega

variable (R : ∀ q (x : Fin (q + 2) → Fin N) (k : Fin (q + 2)),
    L q (x ∘ Fin.succAbove k) →+* L (q + 1) x)
  (hR : ∀ q x k z, π (q + 1) x (R q x k z) =
    (X.presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs i).U) x
      (Fin.succAbove k))).op).hom (π q (x ∘ Fin.succAbove k) z))
  (hRF : ∀ q x k j z, R q x k (F q (x ∘ Fin.succAbove k) j z) =
    F (q + 1) x (Fin.succAbove k j) (R q x k z))
  (hann : ∀ q x z, (p : L q x) * z = 0 → π q x z = 0) (hp2 : ∀ q x, (p : L q x) * p = 0)
  (hK : ∀ q x (k : K), ∃ k' : L q x,
    π q x k' = algebraMap K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x) k ∧
      ∀ j, F q x j k' = k' ^ p)
  (hft : ∀ q (x : Fin (q + 1) → Fin N),
    Algebra.FiniteType K Γ(X, TopCat.Presheaf.cechOpen (fun i => (cs i).U) x))

include hR hRF hann hp2 hK hft in
/-- **Restricting a value of the map on a face**: the restriction to `U_x` of `(Ψ' y)_{x ∘ δ_k}`
is the component on `U_x` at the `k`-th face of the front vertices. -/
theorem cechDIMap_face (b i a : ℕ) (h : i + a = b) (q q' : ℕ) (hq : q + a = q')
    (y : TopCat.Presheaf.CechCochain (fun i => (cs i).U) (twistedFormsSheaf K D b).presheaf q)
    (x : Fin (q' + 2) → Fin N) (k : Fin (q' + 2)) :
    (twistedFormsSheaf K (p • D) i).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp
        (fun i => (cs i).U) x (Fin.succAbove k))).op
        (cechDIMap cs haff hne L π hπ p F hF hker g hg b i a h q q' hq y (x ∘ Fin.succAbove k)) =
      (-1 : ℤ) ^ (a * q) • twistedChartDIComponent (cechEtaleChart cs haff hne (q' + 1) x)
        (π (q' + 1) x) (hπ (q' + 1) x) p (F (q' + 1) x) (hF (q' + 1) x) (hker (q' + 1) x)
        (hg (q' + 1) x) b i a h (fun t => cechFront (q' + 1) (seqSkip k t))
        ((twistedFormsSheaf K D b).presheaf.map (homOfLE (TopCat.Presheaf.cechOpen_le_comp
          (fun i => (cs i).U) x (Fin.succAbove k ∘ cechBack a q q' hq))).op
          (y (x ∘ (Fin.succAbove k ∘ cechBack a q q' hq)))) := by
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne q' (x ∘ Fin.succAbove k)).U) :=
    hft q' (x ∘ Fin.succAbove k)
  have : Algebra.FiniteType K Γ(X, (cechEtaleChart cs haff hne (q' + 1) x).U) := hft (q' + 1) x
  rw [cechDIMap_apply, map_zsmul]
  congr 1
  refine (twistedChartDIComponent_restrict (cechEtaleChart cs haff hne q' (x ∘ Fin.succAbove k))
    (cechEtaleChart cs haff hne (q' + 1) x)
    (TopCat.Presheaf.cechOpen_le_comp (fun i => (cs i).U) x (Fin.succAbove k))
    (π q' (x ∘ Fin.succAbove k)) (hπ q' _) (π (q' + 1) x) (hπ (q' + 1) x) p
    (F q' (x ∘ Fin.succAbove k)) (hF q' _) (F (q' + 1) x) (hF (q' + 1) x) (hker q' _)
    (hker (q' + 1) x) (hann q' _) (hp2 q' _) (hann (q' + 1) x) (hp2 (q' + 1) x) (hK q' _)
    (hK (q' + 1) x) (R q' x k) (hR q' x k) (Fin.succAbove k) (hRF q' x k)
    (hg q' (x ∘ Fin.succAbove k)) (hg (q' + 1) x) b i a h (cechFront q') _).trans ?_
  refine (twistedChartDIComponent_congr (cechEtaleChart cs haff hne (q' + 1) x) (π (q' + 1) x)
    (hπ (q' + 1) x) p (F (q' + 1) x) (hF (q' + 1) x) (hker (q' + 1) x) (hg (q' + 1) x) b i a h
    (s := Fin.succAbove k ∘ cechFront q') (t := fun t => cechFront (q' + 1) (seqSkip k t))
    (fun t ht => Fin.ext (succAbove_cechFront_val q' k t (by omega))) _).trans ?_
  congr 1

end Cech

end MixedFujita
