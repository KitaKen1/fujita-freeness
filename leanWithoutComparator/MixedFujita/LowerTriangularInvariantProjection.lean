/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ValuationSubringIwasawa
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic

/-!
The projection to K^m of a zero set in K^m × K^(N×N), restricted to invertible matrices and
invariant under lower triangular changes of the rows of the matrix, is Zariski closed, over an
algebraically closed field (`exists_matrix_of_vanishing_of_lowerTriangular_invariant`): the
properness of the flag variety in the form of polynomials.

Let x₀ lie in the closure of the projection. The ideal of the zero set with the inverse of the
determinant adjoined (Rabinowitsch) has finitely many minimal primes; one of them, 𝔓, meets the
polynomials in x only inside the maximal ideal of x₀ (otherwise a product of polynomials, one
from each minimal prime, vanishes on the projection but not at x₀). In the fraction field F of
the quotient by 𝔓, the local ring of x₀ is dominated by a valuation subring R. The generic
matrix c_F has an integral form L c_F with unit determinant over R (Iwasawa decomposition,
`exists_isLowerTriangular_mul_integral`), and (x_F, L c_F) is still a zero of the ideal, by the
invariance at the K-points and the Nullstellensatz. Reducing modulo the maximal ideal of R gives
a point of the zero set over x₀ with invertible matrix in an extension of K, so the ideal is
proper and has a K-point over x₀.
-/

@[expose] public section

namespace MixedFujita

open MvPolynomial

variable {K : Type*} [Field K]

/-- The point (x, c) of K^m × K^(N×N). -/
def matrixPoint {B : Type*} {m N : ℕ} (x : Fin m → B) (c : Matrix (Fin N) (Fin N) B) :
    Fin m ⊕ (Fin N × Fin N) → B :=
  Sum.elim x fun ij => c ij.1 ij.2

/-- The determinant of the matrix of the variables c. -/
noncomputable def matrixVariableDet (K : Type*) [Field K] (m N : ℕ) :
    MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K :=
  (Matrix.of fun i j => (X (Sum.inr (i, j)) : MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K)).det

theorem aeval_matrixVariableDet {B : Type*} [CommRing B] [Algebra K B] {m N : ℕ}
    (P : Fin m ⊕ (Fin N × Fin N) → B) :
    aeval P (matrixVariableDet K m N) = (Matrix.of fun i j => P (Sum.inr (i, j))).det := by
  rw [matrixVariableDet, AlgHom.map_det]
  congr 1
  ext i j
  simp

/-- The ideal of the zero set of J with the inverse of the determinant adjoined. -/
noncomputable def rabinowitschIdeal {m N : ℕ} (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K)) :
    Ideal (MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K) :=
  Ideal.map (rename some) J ⊔
    Ideal.span {X none * rename some (matrixVariableDet K m N) - 1}

theorem rabinowitschIdeal_le_ker_iff {B : Type*} [CommRing B] {m N : ℕ}
    (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K))
    (φ : MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K →+* B) :
    rabinowitschIdeal J ≤ RingHom.ker φ ↔
      (∀ g ∈ J, φ (rename some g) = 0) ∧ φ (X none) * φ (rename some (matrixVariableDet K m N)) = 1 := by
  rw [rabinowitschIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem,
    RingHom.mem_ker, map_sub, map_mul, map_one, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g hg => h1 hg, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun g hg => h1 g hg, h2⟩

/-- The K-points of the Rabinowitsch ideal. -/
theorem mem_zeroLocus_rabinowitschIdeal_iff {m N : ℕ}
    (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K))
    (q : Option (Fin m ⊕ (Fin N × Fin N)) → K) :
    q ∈ zeroLocus K (rabinowitschIdeal J) ↔
      q ∘ some ∈ zeroLocus K J ∧
        q none * (Matrix.of fun i j => q (some (Sum.inr (i, j)))).det = 1 := by
  have h := rabinowitschIdeal_le_ker_iff J (aeval q).toRingHom
  have hker : rabinowitschIdeal J ≤ RingHom.ker (aeval q).toRingHom ↔
      q ∈ zeroLocus K (rabinowitschIdeal J) := by
    constructor
    · intro hle p hp
      exact hle hp
    · intro hq p hp
      exact hq p hp
  rw [← hker, h]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename, aeval_X,
    aeval_matrixVariableDet, mem_zeroLocus_iff]
  rfl

/-- A proper ideal has a K-point (the weak Nullstellensatz). -/
theorem exists_mem_zeroLocus_of_ne_top [IsAlgClosed K] {σ : Type*} [Finite σ]
    {I : Ideal (MvPolynomial σ K)} (hI : I ≠ ⊤) : ∃ q : σ → K, q ∈ zeroLocus K I := by
  by_contra hno
  push Not at hno
  have hempty : zeroLocus K I = ∅ := Set.eq_empty_iff_forall_notMem.mpr hno
  have h := vanishingIdeal_zeroLocus_eq_radical (K := K) I
  rw [hempty, vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at h
  exact hI h

section Projection

/-- Some minimal prime of the Rabinowitsch ideal meets the polynomials in x only inside the
maximal ideal of a point x₀ of the closure of the projection. -/
theorem exists_minimalPrime_of_vanishing {m N : ℕ}
    (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K)) (x₀ : Fin m → K)
    (hx₀ : ∀ f : MvPolynomial (Fin m) K,
      (∀ x, (∃ c : Matrix (Fin N) (Fin N) K, c.det ≠ 0 ∧ matrixPoint x c ∈ zeroLocus K J) →
        eval x f = 0) → eval x₀ f = 0) :
    ∃ 𝔓 ∈ (rabinowitschIdeal J).minimalPrimes,
      ∀ f : MvPolynomial (Fin m) K, rename (some ∘ Sum.inl) f ∈ 𝔓 → eval x₀ f = 0 := by
  classical
  by_contra hno
  push Not at hno
  choose f hf hfx using hno
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K) (rabinowitschIdeal J)
  set F₀ : MvPolynomial (Fin m) K := ∏ 𝔓 ∈ hfin.toFinset.attach,
    f 𝔓.1 (hfin.mem_toFinset.mp 𝔓.2) with hF₀
  have hne : eval x₀ F₀ ≠ 0 := by
    rw [hF₀, map_prod, Finset.prod_ne_zero_iff]
    intro 𝔓 _
    exact hfx _ _
  apply hne
  apply hx₀
  rintro x ⟨c, hc, hxc⟩
  set q : Option (Fin m ⊕ (Fin N × Fin N)) → K := fun o => Option.elim o (c.det)⁻¹ (matrixPoint x c)
    with hq
  have hqz : q ∈ zeroLocus K (rabinowitschIdeal J) := by
    rw [mem_zeroLocus_rabinowitschIdeal_iff]
    refine ⟨hxc, ?_⟩
    have hmat : (Matrix.of fun i j => q (some (Sum.inr (i, j)))) = c := by
      ext i j
      rfl
    rw [hmat]
    exact inv_mul_cancel₀ hc
  have hle : rabinowitschIdeal J ≤ vanishingIdeal K {q} :=
    (le_vanishingIdeal_zeroLocus (K := K) _).trans
      (vanishingIdeal_anti_mono (Set.singleton_subset_iff.mpr hqz))
  obtain ⟨𝔓, h𝔓, h𝔓le⟩ := Ideal.exists_minimalPrimes_le hle
  rw [hF₀, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_attach _ ⟨𝔓, hfin.mem_toFinset.mpr h𝔓⟩)
  have h1 := h𝔓le (hf 𝔓 h𝔓)
  rw [mem_vanishingIdeal_singleton_iff, aeval_rename] at h1
  exact h1

variable [IsAlgClosed K]

section Invariance

variable {m N : ℕ}

/-- The variables x, c, the lower triangular matrix ℓ and the inverses of det c and det ℓ. -/
@[reducible]
def InvariantVars (m N : ℕ) : Type := Fin m ⊕ (Fin N × Fin N) ⊕ (Fin N × Fin N) ⊕ Bool

/-- The original variables x and c among the invariance variables. -/
def invariantOrig : Fin m ⊕ (Fin N × Fin N) → InvariantVars m N :=
  Sum.elim Sum.inl fun ij => Sum.inr (Sum.inl ij)

/-- The substitution c ↦ ℓ c. -/
noncomputable def invariantSubst : Fin m ⊕ (Fin N × Fin N) → MvPolynomial (InvariantVars m N) K :=
  Sum.elim (fun i => X (Sum.inl i)) fun ij =>
    ∑ k, X (Sum.inr (Sum.inr (Sum.inl (ij.1, k)))) * X (Sum.inr (Sum.inl (k, ij.2)))

/-- The relations of the invariance variables: ℓ lower triangular, inverses of the
determinants. -/
def invariantRelations (K : Type*) [Field K] (m N : ℕ) : Set (MvPolynomial (InvariantVars m N) K) :=
  {p | ∃ ij : Fin N × Fin N, ij.1 < ij.2 ∧ p = X (Sum.inr (Sum.inr (Sum.inl ij)))} ∪
    {X (Sum.inr (Sum.inr (Sum.inr false))) *
        (Matrix.of fun i j => (X (Sum.inr (Sum.inl (i, j))) : MvPolynomial (InvariantVars m N) K)).det - 1,
      X (Sum.inr (Sum.inr (Sum.inr true))) *
        (Matrix.of fun i j =>
          (X (Sum.inr (Sum.inr (Sum.inl (i, j)))) : MvPolynomial (InvariantVars m N) K)).det - 1}

/-- The ideal of the invariance test. -/
noncomputable def invariantTestIdeal (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K)) :
    Ideal (MvPolynomial (InvariantVars m N) K) :=
  Ideal.map (rename invariantOrig) J ⊔ Ideal.span (invariantRelations K m N)

omit [IsAlgClosed K] in
theorem invariantTestIdeal_le_ker_iff {B : Type*} [CommRing B]
    (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K))
    (φ : MvPolynomial (InvariantVars m N) K →+* B) :
    invariantTestIdeal J ≤ RingHom.ker φ ↔
      (∀ g ∈ J, φ (rename invariantOrig g) = 0) ∧ ∀ s ∈ invariantRelations K m N, φ s = 0 := by
  rw [invariantTestIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g hg => h1 hg, fun s hs => h2 hs⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun g hg => h1 g hg, fun s hs => h2 s hs⟩

omit [IsAlgClosed K] in
/-- The substituted polynomial evaluates to the polynomial at (x, ℓ c). -/
theorem aeval_invariantSubst {B : Type*} [CommRing B] [Algebra K B] (w : InvariantVars m N → B)
    (g : MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K) :
    aeval w (aeval (invariantSubst (K := K)) g) =
      aeval (matrixPoint (fun i => w (Sum.inl i))
        ((Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inl (i, j))))) *
          Matrix.of fun i j => w (Sum.inr (Sum.inl (i, j))))) g := by
  rw [MvPolynomial.comp_aeval_apply]
  congr 2
  funext v
  cases v with
  | inl i => simp [invariantSubst, matrixPoint]
  | inr ij => simp [invariantSubst, matrixPoint, Matrix.mul_apply]

/-- The invariance of the zero set at the K-points passes to every field: (x, L c) is a zero of J
whenever (x, c) is, for L lower triangular and invertible. -/
theorem aeval_eq_zero_of_lowerTriangular_invariant
    (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K))
    (hinv : ∀ (x : Fin m → K) (c : Matrix (Fin N) (Fin N) K), matrixPoint x c ∈ zeroLocus K J →
      c.det ≠ 0 → ∀ L : Matrix (Fin N) (Fin N) K, L.IsLowerTriangular → L.det ≠ 0 →
        matrixPoint x (L * c) ∈ zeroLocus K J)
    {Fr : Type*} [Field Fr] [Algebra K Fr] (xF : Fin m → Fr) (cF : Matrix (Fin N) (Fin N) Fr)
    (hcF : cF.det ≠ 0) (hJF : ∀ g ∈ J, aeval (matrixPoint xF cF) g = 0)
    (LF : Matrix (Fin N) (Fin N) Fr) (hLFl : LF.IsLowerTriangular) (hLF : LF.det ≠ 0) :
    ∀ g ∈ J, aeval (matrixPoint xF (LF * cF)) g = 0 := by
  classical
  intro g hg
  set G := aeval (invariantSubst (K := K)) g with hG
  -- G vanishes at the K-points of the test ideal
  have hGvan : G ∈ vanishingIdeal K (zeroLocus K (invariantTestIdeal J)) := by
    intro q hq
    have hle : invariantTestIdeal J ≤ RingHom.ker (aeval q).toRingHom := fun p hp => hq p hp
    obtain ⟨h1, h2⟩ := (invariantTestIdeal_le_ker_iff J _).mp hle
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1 h2
    set x : Fin m → K := fun i => q (Sum.inl i)
    set c : Matrix (Fin N) (Fin N) K := Matrix.of fun i j => q (Sum.inr (Sum.inl (i, j)))
    set L : Matrix (Fin N) (Fin N) K := Matrix.of fun i j => q (Sum.inr (Sum.inr (Sum.inl (i, j))))
    have hxc : matrixPoint x c ∈ zeroLocus K J := by
      intro p hp
      have h := h1 p hp
      rw [aeval_rename] at h
      convert h using 3
      funext v
      cases v <;> rfl
    have hdc : q (Sum.inr (Sum.inr (Sum.inr false))) * c.det = 1 := by
      have h := h2 _ (Or.inr (Or.inl rfl))
      rw [map_sub, map_mul, aeval_X, AlgHom.map_det, map_one, sub_eq_zero] at h
      convert h using 3
      ext i j
      simp [c]
    have hdL : q (Sum.inr (Sum.inr (Sum.inr true))) * L.det = 1 := by
      have h := h2 _ (Or.inr (Or.inr rfl))
      rw [map_sub, map_mul, aeval_X, AlgHom.map_det, map_one, sub_eq_zero] at h
      convert h using 3
      ext i j
      simp [L]
    have hLl : L.IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := hij
      have h := h2 _ (Or.inl ⟨(i, j), hij', rfl⟩)
      rw [aeval_X] at h
      exact h
    have hinv' := hinv x c hxc (right_ne_zero_of_mul_eq_one hdc) L hLl
      (right_ne_zero_of_mul_eq_one hdL) g hg
    show aeval q G = 0
    rw [hG, aeval_invariantSubst]
    exact hinv'
  rw [vanishingIdeal_zeroLocus_eq_radical] at hGvan
  obtain ⟨n, hn⟩ := hGvan
  -- the specialization to the point (x_F, c_F, L_F) kills the test ideal
  let w : InvariantVars m N → Fr := Sum.elim xF (Sum.elim (fun ij => cF ij.1 ij.2)
    (Sum.elim (fun ij => LF ij.1 ij.2) fun b => if b then LF.det⁻¹ else cF.det⁻¹))
  have hker : invariantTestIdeal J ≤ RingHom.ker (aeval w).toRingHom := by
    rw [invariantTestIdeal_le_ker_iff]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    refine ⟨fun g' hg' => ?_, fun s hs => ?_⟩
    · rw [aeval_rename]
      convert hJF g' hg' using 3
      funext v
      cases v <;> rfl
    · rcases hs with ⟨ij, hij, rfl⟩ | hs
      · rw [aeval_X]
        exact hLFl hij
      · rcases hs with rfl | rfl
        · rw [map_sub, map_mul, aeval_X, AlgHom.map_det, map_one]
          have hm : (aeval w).mapMatrix (Matrix.of fun i j =>
              (X (Sum.inr (Sum.inl (i, j))) : MvPolynomial (InvariantVars m N) K)) = cF := by
            ext i j
            simp [w]
          rw [hm]
          simp [w, inv_mul_cancel₀ hcF]
        · rw [map_sub, map_mul, aeval_X, AlgHom.map_det, map_one]
          have hm : (aeval w).mapMatrix (Matrix.of fun i j =>
              (X (Sum.inr (Sum.inr (Sum.inl (i, j)))) : MvPolynomial (InvariantVars m N) K)) = LF := by
            ext i j
            simp [w]
          rw [hm]
          simp [w, inv_mul_cancel₀ hLF]
  have h0 : aeval w (G ^ n) = 0 := hker hn
  rw [map_pow] at h0
  have hG0 : aeval w G = 0 := IsNilpotent.eq_zero ⟨n, h0⟩
  rw [hG, aeval_invariantSubst] at hG0
  have hx : (fun i => w (Sum.inl i)) = xF := rfl
  have hc : (Matrix.of fun i j => w (Sum.inr (Sum.inl (i, j)))) = cF := by
    ext i j
    rfl
  have hL : (Matrix.of fun i j => w (Sum.inr (Sum.inr (Sum.inl (i, j))))) = LF := by
    ext i j
    rfl
  rw [hx, hc, hL] at hG0
  exact hG0

end Invariance

/-- The properness of the flag variety in the form of polynomials: the projection of an invariant
zero set restricted to invertible matrices is closed. -/
theorem exists_matrix_of_vanishing_of_lowerTriangular_invariant {m N : ℕ}
    (J : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K))
    (hinv : ∀ (x : Fin m → K) (c : Matrix (Fin N) (Fin N) K), matrixPoint x c ∈ zeroLocus K J →
      c.det ≠ 0 → ∀ L : Matrix (Fin N) (Fin N) K, L.IsLowerTriangular → L.det ≠ 0 →
        matrixPoint x (L * c) ∈ zeroLocus K J)
    (x₀ : Fin m → K)
    (hx₀ : ∀ f : MvPolynomial (Fin m) K,
      (∀ x, (∃ c : Matrix (Fin N) (Fin N) K, c.det ≠ 0 ∧ matrixPoint x c ∈ zeroLocus K J) →
        eval x f = 0) → eval x₀ f = 0) :
    ∃ c : Matrix (Fin N) (Fin N) K, c.det ≠ 0 ∧ matrixPoint x₀ c ∈ zeroLocus K J := by
  classical
  obtain ⟨𝔓, h𝔓, h𝔓x⟩ := exists_minimalPrime_of_vanishing J x₀ hx₀
  have h𝔓prime : 𝔓.IsPrime := h𝔓.1.1
  have hJ𝔓 : rabinowitschIdeal J ≤ 𝔓 := h𝔓.1.2
  -- the fraction field of the quotient by 𝔓
  let D := MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K ⧸ 𝔓
  let Fr := FractionRing D
  let ι : MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K →ₐ[K] Fr :=
    (IsScalarTower.toAlgHom K D Fr).comp (Ideal.Quotient.mkₐ K 𝔓)
  have hι : ∀ g, ι g = 0 ↔ g ∈ 𝔓 := by
    intro g
    change algebraMap D Fr (Ideal.Quotient.mk 𝔓 g) = 0 ↔ g ∈ 𝔓
    rw [(IsFractionRing.injective D Fr).eq_iff' (map_zero _), Ideal.Quotient.eq_zero_iff_mem]
  have hιJ : ∀ g ∈ rabinowitschIdeal J, ι g = 0 := fun g hg => (hι g).mpr (hJ𝔓 hg)
  -- the generic point (x_F, c_F)
  let xF : Fin m → Fr := fun i => ι (X (some (Sum.inl i)))
  let cF : Matrix (Fin N) (Fin N) Fr := Matrix.of fun i j => ι (X (some (Sum.inr (i, j))))
  have hιrename : ∀ g, ι (rename some g) = aeval (matrixPoint xF cF) g := by
    intro g
    rw [← AlgHom.comp_apply]
    congr 1
    apply MvPolynomial.algHom_ext
    intro v
    cases v with
    | inl i => simp [xF, matrixPoint]
    | inr ij => simp [cF, matrixPoint]
  have hιker := (rabinowitschIdeal_le_ker_iff J ι.toRingHom).mp
    (fun g hg => RingHom.mem_ker.mpr (hιJ g hg))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hιker
  have hdetF : ι (X none) * cF.det = 1 := by
    have h := hιker.2
    rw [hιrename, aeval_matrixVariableDet] at h
    exact h
  have hcF : cF.det ≠ 0 := right_ne_zero_of_mul_eq_one hdetF
  have hJF : ∀ g ∈ J, aeval (matrixPoint xF cF) g = 0 := by
    intro g hg
    rw [← hιrename]
    exact hιker.1 g hg
  -- the local ring of x₀ and a dominating valuation subring
  let 𝔪 : Ideal (MvPolynomial (Fin m) K) := vanishingIdeal K {x₀}
  let φ₀ : MvPolynomial (Fin m) K →ₐ[K] Fr := ι.comp (rename (some ∘ Sum.inl))
  have hφ₀unit : ∀ s ∈ 𝔪.primeCompl, IsUnit (φ₀ s) := by
    intro s hs
    rw [isUnit_iff_ne_zero]
    intro h0
    apply hs
    change s ∈ (vanishingIdeal K {x₀} : Ideal (MvPolynomial (Fin m) K))
    rw [mem_vanishingIdeal_singleton_iff]
    exact h𝔓x s ((hι _).mp h0)
  let O := Localization.AtPrime 𝔪
  let φ : O →+* Fr := IsLocalization.lift (M := 𝔪.primeCompl) (g := φ₀.toRingHom)
    (fun s => hφ₀unit s.1 s.2)
  have hφ : ∀ f, φ (algebraMap _ O f) = φ₀ f := fun f => IsLocalization.lift_eq _ f
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing φ
  have hφ₀A : ∀ f, φ₀ f ∈ A := fun f => by rw [← hφ]; exact hA _
  have hφ₀max : ∀ f ∈ 𝔪, (⟨φ₀ f, hφ₀A f⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro f hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit ((φ.codRestrict A.toSubring hA) (algebraMap _ O f)) := by
      have : (φ.codRestrict A.toSubring hA) (algebraMap _ O f) = ⟨φ₀ f, hφ₀A f⟩ := by
        ext
        exact hφ f
      rw [this]
      exact hu
    have hO : IsUnit (algebraMap _ O f) := IsLocalHom.map_nonunit _ hu'
    exact ((IsLocalRing.mem_maximalIdeal _).mp
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff O 𝔪 f).mpr hf)) hO
  -- the Iwasawa decomposition of the generic matrix over A, and invariance over Fr
  obtain ⟨LF, hLFl, hLFR, hLFne, hLFd, hLFd'⟩ := exists_isLowerTriangular_mul_integral A N cF hcF
  have hLFdet : LF.det ≠ 0 := by
    intro h0
    apply hLFne
    rw [Matrix.det_mul, h0, zero_mul]
  have hJF' := aeval_eq_zero_of_lowerTriangular_invariant J hinv xF cF hcF hJF LF hLFl hLFdet
  -- the values in A and the reduction modulo the maximal ideal of A
  have hKA : ∀ r : K, algebraMap K Fr r ∈ A := fun r => by
    have h := hφ₀A (C r)
    rwa [← MvPolynomial.algebraMap_eq, AlgHom.commutes] at h
  have hxA : ∀ i, xF i ∈ A := fun i => by
    have h := hφ₀A (X i)
    simpa [φ₀, xF] using h
  let κ : K →+* A := (algebraMap K Fr).codRestrict A.toSubring hKA
  let valsA : Option (Fin m ⊕ (Fin N × Fin N)) → A := fun o => Option.elim o
    ⟨(LF * cF).det⁻¹, hLFd'⟩ (Sum.elim (fun i => ⟨xF i, hxA i⟩)
      fun ij => ⟨(LF * cF) ij.1 ij.2, hLFR ij.1 ij.2⟩)
  let θA : MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K →+* A := eval₂Hom κ valsA
  have hθA : ∀ g, ((θA g : A) : Fr) = aeval (fun o => (valsA o : Fr)) g := by
    intro g
    have h := map_eval₂Hom κ valsA A.subtype g
    rw [aeval_eq_eval₂Hom]
    exact h
  have hθAsome : ∀ g, ((θA (rename some g) : A) : Fr) = aeval (matrixPoint xF (LF * cF)) g := by
    intro g
    rw [hθA, aeval_rename]
    congr 2
    funext v
    cases v <;> rfl
  let θ := (IsLocalRing.residue A).comp θA
  let I₀ : Ideal (MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K) := rabinowitschIdeal J ⊔
    Ideal.span (Set.range fun i : Fin m => X (some (Sum.inl i)) - C (x₀ i))
  have hI₀ : I₀ ≤ RingHom.ker θ := by
    refine sup_le ((rabinowitschIdeal_le_ker_iff J θ).mpr ⟨fun g hg => ?_, ?_⟩) ?_
    · change IsLocalRing.residue A (θA (rename some g)) = 0
      have h1 : θA (rename some g) = 0 := Subtype.ext (by rw [hθAsome]; exact hJF' g hg)
      rw [h1, map_zero]
    · change IsLocalRing.residue A (θA (X none)) *
        IsLocalRing.residue A (θA (rename some (matrixVariableDet K m N))) = 1
      rw [← map_mul]
      have h1 : θA (X none) * θA (rename some (matrixVariableDet K m N)) = 1 := by
        apply Subtype.ext
        rw [MulMemClass.coe_mul, hθAsome, aeval_matrixVariableDet]
        have h2 : ((θA (X none) : A) : Fr) = (LF * cF).det⁻¹ := by
          rw [hθA, aeval_X]
          rfl
        rw [h2]
        have h3 : (Matrix.of fun i j => matrixPoint xF (LF * cF) (Sum.inr (i, j))) = LF * cF := by
          ext i j
          rfl
        rw [h3, inv_mul_cancel₀ hLFne]
        rfl
      rw [h1, map_one]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      change IsLocalRing.residue A (θA (X (some (Sum.inl i)) - C (x₀ i))) = 0
      rw [IsLocalRing.residue_eq_zero_iff]
      have h1 : θA (X (some (Sum.inl i)) - C (x₀ i)) = ⟨φ₀ (X i - C (x₀ i)), hφ₀A _⟩ := by
        apply Subtype.ext
        rw [hθA]
        simp [φ₀, valsA, xF]
      rw [h1]
      apply hφ₀max
      change _ ∈ (vanishingIdeal K {x₀} : Ideal (MvPolynomial (Fin m) K))
      rw [mem_vanishingIdeal_singleton_iff]
      simp
  have hI₀ne : I₀ ≠ ⊤ := by
    intro htop
    have h1 : (1 : MvPolynomial (Option (Fin m ⊕ (Fin N × Fin N))) K) ∈ RingHom.ker θ :=
      hI₀ (htop ▸ Submodule.mem_top)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨q, hq⟩ := exists_mem_zeroLocus_of_ne_top hI₀ne
  have hqR := (mem_zeroLocus_rabinowitschIdeal_iff J q).mp
    (zeroLocus_anti_mono le_sup_left hq)
  have hqx : ∀ i, q (some (Sum.inl i)) = x₀ i := by
    intro i
    have h := hq _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    simpa [sub_eq_zero] using h
  refine ⟨Matrix.of fun i j => q (some (Sum.inr (i, j))), right_ne_zero_of_mul_eq_one hqR.2, ?_⟩
  have hpt : matrixPoint x₀ (Matrix.of fun i j => q (some (Sum.inr (i, j)))) = q ∘ some := by
    funext v
    cases v with
    | inl i => exact (hqx i).symm
    | inr ij => rfl
  rw [hpt]
  exact hqR.1

end Projection

end MixedFujita
