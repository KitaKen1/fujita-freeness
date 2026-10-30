/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.RealizationLocalThreshold
public import MixedFujita.NormalizedProfileRealization
public import MixedFujita.LowerTriangularInvariantProjection
public import MixedFujita.SmoothClosedPoints
public import Mathlib.Data.Fin.Tuple.Sort

/-!
The closedness of the realization sets in the point (step 9, section 2.2 of the manuscript) from
Lemma 3 in the model form on the affine opens of a smooth variety.

`SmoothAffineLemmaThreeStatement`: for an affine open V of a smooth variety Y over an
algebraically closed field of characteristic zero, polynomials G_j in parameters c with
coefficients in Γ(V) and M ≥ 1, the set of pairs (y, c) of a closed point of V and a parameter
at which the threshold of the ideal of the G_j(c) at y is at most 1/M (model form) is the zero set
of an ideal of Γ(V)[c]: g(c) lies in the prime of y for every g of the ideal. It is the lower
semicontinuity of the log canonical threshold of a family of ideals, in the point and the
parameter jointly. It is a definition, used as a hypothesis; it is not proved here.

Around every closed point, D has a local equation f on an affine open V and the sections b_k of a
basis give regular functions r_k on V with image f b_k in the function field. A tuple
Σ_k c_ik b_k realizes a nonnegative rational profile β at y ∈ V exactly when the threshold of the
(Σ_k c_ik r_k)^(e_i) at y is at most 1/M (`isRealizedProfile_iff_modelThresholdBadAt`), so the
pairs (y, c) form a zero set; with generators of Γ(V) it is a zero set in K^m × K^(N×N). For β
sorted decreasingly, realization is invariant under lower triangular changes of the tuple, so the
projection of the zero set restricted to invertible matrices is closed
(`exists_matrix_of_vanishing_of_lowerTriangular_invariant`, the properness of the flag variety):
the points of V at which some basis realizes β are the closed points of a closed set. These local
closed sets glue on closed points (`isClosedOnClosedPoints_of_local`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Glue

/-- Closedness on closed points is local: if every closed point has an open neighbourhood on whose
closed points the set agrees with a closed set, the set is closed on closed points. -/
theorem isClosedOnClosedPoints_of_local {T : Type*} [TopologicalSpace T] (s : Set T)
    (h : ∀ x : T, IsClosed ({x} : Set T) → ∃ V : Set T, IsOpen V ∧ x ∈ V ∧
      ∃ C : Set T, IsClosed C ∧ ∀ y ∈ V, IsClosed ({y} : Set T) → (y ∈ s ↔ y ∈ C)) :
    IsClosedOnClosedPoints s := by
  refine ⟨closure (s ∩ {y | IsClosed ({y} : Set T)}), isClosed_closure, fun x hx => ?_⟩
  constructor
  · intro hxs
    exact subset_closure ⟨hxs, hx⟩
  · intro hxZ
    obtain ⟨V, hV, hxV, C, hC, hrep⟩ := h x hx
    have hsub : s ∩ {y | IsClosed ({y} : Set T)} ∩ V ⊆ C := by
      rintro y ⟨⟨hys, hyc⟩, hyV⟩
      exact (hrep y hyV hyc).mp hys
    have hx' : x ∈ closure (s ∩ {y | IsClosed ({y} : Set T)} ∩ V) := by
      rw [mem_closure_iff] at hxZ ⊢
      intro W hW hxW
      obtain ⟨z, hzW, hz⟩ := hxZ (W ∩ V) (hW.inter hV) ⟨hxW, hxV⟩
      exact ⟨z, hzW.1, hz, hzW.2⟩
    exact (hrep x hxV hx).mpr (closure_minimal hsub hC hx')

end Glue

section Algebra

open MvPolynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- The properness of the flag variety for the K-points of a finitely generated K-algebra: if the
K-points ψ and invertible matrices c at which an ideal of A[c] vanishes form a set invariant under
lower triangular changes of c, the K-points carrying such a c are the zero set of an ideal of
A. -/
theorem exists_ideal_of_lowerTriangular_invariant {A : Type*} [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] {N : ℕ} (I : Ideal (MvPolynomial (Fin N × Fin N) A))
    (hinv : ∀ (ψ : A →ₐ[K] K) (c : Matrix (Fin N) (Fin N) K),
      (∀ g ∈ I, ψ (eval (fun ij => algebraMap K A (c ij.1 ij.2)) g) = 0) → c.det ≠ 0 →
      ∀ L : Matrix (Fin N) (Fin N) K, L.IsLowerTriangular → L.det ≠ 0 →
        ∀ g ∈ I, ψ (eval (fun ij => algebraMap K A ((L * c) ij.1 ij.2)) g) = 0) :
    ∃ 𝔟 : Ideal A, ∀ ψ : A →ₐ[K] K,
      (∃ c : Matrix (Fin N) (Fin N) K, c.det ≠ 0 ∧
        ∀ g ∈ I, ψ (eval (fun ij => algebraMap K A (c ij.1 ij.2)) g) = 0) ↔
        ∀ a ∈ 𝔟, ψ a = 0 := by
  classical
  obtain ⟨m, π, hπ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K A)
  let Φ : MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K →ₐ[K] MvPolynomial (Fin N × Fin N) A :=
    aeval (Sum.elim (fun i => C (π (X i))) X)
  have hΦC : ∀ p : MvPolynomial (Fin m) K, Φ (rename Sum.inl p) = C (π p) := by
    intro p
    have h : (Φ.comp (rename Sum.inl)) =
        (IsScalarTower.toAlgHom K A (MvPolynomial (Fin N × Fin N) A)).comp π := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [Φ]
    exact congrArg (fun φ : MvPolynomial (Fin m) K →ₐ[K] MvPolynomial (Fin N × Fin N) A => φ p) h
  have hΦX : ∀ ij, Φ (X (Sum.inr ij)) = X ij := fun ij => by simp [Φ]
  have hΦsurj : Function.Surjective Φ := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a =>
      obtain ⟨p, rfl⟩ := hπ a
      exact ⟨rename Sum.inl p, hΦC p⟩
    | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add _ _ _⟩
    | mul_X p ij hp =>
      obtain ⟨p', rfl⟩ := hp
      exact ⟨p' * X (Sum.inr ij), by rw [map_mul, hΦX]⟩
  let 𝔍 : Ideal (MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K) := Ideal.comap Φ I
  -- the coordinates of a K-point and the evaluation of the pulled ideal
  let xOf : (A →ₐ[K] K) → Fin m → K := fun ψ i => ψ (π (X i))
  have hψπ : ∀ ψ : A →ₐ[K] K, ψ.comp π = aeval (xOf ψ) := fun ψ => by
    apply MvPolynomial.algHom_ext
    intro i
    simp [xOf]
  have hkey : ∀ (ψ : A →ₐ[K] K) (c : Matrix (Fin N) (Fin N) K) (g' : MvPolynomial _ K),
      ψ (eval (fun ij => algebraMap K A (c ij.1 ij.2)) (Φ g')) =
        aeval (matrixPoint (xOf ψ) c) g' := by
    intro ψ c g'
    let ev : MvPolynomial (Fin N × Fin N) A →ₐ[K] A :=
      (aeval (R := A) (fun ij => algebraMap K A (c ij.1 ij.2))).restrictScalars K
    have h : (ψ.comp (ev.comp Φ)) = aeval (matrixPoint (xOf ψ) c) := by
      apply MvPolynomial.algHom_ext
      intro v
      cases v with
      | inl i => simp [Φ, ev, matrixPoint, xOf]
      | inr ij => simp [Φ, ev, matrixPoint]
    have h2 := congrArg (fun φ : MvPolynomial (Fin m ⊕ (Fin N × Fin N)) K →ₐ[K] K => φ g') h
    simp only [AlgHom.comp_apply] at h2
    rw [← h2]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have hzero : ∀ (ψ : A →ₐ[K] K) (c : Matrix (Fin N) (Fin N) K),
      (∀ g ∈ I, ψ (eval (fun ij => algebraMap K A (c ij.1 ij.2)) g) = 0) ↔
        matrixPoint (xOf ψ) c ∈ zeroLocus K 𝔍 := by
    intro ψ c
    constructor
    · intro h g' hg'
      rw [← hkey]
      exact h _ hg'
    · intro h g hg
      obtain ⟨g', rfl⟩ := hΦsurj g
      rw [hkey]
      exact h g' hg
  -- every K-point of the zero set comes from a K-point of A
  have hpoint : ∀ (x : Fin m → K) (c : Matrix (Fin N) (Fin N) K),
      matrixPoint x c ∈ zeroLocus K 𝔍 → ∃ ψ : A →ₐ[K] K, xOf ψ = x := by
    intro x c hxc
    have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (aeval (R := K) x).toRingHom := by
      intro a ha
      have ha' : π a = 0 := RingHom.mem_ker.mp ha
      have h1 : rename Sum.inl a ∈ 𝔍 := by
        show Φ (rename Sum.inl a) ∈ I
        rw [hΦC, ha', map_zero]
        exact I.zero_mem
      have h2 := hxc _ h1
      rw [aeval_rename] at h2
      exact h2
    let ψ : A →ₐ[K] K := (Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) (aeval x) hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
    refine ⟨ψ, funext fun i => ?_⟩
    show Ideal.Quotient.liftₐ (RingHom.ker π.toRingHom) (aeval x) hker
      ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π (X i))) = x i
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
    change MvPolynomial.eval x (X i) = x i
    simp
  -- invariance of the zero set at the K-points
  have hinv' : ∀ (x : Fin m → K) (c : Matrix (Fin N) (Fin N) K), matrixPoint x c ∈ zeroLocus K 𝔍 →
      c.det ≠ 0 → ∀ L : Matrix (Fin N) (Fin N) K, L.IsLowerTriangular → L.det ≠ 0 →
        matrixPoint x (L * c) ∈ zeroLocus K 𝔍 := by
    intro x c hxc hc L hL hLd
    obtain ⟨ψ, rfl⟩ := hpoint x c hxc
    exact (hzero ψ (L * c)).mp (hinv ψ c ((hzero ψ c).mpr hxc) hc L hL hLd)
  -- the projection and its ideal
  let S : Set (Fin m → K) := {x | ∃ c : Matrix (Fin N) (Fin N) K, c.det ≠ 0 ∧
    matrixPoint x c ∈ zeroLocus K 𝔍}
  refine ⟨Ideal.map π (vanishingIdeal K S), fun ψ => ?_⟩
  constructor
  · rintro ⟨c, hc, hψc⟩ a ha
    rw [Ideal.mem_map_iff_of_surjective _ hπ] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    have h1 : xOf ψ ∈ S := ⟨c, hc, (hzero ψ c).mp hψc⟩
    have h2 := hp (xOf ψ) h1
    rw [← AlgHom.comp_apply, hψπ]
    exact h2
  · intro h
    obtain ⟨c, hc, hxc⟩ := exists_matrix_of_vanishing_of_lowerTriangular_invariant 𝔍 hinv'
      (xOf ψ) (fun p hp => by
        have h1 := h (π p) (Ideal.mem_map_of_mem _ (fun x hx => hp x hx))
        rw [← AlgHom.comp_apply, hψπ] at h1
        exact h1)
    exact ⟨c, hc, (hzero ψ c).mpr hxc⟩

end Algebra

section Statement

/-- Lemma 3 in the model form on the affine opens of a smooth variety: for polynomials G_j in
parameters c with coefficients in Γ(V) and M ≥ 1, the pairs of a closed point y of V and a
parameter c at which some prime divisor over Y with centre containing y has ord ≥ M A on every
nonzero G_j(c) are the zero set of an ideal of Γ(V)[c]. It is a definition, used as a hypothesis;
it is not proved here. -/
def SmoothAffineLemmaThreeStatement (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (n : ℕ)
    [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] (cY : EtaleChart K Y n)
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] {ι J : Type} [Finite ι] [Finite J]
    (G : J → MvPolynomial ι Γ(Y, V)) (M : ℕ), 1 ≤ M →
    ∃ I : Ideal (MvPolynomial ι Γ(Y, V)), ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) →
      ∀ c : ι → K,
        (ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
          (fun j => Y.germToFunctionField V
            (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j))) M ↔
          ∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
            (hV.primeIdealOf ⟨y, hy⟩).asIdeal)

end Statement

section Chart

variable {K : Type u} [Field K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- Around a point, a Cartier divisor has a local equation f on an affine open on which given
sections are f times regular functions. -/
theorem exists_affine_localEquation_regular (D : CartierDivisor Y) (x₀ : Y) {m : ℕ}
    (b : Fin m → Γ(D.sheaf, ⊤)) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (_ : x₀ ∈ V) (f : Y.functionFieldˣ)
      (r : Fin m → Γ(Y, V)), (∀ y ∈ V, D.IsLocalEquationAt y f) ∧
        ∀ (_ : Nonempty V) k, Y.germToFunctionField V (r k) =
          (f : Y.functionField) * cartierSectionRational D (b k) := by
  classical
  obtain ⟨f, hf⟩ := D.exists_isLocalEquationAt x₀
  obtain ⟨W, hxW, hW⟩ := CartierDivisor.isLocalEquationAt_iff.mp hf
  have hWloc : ∀ y ∈ W, D.IsLocalEquationAt y f := fun y hy =>
    CartierDivisor.isLocalEquationAt_iff.mpr ⟨W, hy, hW⟩
  choose W' hxW' s hs using fun k => Y.presheaf.exists_germ_eq
    (cartierLocalCoefficient D x₀ f hf (b k))
  set O : Y.Opens := W ⊓ ⨅ k, W' k with hO
  have hxO : x₀ ∈ O := ⟨hxW, by
    simp only [Opens.coe_iInf, Set.mem_iInter, SetLike.mem_coe]
    exact fun k => hxW' k⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVO⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hxO O.isOpen
  have hVW : V ≤ W := fun y hy => (hVO hy).1
  have hVW' : ∀ k, V ≤ W' k := fun k y hy => by
    have h := (hVO hy).2
    simp only [Opens.coe_iInf, Set.mem_iInter, SetLike.mem_coe] at h
    exact h k
  refine ⟨V, hV, hxV, f, fun k => Y.presheaf.map (homOfLE (hVW' k)).op (s k),
    fun y hy => hWloc y (hVW hy), fun _ k => ?_⟩
  show Y.germToFunctionField V (Y.presheaf.map (homOfLE (hVW' k)).op (s k)) = _
  rw [← Y.algebraMap_germ_eq_germToFunctionField hxV, TopCat.Presheaf.germ_res_apply, hs k,
    cartierLocalCoefficient_image]

end Chart

section Points

variable {K : Type u} [Field K] [IsAlgClosed K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ} [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

omit [IsAlgClosed K] [IsIntegral Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] in
include n in
/-- The sections over an affine open of a smooth variety are a finitely generated K-algebra. -/
theorem smooth_affineOpen_finiteType {V : Y.Opens} (hV : IsAffineOpen V) :
    Algebra.FiniteType K Γ(Y, V) := by
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have : Algebra.Smooth K Γ(Y, V) := smoothScheme_affineOpen_smooth hV
  infer_instance

omit [IsAlgClosed K] [IsIntegral Y] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] in
/-- A point of an affine open lies in the basic open of a section exactly when the section is
not in its prime. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {V : Y.Opens} (hV : IsAffineOpen V) (y : Y)
    (hy : y ∈ V) (g : Γ(Y, V)) :
    y ∈ Y.basicOpen g ↔ g ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  rw [Y.mem_basicOpen g y hy]
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : V)
  have := hV.isLocalization_stalk (⟨y, hy⟩ : V)
  exact IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
    (hV.primeIdealOf ⟨y, hy⟩).asIdeal g

omit [IsAlgClosed K] [IsIntegral Y] [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Every K-point of the sections over an affine open is a closed point. -/
theorem exists_closedPoint_of_algHom {V : Y.Opens} (hV : IsAffineOpen V) (ψ : Γ(Y, V) →ₐ[K] K) :
    ∃ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) ∧
      ∀ a, ψ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
  have hsurj : Function.Surjective ψ := fun k => ⟨algebraMap K Γ(Y, V) k, ψ.commutes k⟩
  have hmax : (RingHom.ker ψ.toRingHom).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  set q : PrimeSpectrum Γ(Y, V) := ⟨RingHom.ker ψ.toRingHom, hmax.isPrime⟩ with hq
  have hy : hV.fromSpec q ∈ V := by
    have h : hV.fromSpec q ∈ Set.range hV.fromSpec := ⟨q, rfl⟩
    rw [hV.range_fromSpec] at h
    exact h
  have hprime : hV.primeIdealOf ⟨hV.fromSpec q, hy⟩ = q :=
    hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec q, hy⟩)
  refine ⟨hV.fromSpec q, hy, ?_, fun a => ?_⟩
  · have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace (Y ↘ Spec (CommRingCat.of K))
    have hqc : q ∈ closedPoints (Spec Γ(Y, V)) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hmax
    rw [← hV.fromSpec.isOpenEmbedding.preimage_closedPoints] at hqc
    exact hqc
  · rw [hprime]
    exact RingHom.mem_ker.symm

end Points

section Independence

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- Combinations of a basis by the rows of a matrix are linearly independent exactly when the
matrix is invertible. -/
theorem linearIndependent_sum_smul_iff_det_ne_zero {N : ℕ} (b₀ : Module.Basis (Fin N) K E)
    (c : Matrix (Fin N) (Fin N) K) :
    LinearIndependent K (fun i => ∑ k, c i k • b₀ k) ↔ c.det ≠ 0 := by
  have h : (fun i => ∑ k, c i k • b₀ k) = b₀.equivFun.symm ∘ fun i => c i := by
    funext i
    simp [Module.Basis.equivFun_symm_apply]
  rw [h, ← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_rows_iff_isUnit]
  exact ⟨fun hli => hli.of_comp _, fun hli => hli.map' _ b₀.equivFun.symm.ker⟩

end Independence

section Realization

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  {n : ℕ} [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))]

/-- On an affine open where a Cartier divisor has a local equation f and the sections b_k are f
times regular functions, the pairs (y, c) of a closed point and a coefficient matrix at which the
tuple Σ_k c_ik b_k realizes a nonnegative rational profile are the zero set of an ideal of
Γ(V)[c], by Lemma 3 in the model form on affine opens. -/
theorem exists_ideal_realization_on_affine (hL3 : SmoothAffineLemmaThreeStatement K)
    (cY : EtaleChart K Y n) (D : CartierDivisor Y) {N m : ℕ} (b : Fin m → Γ(D.sheaf, ⊤))
    (β : Fin N → ℚ) (hβ0 : ∀ i, 0 ≤ β i) (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V]
    (f : Y.functionFieldˣ) (r : Fin m → Γ(Y, V)) (hloc : ∀ y ∈ V, D.IsLocalEquationAt y f)
    (hr : ∀ k, Y.germToFunctionField V (r k) =
      (f : Y.functionField) * cartierSectionRational D (b k)) :
    ∃ I : Ideal (MvPolynomial (Fin N × Fin m) Γ(Y, V)),
      ∀ (y : Y) (hy : y ∈ V), IsClosed ({y} : Set Y) → ∀ c : Fin N × Fin m → K,
        (IsRealizedProfile cY (1 : Y.functionFieldˣ) 1
            (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D y
            (fun i => ∑ k, c (i, k) • b k) (fun i => (β i : ℝ)) ↔
          ∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
            (hV.primeIdealOf ⟨y, hy⟩).asIdeal) := by
  classical
  obtain ⟨M, ex, hM2, hex1, hexM⟩ := exists_common_exponents β hβ0
  let G : {i : Fin N // 0 < β i} → MvPolynomial (Fin N × Fin m) Γ(Y, V) := fun j =>
    (∑ k, MvPolynomial.X (j.1, k) * MvPolynomial.C (r k)) ^ (ex j.1)
  obtain ⟨I, hI⟩ := hL3 Y n cY V hV G M (by omega)
  have hc : ∀ a : K, Y.germToFunctionField V (algebraMap K Γ(Y, V) a) =
      algebraMap K Y.functionField a := fun a => (sectionGermAlgHom (K := K) V).commutes a
  refine ⟨I, fun y hy hyc c => ?_⟩
  rw [isRealizedProfile_iff_modelThresholdBadAt cY _ 1 _ D y f (hloc y hy) b β hβ0 hex1 hexM c]
  have hfun : (fun j : {i : Fin N // 0 < β i} =>
      (∑ k, algebraMap K Y.functionField (c (j.1, k)) *
        ((f : Y.functionField) * cartierSectionRational D (b k))) ^ (ex j.1)) =
      fun j => Y.germToFunctionField V
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j)) := by
    funext j
    simp only [G, map_pow, map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, hc, hr]
  rw [hfun]
  exact hI y hy hyc c

/-- On an affine open where a Cartier divisor has a local equation and the sections of a basis
are regular, the points at which some basis realizes a decreasing nonnegative rational profile
are the closed points of a closed set, by Lemma 3 in the model form on affine opens. -/
theorem exists_closed_realizedSet_on_affine (hL3 : SmoothAffineLemmaThreeStatement K)
    (cY : EtaleChart K Y n) (D : CartierDivisor Y) {N : ℕ} (hN : 0 < N)
    (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (β : Fin N → ℚ) (hβ0 : ∀ i, 0 ≤ β i)
    (hβanti : Antitone β) (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (f : Y.functionFieldˣ)
    (r : Fin N → Γ(Y, V)) (hloc : ∀ y ∈ V, D.IsLocalEquationAt y f)
    (hr : ∀ k, Y.germToFunctionField V (r k) =
      (f : Y.functionField) * cartierSectionRational D (b₀ k)) :
    ∃ C : Set Y, IsClosed C ∧ ∀ y ∈ V, IsClosed ({y} : Set Y) →
      ((∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D y B
          (fun i => (β i : ℝ))) ↔ y ∈ C) := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hfin : Module.Finite K Γ(D.sheaf, ⊤) := Module.Finite.of_basis b₀
  have hcard : Fintype.card (Fin N) = Module.finrank K Γ(D.sheaf, ⊤) :=
    (Module.finrank_eq_card_basis b₀).symm
  obtain ⟨I, hreal⟩ := exists_ideal_realization_on_affine hL3 cY D b₀ β hβ0 V hV f r hloc hr
  have hFT : Algebra.FiniteType K Γ(Y, V) := smooth_affineOpen_finiteType (n := n) hV
  -- the invariance under lower triangular changes
  have htup : ∀ (L c : Matrix (Fin N) (Fin N) K) (i : Fin N),
      ∑ l, L i l • ∑ k, c l k • b₀ k = ∑ k, (L * c) i k • b₀ k := by
    intro L c i
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  have hinv : ∀ (ψ : Γ(Y, V) →ₐ[K] K) (c : Matrix (Fin N) (Fin N) K),
      (∀ g ∈ I, ψ (MvPolynomial.eval (fun ij => algebraMap K Γ(Y, V) (c ij.1 ij.2)) g) = 0) →
      c.det ≠ 0 → ∀ L : Matrix (Fin N) (Fin N) K, L.IsLowerTriangular → L.det ≠ 0 →
        ∀ g ∈ I, ψ (MvPolynomial.eval
          (fun ij => algebraMap K Γ(Y, V) ((L * c) ij.1 ij.2)) g) = 0 := by
    intro ψ c hψc _ L hL _
    obtain ⟨y, hy, hyc, hψ⟩ := exists_closedPoint_of_algHom hV ψ
    have h1 := (hreal y hy hyc (fun ij => c ij.1 ij.2)).mpr fun g hg => (hψ _).mp (hψc g hg)
    have hL' : ∀ i l, L i l ≠ 0 → (β i : ℝ) ≤ (β l : ℝ) := by
      intro i l hil
      have hli : l ≤ i := by
        by_contra hlt
        exact hil (hL (show OrderDual.toDual l < OrderDual.toDual i from not_le.mp hlt))
      exact_mod_cast hβanti hli
    have h2 := isRealizedProfile_triangular cY _ 1 _ D y _ _ L hL' h1
    have h3 : (fun i => ∑ l, L i l • ∑ k, (fun ij : Fin N × Fin N => c ij.1 ij.2) (l, k) • b₀ k) =
        fun i => ∑ k, (fun ij : Fin N × Fin N => (L * c) ij.1 ij.2) (i, k) • b₀ k :=
      funext fun i => htup L c i
    rw [h3] at h2
    intro g hg
    exact (hψ _).mpr ((hreal y hy hyc _).mp h2 g hg)
  obtain ⟨𝔟, h𝔟⟩ := exists_ideal_of_lowerTriangular_invariant I hinv
  refine ⟨Y.zeroLocus (U := V) (𝔟 : Set Γ(Y, V)), Y.zeroLocus_isClosed _, fun y hy hyc => ?_⟩
  have hmax : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩ hyc
  let ev : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  have hev : ∀ a, ev a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := fun a =>
    closedPointEvaluation_eq_zero_iff (K := K) _ a
  have hzl : y ∈ Y.zeroLocus (U := V) (𝔟 : Set Γ(Y, V)) ↔ ∀ b ∈ 𝔟, ev b = 0 := by
    rw [Scheme.mem_zeroLocus_iff]
    refine forall₂_congr fun b _ => ?_
    rw [mem_basicOpen_iff_notMem_primeIdealOf hV y hy, not_not, hev]
  rw [hzl, ← h𝔟 ev]
  constructor
  · rintro ⟨B, hB⟩
    let c : Matrix (Fin N) (Fin N) K := Matrix.of fun i k => b₀.repr (B i) k
    have hBc : (fun i => ∑ k, (fun ij : Fin N × Fin N => c ij.1 ij.2) (i, k) • b₀ k) = ⇑B :=
      funext fun i => b₀.sum_repr (B i)
    refine ⟨c, ?_, fun g hg => (hev _).mpr ((hreal y hy hyc _).mp (by rw [hBc]; exact hB) g hg)⟩
    have hli : LinearIndependent K (fun i => ∑ k, c i k • b₀ k) := by
      have h := B.linearIndependent
      rw [← hBc] at h
      exact h
    exact (linearIndependent_sum_smul_iff_det_ne_zero b₀ c).mp hli
  · rintro ⟨c, hcdet, hcI⟩
    have hli := (linearIndependent_sum_smul_iff_det_ne_zero b₀ c).mpr hcdet
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_⟩
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
    exact (hreal y hy hyc (fun ij => c ij.1 ij.2)).mpr fun g hg => (hev _).mp (hcI g hg)

omit [IsAlgClosed K] [CharZero K] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))]
  [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] in
/-- Simultaneous reindexing of a tuple and a profile does not change realization. -/
theorem isRealizedProfile_comp_equiv (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (y : Y) {N : ℕ} (s : Fin N → Γ(D.sheaf, ⊤)) (α : Fin N → ℝ)
    (e : Fin N ≃ Fin N) :
    IsRealizedProfile cY fY d D₀ D y (s ∘ e) (α ∘ e) ↔ IsRealizedProfile cY fY d D₀ D y s α := by
  constructor
  · rintro ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e', hx, hA, hval⟩
    refine ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e', hx, hA, fun i hs => ?_⟩
    have hs' : (s ∘ e) (e.symm i) ≠ 0 := by simpa using hs
    have h := hval (e.symm i) hs'
    simpa using h
  · rintro ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e', hx, hA, hval⟩
    exact ⟨U, h1, h2, h3, h4, σ, h5, h6, hσ, cU, e', hx, hA, fun i hs => hval (e i) hs⟩

/-- The closedness on closed points of the set of points at which some basis realizes a
nonnegative rational profile, from Lemma 3 in the model form on affine opens. -/
theorem isClosedOnClosedPoints_realized_of_smoothAffineLemmaThree
    (hL3 : SmoothAffineLemmaThreeStatement K) (cY : EtaleChart K Y n) (D : CartierDivisor Y)
    {N : ℕ} (hN : 0 < N) (b₀ : Module.Basis (Fin N) K Γ(D.sheaf, ⊤)) (β : Fin N → ℚ)
    (hβ0 : ∀ i, 0 ≤ β i) :
    IsClosedOnClosedPoints {y : Y | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      IsRealizedProfile cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D y B
        (fun i => (β i : ℝ))} := by
  classical
  set τ := Tuple.sort (fun i => -β i) with hτ
  have hanti : Antitone (β ∘ τ) := by
    intro a b hab
    have h := Tuple.monotone_sort (fun i => -β i) hab
    simp only [Function.comp_apply] at h ⊢
    linarith
  have hset : {y : Y | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
      IsRealizedProfile cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D y B
        (fun i => (β i : ℝ))} =
      {y : Y | ∃ B : Module.Basis (Fin N) K Γ(D.sheaf, ⊤),
        IsRealizedProfile cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D y B
          (fun i => ((β ∘ τ) i : ℝ))} := by
    ext y
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B.reindex τ.symm, ?_⟩
      have h1 : ⇑(B.reindex τ.symm) = ⇑B ∘ τ := by
        funext i
        simp [Module.Basis.reindex_apply]
      rw [h1]
      exact (isRealizedProfile_comp_equiv cY _ 1 _ D y B (fun i => (β i : ℝ)) τ).mpr hB
    · rintro ⟨B, hB⟩
      refine ⟨B.reindex τ, ?_⟩
      have h1 : ⇑(B.reindex τ) = ⇑B ∘ τ.symm := by
        funext i
        simp [Module.Basis.reindex_apply]
      rw [h1]
      apply (isRealizedProfile_comp_equiv cY _ 1 _ D y (⇑B ∘ τ.symm) (fun i => (β i : ℝ)) τ).mp
      have h2 : (⇑B ∘ τ.symm) ∘ τ = ⇑B := by
        funext i
        simp
      rw [h2]
      exact hB
  rw [hset]
  apply isClosedOnClosedPoints_of_local
  intro x _
  obtain ⟨V, hV, hxV, f, r, hloc, hr⟩ := exists_affine_localEquation_regular D x b₀
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨C, hC, hrep⟩ := exists_closed_realizedSet_on_affine hL3 cY D hN b₀ (β ∘ τ)
    (fun i => hβ0 _) hanti V hV f r hloc (hr hne)
  exact ⟨V, V.isOpen, hxV, C, hC, fun y hy hyc => hrep y hy hyc⟩

/-- Lemma 3 at a closed point in the form of the closedness of the realization sets in the
tuple, as the slice of Lemma 3 in the model form on affine opens. -/
theorem realizationSetsZariskiClosed_of_smoothAffineLemmaThree
    (hL3 : SmoothAffineLemmaThreeStatement K) (cY : EtaleChart K Y n) (D : CartierDivisor Y)
    (x : Y) (hx : IsClosed ({x} : Set Y)) :
    RealizationSetsZariskiClosed cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) D x := by
  classical
  intro N m b α hα
  obtain ⟨V, hV, hxV, f, r, hloc, hr⟩ := exists_affine_localEquation_regular D x b
  have hne : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain ⟨I, hreal⟩ := exists_ideal_realization_on_affine hL3 cY D b α hα V hV f r hloc (hr hne)
  have hFT : Algebra.FiniteType K Γ(Y, V) := smooth_affineOpen_finiteType (n := n) hV
  have hmax : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  let ev : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hev : ∀ a, ev a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := fun a =>
    closedPointEvaluation_eq_zero_iff (K := K) _ a
  have hcomp : ∀ (c : Fin N × Fin m → K) (g : MvPolynomial (Fin N × Fin m) Γ(Y, V)),
      ev (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g) =
        MvPolynomial.eval c (MvPolynomial.map ev.toRingHom g) := by
    intro c g
    rw [MvPolynomial.eval_map]
    have h : ev.toRingHom.comp (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i))) =
        MvPolynomial.eval₂Hom ev.toRingHom c := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp
      · intro i
        simp
    exact congrArg (fun φ : MvPolynomial (Fin N × Fin m) Γ(Y, V) →+* K => φ g) h
  refine ⟨Ideal.map (MvPolynomial.map ev.toRingHom) I, ?_⟩
  ext c
  change IsRealizedProfile _ _ _ _ D x _ _ ↔ ∀ p ∈ Ideal.map (MvPolynomial.map ev.toRingHom) I,
    MvPolynomial.eval c p = 0
  rw [hreal x hxV hx c]
  constructor
  · intro h p hp
    have hle : Ideal.map (MvPolynomial.map ev.toRingHom) I ≤ RingHom.ker (MvPolynomial.eval c) := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomp]
      exact (hev _).mpr (h g hg)
    exact hle hp
  · intro h g hg
    rw [← hev, hcomp]
    exact h _ (Ideal.mem_map_of_mem _ hg)

end Realization

end MixedFujita
