/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.ResolutionChartOfPrime

/-!
Lemma 3 from the two restriction statements for products (step 9). For an affine open V of a
smooth variety Y and a smooth finitely generated domain B over K, X = Spec(Γ(V) ⊗ B) is the
product V × Spec B; a family g of functions on X restricts at a K-point w of B to the functions
(id ⊗ w)(g) on V. Two standard facts on the threshold along the fibres V × {w}:

* `FibreRestrictionStatement` (restriction to fibres, the inversion-of-adjunction direction): if
  the threshold of g at (y, w) on X is at most 1/M, so is the threshold of (id ⊗ w)(g) at y on V;
* `GenericRestrictionStatement` (generic restriction): for w in a dense open of Spec B, if the
  threshold of (id ⊗ w)(g) at y on V is at most 1/M, so is the threshold of g at (y, w) on X.

From them, Lemma 3 in the model form on affine opens follows
(`smoothAffineLemmaThreeStatement_of_restriction`). The K-points D of R = Γ(V)[c] where the
threshold of G(c) is at most 1/M have vanishing ideal I; a K-point χ₀ killing I lies on V(𝔭) for a
minimal prime 𝔭 of I, and D ∩ V(𝔭) is dense in V(𝔭) (an element of the other minimal primes not in
𝔭 separates). A smooth affine chart B of a resolution of V(𝔭) through χ₀ (with Φ : R → B, a common
denominator and a K-point w₀ over χ₀) carries the family g = Φ(G) on X = V × Spec B with the section
σ(w) = (Φ(·)(w), w). Lemma 3 for the fixed family g on X gives an ideal I_X; by generic restriction
σ*(I_X) vanishes at the K-points of B over D in a dense open, which are dense, so σ*(I_X) = 0; then
(y₀, w₀) is bad on X, and restriction to the fibre makes χ₀ bad. So F1 follows from sum KV and
the two restriction statements (`mixedFujitaFreeness_of_kvSum_of_restriction`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TensorProduct Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] cartierBaseOpenAlgebra specAlgebraOver

section Fibre

variable {K : Type u} [Field K] {A B : Type u} [CommRing A] [CommRing B] [Algebra K A]
  [Algebra K B]

/-- The restriction to the fibre over a K-point w of B: id ⊗ w. -/
noncomputable def fibreAt (w : B →ₐ[K] K) : A ⊗[K] B →ₐ[K] A :=
  Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp w)
    (fun _ _ => Commute.all _ _)

theorem fibreAt_tmul (w : B →ₐ[K] K) (a : A) (b : B) :
    fibreAt w (a ⊗ₜ[K] b) = a * algebraMap K A (w b) := by
  simp [fibreAt, Algebra.TensorProduct.lift_tmul]

/-- The point (ψ, w) of the product. -/
noncomputable def pairAlgHom (ψ : A →ₐ[K] K) (w : B →ₐ[K] K) : A ⊗[K] B →ₐ[K] K :=
  Algebra.TensorProduct.lift ψ w (fun _ _ => Commute.all _ _)

theorem pairAlgHom_tmul (ψ : A →ₐ[K] K) (w : B →ₐ[K] K) (a : A) (b : B) :
    pairAlgHom ψ w (a ⊗ₜ[K] b) = ψ a * w b := by
  simp [pairAlgHom, Algebra.TensorProduct.lift_tmul]

end Fibre

section Statements

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- Restriction to fibres of products: for an affine open V of a smooth variety Y of positive
dimension and a smooth finitely generated domain B, if the threshold of a family g on
Spec(Γ(V) ⊗ B) at the point (y, w) is at most 1/M in the model form, then so is the threshold at y
on Y of the restriction (id ⊗ w)(g) of g to the fibre over w. (In dimension zero the model form
has no prime divisors, so the zero family is not bad there.) -/
def FibreRestrictionStatement : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (n : ℕ)
    [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] (cY : EtaleChart K Y n)
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (B : Type u) [CommRing B] [IsDomain B]
    [Algebra K B] (d : ℕ)
    [SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B)))]
    [IsDomain (Γ(Y, V) ⊗[K] B)]
    [SmoothOfRelativeDimension (n + d)
      (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (n + d)) {J : Type} [Finite J]
    (g : J → Γ(Y, V) ⊗[K] B) (M : ℕ), 1 ≤ n → 1 ≤ M →
    ∀ (y : Y) (hy : y ∈ V) (ψ : Γ(Y, V) →ₐ[K] K),
      (∀ a, ψ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) → ∀ w : B →ₐ[K] K,
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor
          (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))
          (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ)))
        (specAlgHomPoint (pairAlgHom ψ w))
        (fun j => (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j))) M →
      ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
        (fun j => Y.germToFunctionField V (fibreAt w (g j))) M

/-- Generic restriction for products: in the situation of `FibreRestrictionStatement`, there is
a nonzero h ∈ B such that over every K-point w of B with w h ≠ 0, a point y of V at which the
restriction (id ⊗ w)(g) has threshold at most 1/M gives a point (y, w) of the product at which g
has threshold at most 1/M. -/
def GenericRestrictionStatement : Prop :=
  ∀ (Y : Scheme.{u}) [IsIntegral Y] [Y.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of K))] (n : ℕ)
    [SmoothOfRelativeDimension n (Y ↘ Spec (CommRingCat.of K))] (cY : EtaleChart K Y n)
    (V : Y.Opens) (hV : IsAffineOpen V) [Nonempty V] (B : Type u) [CommRing B] [IsDomain B]
    [Algebra K B] (d : ℕ)
    [SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap K B)))]
    [IsDomain (Γ(Y, V) ⊗[K] B)]
    [SmoothOfRelativeDimension (n + d)
      (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)) ↘ Spec (CommRingCat.of K))]
    (cX : EtaleChart K (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (n + d)) {J : Type} [Finite J]
    (g : J → Γ(Y, V) ⊗[K] B) (M : ℕ), 1 ≤ n → 1 ≤ M →
    ∃ h : B, h ≠ 0 ∧ ∀ w : B →ₐ[K] K, w h ≠ 0 →
      ∀ (y : Y) (hy : y ∈ V) (ψ : Γ(Y, V) →ₐ[K] K),
      (∀ a, ψ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) →
      ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
        (fun j => Y.germToFunctionField V (fibreAt w (g j))) M →
      ModelThresholdBadAt cX (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ) 1
        (1 • (smoothCanonicalDivisor cX + principalCartierDivisor
          (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)))
          (1 : (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).functionFieldˣ)))
        (specAlgHomPoint (pairAlgHom ψ w))
        (fun j => (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))).germToFunctionField ⊤
          ((Scheme.ΓSpecIso (CommRingCat.of (Γ(Y, V) ⊗[K] B))).inv (g j))) M

end Statements

section Assembly

variable {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]

/-- Lemma 3 in the model form on affine opens from restriction to fibres and generic restriction
for products. -/
theorem smoothAffineLemmaThreeStatement_of_restriction (hRI : FibreRestrictionStatement K)
    (hGR : GenericRestrictionStatement K) : SmoothAffineLemmaThreeStatement K := by
  classical
  intro Y _ _ _ n _ cY V hV _ ι J _ _ G M hM
  have : Smooth (Y ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hFTA : Algebra.FiniteType K Γ(Y, V) := smooth_affineOpen_finiteType (n := n) hV
  have hFTR : Algebra.FiniteType K (MvPolynomial ι Γ(Y, V)) :=
    Algebra.FiniteType.trans hFTA inferInstance
  have : IsNoetherianRing (MvPolynomial ι Γ(Y, V)) := Algebra.FiniteType.isNoetherianRing K _
  -- the bad K-points of Γ(V)[c]
  let ψof : (MvPolynomial ι Γ(Y, V) →ₐ[K] K) → (Γ(Y, V) →ₐ[K] K) := fun χ =>
    χ.comp (IsScalarTower.toAlgHom K Γ(Y, V) (MvPolynomial ι Γ(Y, V)))
  let Bad : Y → (ι → K) → Prop := fun y c =>
    ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
      (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y
      (fun j => Y.germToFunctionField V
        (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) (G j))) M
  let Dset : Set (MvPolynomial ι Γ(Y, V) →ₐ[K] K) := {χ | ∃ (y : Y) (hy : y ∈ V),
    IsClosed ({y} : Set Y) ∧ (∀ a, ψof χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
      Bad y (fun i => χ (MvPolynomial.X i))}
  let I : Ideal (MvPolynomial ι Γ(Y, V)) := ⨅ χ ∈ Dset, RingHom.ker χ.toRingHom
  have hmemI : ∀ g, g ∈ I ↔ ∀ χ ∈ Dset, χ g = 0 := by
    intro g
    simp only [I, Submodule.mem_iInf, RingHom.mem_ker]
    rfl
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- in dimension zero no point is bad
    refine ⟨⊤, fun y hy _ c => iff_of_false
      (not_modelThresholdBadAt_of_eq_zero hn0 cY _ _ _ y _ M) fun h => ?_⟩
    exact (hV.primeIdealOf ⟨y, hy⟩).isPrime.ne_top (eq_top_iff.mpr fun a _ => by
      simpa using h (MvPolynomial.C a) Submodule.mem_top)
  refine ⟨I, fun y hy hyc c => ?_⟩
  -- the K-point of (y, c)
  have hmax : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hy⟩ hyc
  let evy : Γ(Y, V) →ₐ[K] K := closedPointEvaluation (K := K) (hV.primeIdealOf ⟨y, hy⟩).asIdeal
  let χ₀ : MvPolynomial ι Γ(Y, V) →ₐ[K] K :=
    evy.comp ((MvPolynomial.aeval (fun i => algebraMap K Γ(Y, V) (c i))).restrictScalars K)
  have hχ₀ : ∀ g, χ₀ g = evy (MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g) := by
    intro g
    change evy (MvPolynomial.aeval _ g) = _
    rw [MvPolynomial.aeval_eq_eval]
  have hψ₀ : ψof χ₀ = evy := by
    ext a
    change χ₀ (MvPolynomial.C a) = evy a
    rw [hχ₀, MvPolynomial.eval_C]
  have hc₀ : (fun i => χ₀ (MvPolynomial.X i)) = c := by
    funext i
    rw [hχ₀, MvPolynomial.eval_X, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  have hRHS : (∀ g ∈ I, MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (c i)) g ∈
      (hV.primeIdealOf ⟨y, hy⟩).asIdeal) ↔ ∀ g ∈ I, χ₀ g = 0 := by
    refine forall₂_congr fun g _ => ?_
    rw [hχ₀, closedPointEvaluation_eq_zero_iff (K := K)]
  rw [hRHS]
  constructor
  · -- a bad point is in the bad set
    intro hbad g hg
    refine (hmemI g).mp hg χ₀ ⟨y, hy, hyc, ?_, ?_⟩
    · intro a
      rw [hψ₀]
      exact closedPointEvaluation_eq_zero_iff (K := K) _ a
    · rw [hc₀]
      exact hbad
  · -- closedness of the bad set
    intro hI
    have hIle : I ≤ RingHom.ker χ₀.toRingHom := fun g hg => (RingHom.mem_ker).mpr (hI g hg)
    have : (RingHom.ker χ₀.toRingHom).IsPrime := RingHom.ker_isPrime _
    obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le hIle
    have h𝔭prime : 𝔭.IsPrime := h𝔭min.1.1
    have hI𝔭 : I ≤ 𝔭 := h𝔭min.1.2
    -- an element of the other minimal primes outside 𝔭
    have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
    obtain ⟨s, hsP, hs𝔭⟩ : ∃ s, (∀ 𝔮 ∈ I.minimalPrimes, 𝔮 ≠ 𝔭 → s ∈ 𝔮) ∧ s ∉ 𝔭 := by
      by_contra hno
      push Not at hno
      have hle : (hfin.toFinset.erase 𝔭).inf id ≤ 𝔭 := fun s hs => hno s fun 𝔮 h𝔮 hne =>
        (Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne, hfin.mem_toFinset.mpr h𝔮⟩)) hs
      obtain ⟨𝔮, h𝔮F, h𝔮le⟩ := h𝔭prime.inf_le'.mp hle
      obtain ⟨hne, h𝔮mem⟩ := Finset.mem_erase.mp h𝔮F
      have h𝔮min : 𝔮 ∈ I.minimalPrimes := hfin.mem_toFinset.mp h𝔮mem
      exact hne (le_antisymm h𝔮le (h𝔭min.2 h𝔮min.1 h𝔮le))
    -- the bad points on V(𝔭) are dense in V(𝔭)
    let D𝔭 : Set (MvPolynomial ι Γ(Y, V) →ₐ[K] K) := {χ | χ ∈ Dset ∧ ∀ r ∈ 𝔭, χ r = 0}
    have hD𝔭 : ∀ r, (∀ χ ∈ D𝔭, χ r = 0) → r ∈ 𝔭 := by
      intro r hr
      have hrs : r * s ∈ I := by
        refine (hmemI _).mpr fun χ hχ => ?_
        have hIχ : I ≤ RingHom.ker χ.toRingHom := fun g hg =>
          (RingHom.mem_ker).mpr ((hmemI g).mp hg χ hχ)
        have : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime _
        obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hIχ
        rw [map_mul]
        by_cases h𝔮 : 𝔮 = 𝔭
        · subst h𝔮
          rw [hr χ ⟨hχ, fun r' hr' => (RingHom.mem_ker).mp (h𝔮le hr')⟩, zero_mul]
        · have hs0 : χ s = 0 := (RingHom.mem_ker).mp (h𝔮le (hsP 𝔮 h𝔮min h𝔮))
          rw [hs0, mul_zero]
      exact (h𝔭prime.mem_or_mem (hI𝔭 hrs)).resolve_right hs𝔭
    -- a smooth affine chart of a resolution of V(𝔭) through χ₀
    obtain ⟨B, _, _, _, hFTB, d, hsmB, Φ, t, hΦ𝔭, hker, ht𝔭, hden, w₀, hw₀⟩ :=
      exists_resolution_chart_of_prime 𝔭 χ₀ (fun r hr => (RingHom.mem_ker).mp (h𝔭le hr))
    -- the product V × Spec B
    have hsmA : SmoothOfRelativeDimension n
        (Spec.map (CommRingCat.ofHom (algebraMap K Γ(Y, V)))) :=
      smoothOfRelativeDimension_spec_sections hV
    have : IsDomain (Γ(Y, V) ⊗[K] B) := isDomain_tensorProduct_of_isAlgClosed K Γ(Y, V) B
    have hsmX : SmoothOfRelativeDimension (n + d)
        (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)) ↘ Spec (CommRingCat.of K)) :=
      smoothOfRelativeDimension_spec_tensorProduct Γ(Y, V) B
    have : Smooth (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B)) ↘ Spec (CommRingCat.of K)) :=
      SmoothOfRelativeDimension.smooth (n + d) _
    obtain ⟨cX⟩ : Nonempty (EtaleChart K (Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (n + d)) := by
      obtain ⟨c', -⟩ := Opens.mem_iSup.mp ((etaleCharts_cover (K := K)
        (X := Spec (CommRingCat.of (Γ(Y, V) ⊗[K] B))) (n := n + d)).symm ▸
          Opens.mem_top (specAlgHomPoint (pairAlgHom evy w₀)))
      exact ⟨c'⟩
    -- the family on the product and its fibres
    let ΦX : MvPolynomial ι Γ(Y, V) →ₐ[K] Γ(Y, V) ⊗[K] B :=
      (MvPolynomial.aeval (R := Γ(Y, V)) (fun i =>
        (Algebra.TensorProduct.includeRight : B →ₐ[K] Γ(Y, V) ⊗[K] B)
          (Φ (MvPolynomial.X i)))).restrictScalars K
    let g : J → Γ(Y, V) ⊗[K] B := fun j => ΦX (G j)
    have hfib : ∀ (w : B →ₐ[K] K) (j : J), fibreAt w (g j) =
        MvPolynomial.eval (fun i => algebraMap K Γ(Y, V) (w (Φ (MvPolynomial.X i)))) (G j) := by
      intro w j
      have h1 : (fibreAt w).toRingHom.comp ΦX.toRingHom = MvPolynomial.eval₂Hom (RingHom.id _)
          (fun i => algebraMap K Γ(Y, V) (w (Φ (MvPolynomial.X i)))) := by
        apply MvPolynomial.ringHom_ext
        · intro a
          change fibreAt w (MvPolynomial.aeval _ (MvPolynomial.C a)) = _
          rw [MvPolynomial.aeval_C, Algebra.TensorProduct.algebraMap_apply, fibreAt_tmul]
          simp
        · intro i
          change fibreAt w (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
          rw [MvPolynomial.aeval_X]
          change fibreAt w (1 ⊗ₜ[K] Φ (MvPolynomial.X i)) = _
          rw [fibreAt_tmul]
          simp
      exact congrArg (fun φ : MvPolynomial ι Γ(Y, V) →+* Γ(Y, V) => φ (G j)) h1
    -- the section of the product over Spec B
    let σS : Γ(Y, V) ⊗[K] B →ₐ[K] B :=
      Algebra.TensorProduct.lift (Φ.comp (IsScalarTower.toAlgHom K Γ(Y, V)
        (MvPolynomial ι Γ(Y, V)))) (AlgHom.id K B) (fun _ _ => Commute.all _ _)
    have hpair : ∀ w : B →ₐ[K] K, pairAlgHom (ψof (w.comp Φ)) w = w.comp σS := by
      intro w
      apply Algebra.TensorProduct.ext'
      intro a b
      rw [pairAlgHom_tmul]
      simp [σS, ψof, Algebra.TensorProduct.lift_tmul]
    -- Lemma 3 for the fixed family on the product, and generic restriction
    obtain ⟨IX, hIX⟩ := exists_ideal_badAt_spec (Γ(Y, V) ⊗[K] B) cX g M hM
    obtain ⟨h, hh0, hgen⟩ := hGR Y n cY V hV B d cX g M hn hM
    -- the section kills the ideal of the bad set of the product
    have hσ : ∀ f ∈ IX, σS f = 0 := by
      intro f hf
      refine eq_zero_of_forall_lift_mem Φ 𝔭 hΦ𝔭 hker t ht𝔭 hden D𝔭 (fun χ hχ => hχ.2) hD𝔭 hh0 ?_
      intro w hwh hwD
      obtain ⟨⟨y', hy', -, hψ', hbad'⟩, -⟩ := hwD
      have hfibbad : ModelThresholdBadAt cY (1 : Y.functionFieldˣ) 1
          (1 • (smoothCanonicalDivisor cY + principalCartierDivisor Y (1 : Y.functionFieldˣ))) y'
          (fun j => Y.germToFunctionField V (fibreAt w (g j))) M := by
        simp only [hfib]
        exact hbad'
      have hbadX := hgen w hwh y' hy' (ψof (w.comp Φ)) hψ' hfibbad
      have h2 := (hIX (pairAlgHom (ψof (w.comp Φ)) w)).mp hbadX f hf
      rw [hpair] at h2
      exact h2
    -- the point over χ₀ is bad on the product, hence on the fibre
    have hψ₀' : ψof (w₀.comp Φ) = evy := by
      rw [hw₀]
      exact hψ₀
    have hbadX₀ := (hIX (pairAlgHom evy w₀)).mpr fun r hr => by
      rw [← hψ₀', hpair]
      change w₀ (σS r) = 0
      rw [hσ r hr, map_zero]
    have hfin' := hRI Y n cY V hV B d cX g M hn hM y hy evy
      (fun a => closedPointEvaluation_eq_zero_iff (K := K) _ a) w₀ hbadX₀
    simp only [hfib] at hfin'
    have hc' : (fun i => w₀ (Φ (MvPolynomial.X i))) = c := by
      funext i
      have h3 := congrArg (fun φ : MvPolynomial ι Γ(Y, V) →ₐ[K] K => φ (MvPolynomial.X i)) hw₀
      simp only [AlgHom.comp_apply] at h3
      rw [h3]
      exact congrFun hc₀ i
    have hc'' : ∀ i, w₀ (Φ (MvPolynomial.X i)) = c i := fun i => congrFun hc' i
    simp only [hc''] at hfin'
    exact hfin'

/-- F1 from sum KV, restriction to fibres and generic restriction for products. -/
theorem mixedFujitaFreeness_of_kvSum_of_restriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNCSum K n)
    (hRI : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], FibreRestrictionStatement K)
    (hGR : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      GenericRestrictionStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kvSum_of_smoothAffineLemmaThree hKV
    (fun K _ _ _ => smoothAffineLemmaThreeStatement_of_restriction (hRI K) (hGR K))

/-- F1 from the usual KV, big plus nef, restriction to fibres and generic restriction for
products. -/
theorem mixedFujitaFreeness_of_kv_of_bigAddNef_of_restriction
    (hKV : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      KawamataViehwegVanishingSNC K n)
    (hba : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] (n : ℕ),
      BigAddNefStatement K n)
    (hRI : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K], FibreRestrictionStatement K)
    (hGR : ∀ (K : Type u) [Field K] [IsAlgClosed K] [CharZero K],
      GenericRestrictionStatement K) :
    MixedFujitaFreeness.{u} :=
  mixedFujitaFreeness_of_kv_of_bigAddNef_of_smoothAffineLemmaThree hKV hba
    (fun K _ _ _ => smoothAffineLemmaThreeStatement_of_restriction (hRI K) (hGR K))

end Assembly

end MixedFujita
