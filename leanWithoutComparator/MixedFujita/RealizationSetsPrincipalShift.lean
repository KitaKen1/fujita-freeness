/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SNCWeightSpecializationComparison
public import MixedFujita.KltMinimizerDataShift

/-!
The realization sets and the normalized profiles do not change under a principal shift (step 9,
in the form used by section 5).

Let E = D + div g. Multiplication by g is a K-linear bijection from the sections of E to those of
D which keeps zero divisors (`cartierSectionZeroDivisor_principalShift`). The realized profiles,
the profile data and the normalized profiles see the sections only through their zero divisors.
So they are the same for a tuple of sections of E and for its shift, and for bases matched by the
shift. Hence the closedness of the realization sets in the tuple, and in the point, holds for E
when it holds for D. For l A = J + div φ the divisor j J is (j l) A + div φ^(-j), so the two
closedness statements pass from the degrees j l of A to the degrees j of J, and the sections of
D J and of (D l) A have the same dimension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Filter Topology
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

attribute [local instance] Classical.propDecidable

attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseLocalScalarTower
  cartierBaseSectionScalarTower cartierBaseOpenAlgebra functionFieldBaseAlgebra

section Shift

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

/-- The shift of a section is nonzero exactly when the section is nonzero. -/
theorem cartierPrincipalShiftLinear_ne_zero_iff (D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (s : Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    cartierPrincipalShiftLinear (K := K) D g s ≠ 0 ↔ s ≠ 0 :=
  ⟨fun h h0 => h (by rw [h0, map_zero]), cartierPrincipalShiftLinear_ne_zero D g s⟩

/-- A tuple of sections of D + div g realizes a profile exactly when its shift does. -/
theorem isRealizedProfile_principalShift (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (g : Y.functionFieldˣ) (x : Y) {N : ℕ}
    (s : Fin N → Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) (α : Fin N → ℝ) :
    IsRealizedProfile cY fY d D₀ D x (fun i => cartierPrincipalShiftLinear (K := K) D g (s i)) α ↔
      IsRealizedProfile cY fY d D₀ (D + principalCartierDivisor Y g) x s α := by
  constructor
  · rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, hval⟩
    refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, fun i hs => ?_⟩
    have h := hval i ((cartierPrincipalShiftLinear_ne_zero_iff D g (s i)).mpr hs)
    rwa [cartierSectionZeroDivisor_principalShift (K := K) D g (s i) hs] at h
  · rintro ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, hval⟩
    refine ⟨U, hUi, hUn, hUo, hUs, σ, hσd, hσo, hσ, cU, e, hcl, hpos, fun i hs => ?_⟩
    have hs' := (cartierPrincipalShiftLinear_ne_zero_iff D g (s i)).mp hs
    rw [cartierSectionZeroDivisor_principalShift (K := K) D g (s i) hs']
    exact hval i hs'

/-- The closedness of the realization sets in the tuple passes to a principal shift of the
divisor. -/
theorem realizationSetsZariskiClosed_principalShift (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (g : Y.functionFieldˣ) (x : Y)
    (h : RealizationSetsZariskiClosed cY fY d D₀ D x) :
    RealizationSetsZariskiClosed cY fY d D₀ (D + principalCartierDivisor Y g) x := by
  intro N m b α hα
  obtain ⟨I, hI⟩ := h N m (fun k => cartierPrincipalShiftLinear (K := K) D g (b k)) α hα
  refine ⟨I, ?_⟩
  rw [← hI]
  ext c
  simp only [Set.mem_ofPred_eq]
  rw [← isRealizedProfile_principalShift cY fY d D₀ D g x]
  simp only [map_sum, map_smul]

/-- The profile data of a tuple of sections of D + div g are those of its shift. -/
theorem sncWeightProfiles_principalShift (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ) (d : ℕ)
    (D₀ D : CartierDivisor Y) (g : Y.functionFieldˣ) (y : Y) {N : ℕ}
    (s : Fin N → Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) :
    sncWeightProfiles cY fY d D₀ D y (fun i => cartierPrincipalShiftLinear (K := K) D g (s i)) =
      sncWeightProfiles cY fY d D₀ (D + principalCartierDivisor Y g) y s := by
  ext p
  constructor
  · rintro ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, hGsupp, hw0, hy, hA, hv⟩
    have hs' : ∀ i, s i ≠ 0 := fun i =>
      (cartierPrincipalShiftLinear_ne_zero_iff D g (s i)).mp (hs i)
    refine ⟨hs', X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, fun i z hz => ?_, hw0, hy, hA, fun i => ?_⟩
    · rw [← cartierSectionZeroDivisor_principalShift (K := K) D g (s i) (hs' i)]
      exact hGsupp i z hz
    · rw [← cartierSectionZeroDivisor_principalShift (K := K) D g (s i) (hs' i)]
      exact hv i
  · rintro ⟨hs, X, hXi, hXn, hXo, hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc,
      hBsupp, hGsupp, hw0, hy, hA, hv⟩
    refine ⟨fun i => cartierPrincipalShiftLinear_ne_zero D g (s i) (hs i), X, hXi, hXn, hXo,
      hXs, π, hπd, hπo, hπp, hπ, cX, r, ξ, w, hinj, hξ, hsnc, hBsupp, fun i z hz => ?_, hw0, hy,
      hA, fun i => ?_⟩
    · rw [cartierSectionZeroDivisor_principalShift (K := K) D g (s i) (hs i)]
      exact hGsupp i z hz
    · rw [cartierSectionZeroDivisor_principalShift (K := K) D g (s i) (hs i)]
      exact hv i

/-- The normalized profiles of D + div g are those of D. -/
theorem sncWeightNormalizedProfiles_principalShift (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (g : Y.functionFieldˣ) (N : ℕ)
    (y : Y) :
    sncWeightNormalizedProfiles cY fY d D₀ (D + principalCartierDivisor Y g) N y =
      sncWeightNormalizedProfiles cY fY d D₀ D N y := by
  ext q
  constructor
  · rintro ⟨B, p, hp, hp1, hq⟩
    refine ⟨B.map (cartierPrincipalShiftEquiv (K := K) D g), p, ?_, hp1, hq⟩
    have hB : ⇑(B.map (cartierPrincipalShiftEquiv (K := K) D g)) =
        fun i => cartierPrincipalShiftLinear (K := K) D g (B i) := by
      funext i
      rw [Module.Basis.map_apply]
      rfl
    have h := sncWeightProfiles_principalShift cY fY d D₀ D g y ⇑B
    rw [← hB] at h
    rw [h]
    exact hp
  · rintro ⟨B, p, hp, hp1, hq⟩
    refine ⟨B.map (cartierPrincipalShiftEquiv (K := K) D g).symm, p, ?_, hp1, hq⟩
    have hB : (fun i => cartierPrincipalShiftLinear (K := K) D g
        ((B.map (cartierPrincipalShiftEquiv (K := K) D g).symm) i)) = ⇑B := by
      funext i
      rw [Module.Basis.map_apply]
      exact (cartierPrincipalShiftEquiv (K := K) D g).apply_symm_apply (B i)
    have h := sncWeightProfiles_principalShift cY fY d D₀ D g y
      ⇑(B.map (cartierPrincipalShiftEquiv (K := K) D g).symm)
    rw [hB] at h
    rw [← h]
    exact hp

/-- The closedness of the realization sets in the point passes to a principal shift of the
divisor. -/
theorem normalizedProfiles_isClosed_principalShift (cY : EtaleChart K Y n)
    (fY : Y.functionFieldˣ) (d : ℕ) (D₀ D : CartierDivisor Y) (g : Y.functionFieldˣ)
    (h : ∀ α : Fin (Module.finrank K Γ(D.sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D
        (Module.finrank K Γ(D.sheaf, ⊤)) y}) :
    ∀ α : Fin (Module.finrank K Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        (D + principalCartierDivisor Y g)
        (Module.finrank K Γ((D + principalCartierDivisor Y g).sheaf, ⊤)) y} := by
  have key : ∀ N₁ N₂ : ℕ, N₁ = N₂ →
      (∀ α : Fin N₂ → ℚ, IsClosed {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ D N₂ y}) →
      ∀ α : Fin N₁ → ℚ, IsClosed {y : Y | (fun i => (α i : ℝ)) ∈
        sncWeightNormalizedProfiles cY fY d D₀ (D + principalCartierDivisor Y g) N₁ y} := by
    rintro N₁ N₂ rfl hN α
    have hset : {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        (D + principalCartierDivisor Y g) N₁ y} =
        {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀ D N₁ y} := by
      ext y
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, sncWeightNormalizedProfiles_principalShift]
    rw [hset]
    exact hN α
  exact key _ _ (finrank_add_principal (K := K) D g) h

end Shift

section Multiples

variable {K : Type u} [Field K] {n : ℕ} {Y : Scheme.{u}} [IsIntegral Y]
  [Y.Over (Spec (CommRingCat.of K))]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- If l A = J + div φ then (j l) A = j J + div φ^j. -/
theorem nsmul_mul_eq_nsmul_add_principal {A J : CartierDivisor Y} {l : ℕ}
    {φ : Y.functionFieldˣ} (hlA : l • A = J + principalCartierDivisor Y φ) (j : ℕ) :
    (j * l) • A = j • J + principalCartierDivisor Y (φ ^ j) := by
  rw [← smul_smul, hlA, smul_add, principalCartierDivisor_power]

omit [Y.Over (Spec (CommRingCat.of K))] in
/-- If l A = J + div φ then j J = (j l) A + div φ^(-j). -/
theorem nsmul_eq_nsmul_mul_add_principal {A J : CartierDivisor Y} {l : ℕ}
    {φ : Y.functionFieldˣ} (hlA : l • A = J + principalCartierDivisor Y φ) (j : ℕ) :
    j • J = (j * l) • A + principalCartierDivisor Y (φ ^ j)⁻¹ := by
  rw [nsmul_mul_eq_nsmul_add_principal hlA j, add_assoc, ← principalCartierDivisor_mul,
    mul_inv_cancel, principalCartierDivisor_one, add_zero]

/-- If E = D + div g, the sections of E and of D have the same dimension. -/
theorem finrank_eq_of_eq_add_principal {E D : CartierDivisor Y} {g : Y.functionFieldˣ}
    (h : E = D + principalCartierDivisor Y g) :
    Module.finrank K Γ(E.sheaf, ⊤) = Module.finrank K Γ(D.sheaf, ⊤) := by
  subst h
  exact finrank_add_principal D g

/-- For l A = J + div φ, the sections of D J and of (D l) A have the same dimension. -/
theorem finrank_nsmul_eq_of_nsmul_eq {A J : CartierDivisor Y} {l : ℕ} {φ : Y.functionFieldˣ}
    (hlA : l • A = J + principalCartierDivisor Y φ) (D : ℕ) :
    Module.finrank K Γ((D • J).sheaf, ⊤) = Module.finrank K Γ(((D * l) • A).sheaf, ⊤) :=
  finrank_eq_of_eq_add_principal (nsmul_eq_nsmul_mul_add_principal hlA D)

/-- For l A = J + div φ, the closedness of the realization sets of (j l) A in the tuple gives that
of j J. -/
theorem realizationSetsZariskiClosed_of_nsmul_eq (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ : CartierDivisor Y) {A J : CartierDivisor Y} {l : ℕ} {φ : Y.functionFieldˣ}
    (hlA : l • A = J + principalCartierDivisor Y φ) (x : Y) (j : ℕ)
    (h : RealizationSetsZariskiClosed cY fY d D₀ ((j * l) • A) x) :
    RealizationSetsZariskiClosed cY fY d D₀ (j • J) x := by
  rw [nsmul_eq_nsmul_mul_add_principal hlA j]
  exact realizationSetsZariskiClosed_principalShift cY fY d D₀ _ _ x h

/-- For l A = J + div φ, the closedness of the realization sets of (j l) A in the point gives that
of j J. -/
theorem normalizedProfiles_isClosed_of_nsmul_eq (cY : EtaleChart K Y n) (fY : Y.functionFieldˣ)
    (d : ℕ) (D₀ : CartierDivisor Y) {A J : CartierDivisor Y} {l : ℕ} {φ : Y.functionFieldˣ}
    (hlA : l • A = J + principalCartierDivisor Y φ) (j : ℕ)
    (h : ∀ α : Fin (Module.finrank K Γ(((j * l) • A).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        ((j * l) • A) (Module.finrank K Γ(((j * l) • A).sheaf, ⊤)) y}) :
    ∀ α : Fin (Module.finrank K Γ((j • J).sheaf, ⊤)) → ℚ,
      IsClosed {y : Y | (fun i => (α i : ℝ)) ∈ sncWeightNormalizedProfiles cY fY d D₀
        (j • J) (Module.finrank K Γ((j • J).sheaf, ⊤)) y} := by
  rw [nsmul_eq_nsmul_mul_add_principal hlA j]
  exact normalizedProfiles_isClosed_principalShift cY fY d D₀ _ _ h

end Multiples

end MixedFujita
