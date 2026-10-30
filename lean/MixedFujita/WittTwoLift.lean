/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
Witt vectors of length two and lifts to them (step 10, R4-5).

Let `κ` be a field of characteristic `p`. The ring `W₂(κ) := W(κ)/(p²)` (`WittTwo`) has
* the reduction `W₂(κ) → κ` (`wittTwoReduction`), surjective by the Teichmüller lifts;
  `p² = 0`, and `p z = 0` only for `z` in the kernel (`W(κ)` is a domain);
* for perfect `κ`, the kernel `p W₂(κ)` (the maximal ideal of the discrete valuation ring `W(κ)`
  is `(p)`), so the kernel is square-zero;
* the Frobenius `σ` lifting `x ↦ x^p` (`wittTwoFrobenius`) and the Teichmüller lifts `[k]` with
  `σ [k] = [k]^p` (`wittTwoTeichmuller`).

Every map `A → κ` from a formally smooth `ℤ`-algebra lifts to `W₂(κ)` (`exists_wittTwo_lift`;
`A` is the finitely generated subring of check 505, `κ` a residue field at a closed point).

For an `A`-algebra `B`, the reduction `W₂(κ) ⊗_A B → κ ⊗_A B` is surjective with kernel
`p (W₂(κ) ⊗_A B)` (right exactness), and if `B` is flat, `p z = 0` only for `z` in the kernel
(the kernel of `p` on `W₂(κ) ⊗_A B` is the image of that on `W₂(κ)`). With `p² = 0` these are the
conditions `hker`, `hann`, `hp2` of the lift data of check 491, for `B` the functions on an affine
open of the closure `T_A`. The kernel is square-zero, `σ ⊗ 1` lifts the `p`-th power map and the
Teichmüller lifts reduce to the constants: the hypotheses of the Frobenius lifts of check 424.
-/

@[expose] public section

open TensorProduct

namespace MixedFujita

universe u

section WittTwo

variable (p : ℕ) [hp : Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p]

/-- The Witt vectors of length two, `W₂(κ) = W(κ)/(p²)`. -/
abbrev WittTwo : Type u := WittVector p κ ⧸ Ideal.span {((p : WittVector p κ) ^ 2)}

/-- `p` lies in the kernel of the constant coefficient. -/
theorem wittVector_constantCoeff_natCast_p :
    WittVector.constantCoeff (p : WittVector p κ) = 0 := by
  rw [map_natCast, CharP.cast_eq_zero]

/-- The reduction `W₂(κ) → κ`. -/
noncomputable def wittTwoReduction : WittTwo p κ →+* κ :=
  Ideal.Quotient.lift _ WittVector.constantCoeff fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, wittVector_constantCoeff_natCast_p, zero_pow two_ne_zero, mul_zero]

theorem wittTwoReduction_mk (x : WittVector p κ) :
    wittTwoReduction p κ (Ideal.Quotient.mk _ x) = WittVector.constantCoeff x :=
  Ideal.Quotient.lift_mk _ _ _

omit [CharP κ p] in
theorem wittTwo_natCast_p :
    (p : WittTwo p κ) = Ideal.Quotient.mk _ (p : WittVector p κ) :=
  (map_natCast _ p).symm

omit [CharP κ p] in
/-- **`p² = 0` in `W₂(κ)`.** -/
theorem wittTwo_p_mul_p : (p : WittTwo p κ) * p = 0 := by
  rw [wittTwo_natCast_p, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.mem_span_singleton_self _

/-- The Teichmüller lifts `κ → W₂(κ)`. -/
noncomputable def wittTwoTeichmuller : κ →* WittTwo p κ :=
  (Ideal.Quotient.mk (Ideal.span {((p : WittVector p κ) ^ 2)})).toMonoidHom.comp
    (WittVector.teichmuller p)

omit [CharP κ p] in
theorem wittTwoTeichmuller_apply (k : κ) :
    wittTwoTeichmuller p κ k = Ideal.Quotient.mk _ (WittVector.teichmuller p k) :=
  rfl

theorem wittTwoReduction_teichmuller (k : κ) :
    wittTwoReduction p κ (wittTwoTeichmuller p κ k) = k := by
  rw [wittTwoTeichmuller_apply, wittTwoReduction_mk]
  exact WittVector.teichmuller_coeff_zero p k

theorem wittTwoReduction_surjective : Function.Surjective (wittTwoReduction p κ) :=
  fun k => ⟨wittTwoTeichmuller p κ k, wittTwoReduction_teichmuller p κ k⟩

/-- **`p z = 0` in `W₂(κ)` only for `z` in the kernel of the reduction.** -/
theorem wittTwoReduction_eq_zero_of_p_mul_eq_zero (z : WittTwo p κ)
    (hz : (p : WittTwo p κ) * z = 0) : wittTwoReduction p κ z = 0 := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [wittTwo_natCast_p, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hz
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hz
  have hp0 : (p : WittVector p κ) ≠ 0 := WittVector.p_nonzero p κ
  have hz : z = b * p := by
    apply mul_left_cancel₀ hp0
    rw [← hb]
    ring
  rw [wittTwoReduction_mk, hz, map_mul, wittVector_constantCoeff_natCast_p, mul_zero]

/-- The kernel of the constant coefficient of `W(κ)` is `(p)` for perfect `κ`. -/
theorem ker_wittVector_constantCoeff [PerfectRing κ p] :
    RingHom.ker (WittVector.constantCoeff : WittVector p κ →+* κ) =
      Ideal.span {(p : WittVector p κ)} := by
  have hmax : (RingHom.ker (WittVector.constantCoeff : WittVector p κ →+* κ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun k =>
      ⟨WittVector.teichmuller p k, WittVector.teichmuller_coeff_zero p k⟩
  rw [IsLocalRing.eq_maximalIdeal hmax]
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 (WittVector.irreducible p)

/-- **The kernel of the reduction `W₂(κ) → κ` is `p W₂(κ)`** for perfect `κ`. -/
theorem wittTwoReduction_eq_zero_iff [PerfectRing κ p] (x : WittTwo p κ) :
    wittTwoReduction p κ x = 0 ↔ ∃ z, x = p * z := by
  constructor
  · intro hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [wittTwoReduction_mk] at hx
    have hmem : x ∈ Ideal.span {(p : WittVector p κ)} := by
      rw [← ker_wittVector_constantCoeff]
      exact RingHom.mem_ker.2 hx
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨Ideal.Quotient.mk _ z, by rw [wittTwo_natCast_p, ← map_mul, mul_comm]⟩
  · rintro ⟨z, rfl⟩
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

/-- The kernel of the reduction `W₂(κ) → κ` is square-zero. -/
theorem isNilpotent_ker_wittTwoReduction [PerfectRing κ p] :
    IsNilpotent (RingHom.ker (wittTwoReduction p κ)) := by
  refine ⟨2, ?_⟩
  have hker : RingHom.ker (wittTwoReduction p κ) = Ideal.span {(p : WittTwo p κ)} := by
    ext x
    rw [RingHom.mem_ker, wittTwoReduction_eq_zero_iff, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, mul_comm _ _⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, mul_comm _ _⟩
  rw [hker, Ideal.span_singleton_pow, pow_two (p : WittTwo p κ), wittTwo_p_mul_p]
  exact Ideal.span_singleton_eq_bot.2 rfl

/-- The Frobenius of `W₂(κ)`. -/
noncomputable def wittTwoFrobenius : WittTwo p κ →+* WittTwo p κ :=
  Ideal.quotientMap _ WittVector.frobenius (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
      map_natCast]
    exact Ideal.mem_span_singleton_self _)

omit [CharP κ p] in
theorem wittTwoFrobenius_mk (x : WittVector p κ) :
    wittTwoFrobenius p κ (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (WittVector.frobenius x) :=
  Ideal.quotientMap_mk

/-- **The Frobenius of `W₂(κ)` lifts `x ↦ x^p`.** -/
theorem wittTwoReduction_frobenius (x : WittTwo p κ) :
    wittTwoReduction p κ (wittTwoFrobenius p κ x) = wittTwoReduction p κ x ^ p := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [wittTwoFrobenius_mk, wittTwoReduction_mk, wittTwoReduction_mk]
  exact WittVector.coeff_frobenius_charP p x 0

/-- **The Frobenius raises Teichmüller lifts to the `p`-th power.** -/
theorem wittTwoFrobenius_teichmuller (k : κ) :
    wittTwoFrobenius p κ (wittTwoTeichmuller p κ k) = wittTwoTeichmuller p κ k ^ p := by
  have h : WittVector.frobenius (WittVector.teichmuller p k) = WittVector.teichmuller p k ^ p := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [wittTwoTeichmuller_apply, wittTwoFrobenius_mk, h, map_pow]

/-- **Maps from a formally smooth `ℤ`-algebra lift to `W₂(κ)`** for perfect `κ`. -/
theorem exists_wittTwo_lift [PerfectRing κ p] {A : Type*} [CommRing A]
    [Algebra.FormallySmooth ℤ A] (φ : A →+* κ) :
    ∃ ψ : A →+* WittTwo p κ, (wittTwoReduction p κ).comp ψ = φ := by
  let g : WittTwo p κ →ₐ[ℤ] κ := (wittTwoReduction p κ).toIntAlgHom
  have hg : Function.Surjective g := wittTwoReduction_surjective p κ
  have hg' : IsNilpotent (RingHom.ker (g : WittTwo p κ →+* κ)) :=
    isNilpotent_ker_wittTwoReduction p κ
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective φ.toIntAlgHom g hg hg' :
    A →+* WittTwo p κ), ?_⟩
  ext a
  exact Algebra.FormallySmooth.liftOfSurjective_apply φ.toIntAlgHom g hg hg' a

end WittTwo

section TensorReduction

variable {A W k B : Type*} [CommRing A] [CommRing W] [CommRing k] [CommRing B]
  [Algebra A W] [Algebra A k] [Algebra A B] (red : W →ₐ[A] k)

theorem tensorReduction_eq_rTensor (z : W ⊗[A] B) :
    Algebra.TensorProduct.map red (AlgHom.id A B) z = red.toLinearMap.rTensor B z := by
  induction z using TensorProduct.inductionOn with
  | tmul w b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The reduction `W ⊗_A B → k ⊗_A B` is surjective. -/
theorem tensorReduction_surjective (hred : Function.Surjective red) :
    Function.Surjective (Algebra.TensorProduct.map red (AlgHom.id A B)) := by
  intro y
  obtain ⟨z, hz⟩ := LinearMap.rTensor_surjective B (g := red.toLinearMap) hred y
  exact ⟨z, by rw [tensorReduction_eq_rTensor, hz]⟩

/-- **The kernel of the reduction `W ⊗_A B → k ⊗_A B` is generated by `ε`** when that of
`W → k` is (right exactness of the tensor product). -/
theorem exists_eq_mul_of_tensorReduction_eq_zero (hred : Function.Surjective red) (ε : W)
    (hker : ∀ w, red w = 0 → ∃ v, w = ε * v) (z : W ⊗[A] B)
    (hz : Algebra.TensorProduct.map red (AlgHom.id A B) z = 0) :
    ∃ y, z = (ε ⊗ₜ[A] (1 : B)) * y := by
  rw [tensorReduction_eq_rTensor] at hz
  have hex := rTensor_exact B (LinearMap.exact_subtype_ker_map red.toLinearMap)
    (g := red.toLinearMap) hred
  obtain ⟨t, rfl⟩ := (hex z).1 hz
  clear hz
  induction t using TensorProduct.inductionOn with
  | tmul w b =>
    obtain ⟨v, hv⟩ := hker w (LinearMap.mem_ker.1 w.2)
    exact ⟨v ⊗ₜ b, by simp [hv, Algebra.TensorProduct.tmul_mul_tmul]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨c, hc⟩ := hy
    exact ⟨a + c, by rw [map_add, ha, hc, mul_add]⟩

/-- **After a flat base change, `ε` kills only elements of the kernel of the reduction** when this
holds for `W → k`: the kernel of `ε` on `W ⊗_A B` is the image of that on `W`. -/
theorem tensorReduction_eq_zero_of_mul_eq_zero [Module.Flat A B] (ε : W)
    (hann : ∀ w, ε * w = 0 → red w = 0) (z : W ⊗[A] B) (hz : (ε ⊗ₜ[A] (1 : B)) * z = 0) :
    Algebra.TensorProduct.map red (AlgHom.id A B) z = 0 := by
  let μ : W →ₗ[A] W := LinearMap.mulLeft A ε
  have hμz : ∀ z : W ⊗[A] B, μ.rTensor B z = (ε ⊗ₜ[A] (1 : B)) * z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul w b => simp [μ, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add, hx, hy, mul_add]
  have hex := Module.Flat.rTensor_exact B (LinearMap.exact_subtype_ker_map μ)
  obtain ⟨t, rfl⟩ := (hex z).1 (by rw [hμz, hz])
  have h0 : red.toLinearMap ∘ₗ (LinearMap.ker μ).subtype = 0 := by
    ext ⟨w, hw⟩
    exact hann w hw
  rw [tensorReduction_eq_rTensor, ← LinearMap.rTensor_comp_apply, h0, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end TensorReduction

section WittTwoTensor

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)

/-- The reduction `W₂(κ) → κ` as a map of `A`-algebras. -/
noncomputable def wittTwoReductionAlgHom : WittTwo p κ →ₐ[A] κ :=
  { wittTwoReduction p κ with commutes' := h }

/-- The reduction `W₂(κ) ⊗_A B → κ ⊗_A B` is surjective. -/
theorem wittTwo_tensor_surjective :
    Function.Surjective
      (Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B)) :=
  tensorReduction_surjective _ (wittTwoReduction_surjective p κ)

/-- **The kernel of the reduction `W₂(κ) ⊗_A B → κ ⊗_A B` is `p (W₂(κ) ⊗_A B)`.** -/
theorem wittTwo_tensor_exists_eq_p_mul [PerfectRing κ p] (z : WittTwo p κ ⊗[A] B)
    (hz : Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B) z = 0) :
    ∃ y, z = (p : WittTwo p κ ⊗[A] B) * y := by
  rw [Algebra.TensorProduct.natCast_def]
  exact exists_eq_mul_of_tensorReduction_eq_zero _ (wittTwoReduction_surjective p κ) _
    (fun w hw => (wittTwoReduction_eq_zero_iff p κ w).1 hw) z hz

/-- **For flat `B`, `p z = 0` in `W₂(κ) ⊗_A B` only for `z` in the kernel of the reduction.** -/
theorem wittTwo_tensor_eq_zero_of_p_mul_eq_zero [Module.Flat A B] (z : WittTwo p κ ⊗[A] B)
    (hz : (p : WittTwo p κ ⊗[A] B) * z = 0) :
    Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B) z = 0 := by
  rw [Algebra.TensorProduct.natCast_def] at hz
  exact tensorReduction_eq_zero_of_mul_eq_zero _ _
    (fun w hw => wittTwoReduction_eq_zero_of_p_mul_eq_zero p κ w hw) z hz

omit [CharP κ p] [Algebra A κ] in
/-- `p² = 0` in `W₂(κ) ⊗_A B`. -/
theorem wittTwo_tensor_p_mul_p : (p : WittTwo p κ ⊗[A] B) * p = 0 := by
  rw [Algebra.TensorProduct.natCast_def, Algebra.TensorProduct.tmul_mul_tmul, wittTwo_p_mul_p,
    TensorProduct.zero_tmul]

/-- **The kernel of the reduction `W₂(κ) ⊗_A B → κ ⊗_A B` is square-zero.** -/
theorem wittTwo_tensor_mul_eq_zero [PerfectRing κ p] (x y : WittTwo p κ ⊗[A] B)
    (hx : Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B) x = 0)
    (hy : Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B) y = 0) :
    x * y = 0 := by
  obtain ⟨x', rfl⟩ := wittTwo_tensor_exists_eq_p_mul p κ h x hx
  obtain ⟨y', rfl⟩ := wittTwo_tensor_exists_eq_p_mul p κ h y hy
  rw [mul_mul_mul_comm, wittTwo_tensor_p_mul_p, zero_mul]

/-- The Frobenius of `W₂(κ)` lifts the `p`-th power map of `κ ⊗_A B` on `W₂(κ) ⊗ 1`. -/
theorem wittTwo_tensor_frobenius (a : WittTwo p κ) :
    Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B)
        (wittTwoFrobenius p κ a ⊗ₜ[A] (1 : B)) =
      Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B)
        (a ⊗ₜ[A] (1 : B)) ^ p := by
  have h1 : wittTwoReductionAlgHom p κ h (wittTwoFrobenius p κ a) =
      wittTwoReductionAlgHom p κ h a ^ p :=
    wittTwoReduction_frobenius p κ a
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h1,
    Algebra.TensorProduct.tmul_pow, one_pow]

/-- The Teichmüller lifts reduce to the constants. -/
theorem wittTwo_tensor_teichmuller (k : κ) :
    Algebra.TensorProduct.map (wittTwoReductionAlgHom p κ h) (AlgHom.id A B)
      (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : B)) = k ⊗ₜ[A] (1 : B) := by
  have h1 : wittTwoReductionAlgHom p κ h (wittTwoTeichmuller p κ k) = k :=
    wittTwoReduction_teichmuller p κ k
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h1]

end WittTwoTensor

end MixedFujita
