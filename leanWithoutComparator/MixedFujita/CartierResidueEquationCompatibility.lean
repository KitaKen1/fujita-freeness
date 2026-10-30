/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SmoothCartierCanonicalAdjunction

/-! 実方程式の単元変更に対する局所留数整合性。 check-277：実際の正則主商 A→B について、ker=(g)、gの非零因子性、A/Bの形式的滑らかさから、B·dg→B⊗Ω_A→Ω_B の単射・完全性・全射性を内部証明。既存OpenAIの行列式随伴を再利用して、Ω_Bの有限自由基底の下で局所標準随伴同型と正確な楔積公式を構成し、その一意性と基底・分裂選択からの独立性を証明。実方程式gを単元倍ugへ変える際の微分・楔積の変換を計算し、二つの局所留数同型と分子の単元倍の整合性を元の商データから内部構成。大域の層同型や元lc中心の数値随伴を証明済みとはしない。 -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open KaehlerDifferential
namespace MixedFujita


/-- Only the first conormal direction scales when its actual equation changes. -/
theorem exteriorPower_wedge_append_one_smul
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : ℕ) (v : M) (z : Fin r → M) (a : R) :
    exteriorPower.ιMulti R (1 + r) (Fin.append (fun _ : Fin 1 => a • v) z) =
      a • exteriorPower.ιMulti R (1 + r) (Fin.append (fun _ : Fin 1 => v) z) := by
  classical
  let w : Fin (1 + r) → M := Fin.append (fun _ : Fin 1 => v) z
  have hw : Fin.append (fun _ : Fin 1 => a • v) z =
      Function.update w (Fin.castAdd r (0 : Fin 1)) (a • v) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [w]
    · have hne : Fin.natAdd 1 j ≠ Fin.castAdd r (0 : Fin 1) := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_natAdd, Fin.val_castAdd, Fin.val_zero] at hh
        omega
      rw [Function.update_of_ne hne]
      simp [w]
  have hv : w (Fin.castAdd r (0 : Fin 1)) = v := by simp [w]
  have hu : Function.update w (Fin.castAdd r (0 : Fin 1)) v = w := by
    simpa only [hv] using (Function.update_eq_self (f := w) (a := Fin.castAdd r (0 : Fin 1)))
  rw [hw, AlternatingMap.map_update_smul, hu]


/-- The differential of a unit multiple of an actual quotient equation is its
unit multiple on the quotient; the extra Leibniz term vanishes there. -/
theorem quotient_equation_differential_mul
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B]
    (g a : A) (hg : algebraMap A B g = 0) :
    (1 : B) ⊗ₜ[A] D K A (a * g) =
      algebraMap A B a • ((1 : B) ⊗ₜ[A] D K A g) := by
  rw [Derivation.leibniz, TensorProduct.tmul_add]
  simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    ← Algebra.algebraMap_eq_smul_one, hg, TensorProduct.zero_tmul, add_zero]
  simp


/-- Local residue maps are compatible after changing a Cartier equation by a unit:
the numerator scales by that same unit. No splitting choices occur in this law. -/
theorem principal_quotient_canonical_adjunction_equation_change
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    (g a : A) (hg : algebraMap A B g = 0)
    (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (e e' : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]))
    (he : ∀ z : Fin r → B ⊗[A] Ω[A⁄K],
      e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
        exteriorPower.ιMulti B (1 + r)
          (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z))
    (he' : ∀ z : Fin r → B ⊗[A] Ω[A⁄K],
      e' (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
        exteriorPower.ιMulti B (1 + r)
          (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A (a * g)) z)) :
    (∀ t, e' t = algebraMap A B a • e t) ∧
      ∀ w, e'.symm (algebraMap A B a • w) = e.symm w := by
  have hmaps : e'.toLinearMap = (algebraMap A B a) • e.toLinearMap := by
    apply exteriorPower_linearMap_ext_of_surjective (mapBaseChange K A B)
      (mapBaseChange_surjective K A B hsurj) r
    intro z
    change e' _ = algebraMap A B a • e _
    rw [he', he, quotient_equation_differential_mul g a hg]
    exact exteriorPower_wedge_append_one_smul r _ z _
  have hpoint : ∀ t, e' t = algebraMap A B a • e t :=
    fun t => LinearMap.congr_fun hmaps t
  refine ⟨hpoint, fun w => ?_⟩
  apply e'.injective
  rw [e'.apply_symm_apply, hpoint, e.apply_symm_apply]


/-- Actual regular smooth Cartier equations and their unit changes supply
compatible local residue isomorphisms internally, without input conormal
certificates, splitting maps, or preconstructed residue maps. -/
theorem smooth_principal_quotient_exists_unit_compatible_residues
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (c : Module.Basis (Fin r) B Ω[B⁄K]) (u : Aˣ) :
    ∃ e e' : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]),
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z)) ∧
      (∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        e' (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A (↑u * g)) z)) ∧
      ∀ w, e'.symm (algebraMap A B ↑u • w) = e.symm w := by
  have hreg : ∀ a : A, a * (↑u * g) = 0 → a = 0 := by
    intro a ha
    have haz : a * ↑u = 0 := hg _ (by simpa only [mul_assoc] using ha)
    calc
      a = (a * ↑u) * ↑u⁻¹ := by simp [mul_assoc]
      _ = 0 := by rw [haz, zero_mul]
  have hkeru : RingHom.ker (algebraMap A B) = Ideal.span {↑u * g} := by
    rw [hker]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro x hx
      have hxg : x = g := Set.mem_singleton_iff.mp hx
      subst x
      exact Ideal.mem_span_singleton'.mpr ⟨↑u⁻¹, by simp [← mul_assoc]⟩
    · apply Ideal.span_le.mpr
      intro x hx
      have hxg : x = ↑u * g := Set.mem_singleton_iff.mp hx
      subst x
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)
  obtain ⟨e, he⟩ := smooth_principal_quotient_canonical_adjunction g hg hsurj hker r c
  obtain ⟨e', he'⟩ := smooth_principal_quotient_canonical_adjunction (↑u * g) hreg hsurj hkeru r c
  have hgzero : algebraMap A B g = 0 := RingHom.mem_ker.mp
    (hker ▸ Ideal.mem_span_singleton_self g)
  exact ⟨e, e', he, he',
    (principal_quotient_canonical_adjunction_equation_change g ↑u hgzero hsurj r e e' he he').2⟩

end MixedFujita
