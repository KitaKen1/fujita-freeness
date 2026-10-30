/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.RegularPrincipalConormalSequence
public import OAI.AlgebraicGeometry.LogKodaira.Adjunction

/-! 正則主商の局所標準随伴と一意性。 check-277：実際の正則主商 A→B について、ker=(g)、gの非零因子性、A/Bの形式的滑らかさから、B·dg→B⊗Ω_A→Ω_B の単射・完全性・全射性を内部証明。既存OpenAIの行列式随伴を再利用して、Ω_Bの有限自由基底の下で局所標準随伴同型と正確な楔積公式を構成し、その一意性と基底・分裂選択からの独立性を証明。実方程式gを単元倍ugへ変える際の微分・楔積の変換を計算し、二つの局所留数同型と分子の単元倍の整合性を元の商データから内部構成。大域の層同型や元lc中心の数値随伴を証明済みとはしない。 -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open KaehlerDifferential
namespace MixedFujita


/-- Actual smooth Cartier equations give the determinant adjunction, with its
wedge formula. No conormal injection or exact-sequence certificate is input. -/
theorem smooth_principal_quotient_canonical_adjunction
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (c : Module.Basis (Fin r) B Ω[B⁄K]) :
    ∃ e : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]),
      ∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z) := by
  let j := LinearMap.toSpanSingleton B (B ⊗[A] Ω[A⁄K]) ((1 : B) ⊗ₜ[A] D K A g)
  obtain ⟨hj, hex, hq⟩ := regular_smooth_principal_quotient_differential_exact (K := K) g hg hsurj hker
  obtain ⟨e, he⟩ := OAI.ReverseLogKodaira.CanonicalAdjunction.exact_canonical_adjunction
    j (mapBaseChange K A B) hj hex hq (Module.Basis.singleton (Fin 1) B) c
  let a := OAI.ReverseLogKodaira.CanonicalAdjunction.determinantCoordinate
    (Module.Basis.singleton (Fin 1) B)
  let t := (TensorProduct.congr a (LinearEquiv.refl B (⋀[B]^r Ω[B⁄K]))).trans
    (TensorProduct.lid B (⋀[B]^r Ω[B⁄K]))
  let e' := t.symm.trans e
  refine ⟨e', fun z => ?_⟩
  have ha : a (exteriorPower.ιMulti B 1 (Module.Basis.singleton (Fin 1) B)) = 1 := by
    dsimp only [a]
    rw [OAI.ReverseLogKodaira.CanonicalAdjunction.determinantCoordinate_wedge, Module.Basis.det_self]
  have hin : t
        (exteriorPower.ιMulti B 1 (Module.Basis.singleton (Fin 1) B) ⊗ₜ[B]
          exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
      exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z) := by
    dsimp only [t]
    simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, TensorProduct.lid_tmul, ha, one_smul]
  change e (t.symm _) = _
  rw [← hin, t.symm_apply_apply]
  simpa only [j, Function.comp_def, Module.Basis.singleton_apply,
    LinearMap.toSpanSingleton_apply, one_smul] using he (Module.Basis.singleton (Fin 1) B) z


/-- Surjective lifts of differential vectors detect maps out of their actual
top exterior power. This supplies independence from all splitting choices. -/
theorem exteriorPower_linearMap_ext_of_surjective
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (q : M →ₗ[R] N) (hq : Function.Surjective q) (r : ℕ)
    (a b : (⋀[R]^r N) →ₗ[R] P)
    (h : ∀ z : Fin r → M,
      a (exteriorPower.ιMulti R r (q ∘ z)) = b (exteriorPower.ιMulti R r (q ∘ z))) :
    a = b := by
  classical
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R r N)
  rintro _ ⟨v, rfl⟩
  choose z hz using fun i => hq (v i)
  have hv : q ∘ z = v := funext hz
  rw [← hv]
  exact h z


/-- The actual smooth Cartier adjunction is unique: it does not depend on
the target differential basis or the chosen splitting of the conormal sequence. -/
theorem smooth_principal_quotient_canonical_adjunction_unique
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (g : A) (hg : ∀ a : A, a * g = 0 → a = 0)
    (hsurj : Function.Surjective (algebraMap A B))
    (hker : RingHom.ker (algebraMap A B) = Ideal.span {g})
    (r : ℕ) (c : Module.Basis (Fin r) B Ω[B⁄K]) :
    ∃! e : (⋀[B]^r Ω[B⁄K]) ≃ₗ[B] ⋀[B]^(1 + r) (B ⊗[A] Ω[A⁄K]),
      ∀ z : Fin r → B ⊗[A] Ω[A⁄K],
        e (exteriorPower.ιMulti B r (mapBaseChange K A B ∘ z)) =
          exteriorPower.ιMulti B (1 + r)
            (Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] D K A g) z) := by
  obtain ⟨e, he⟩ := smooth_principal_quotient_canonical_adjunction g hg hsurj hker r c
  refine ⟨e, he, fun e' he' => ?_⟩
  apply LinearEquiv.toLinearMap_injective
  exact exteriorPower_linearMap_ext_of_surjective (mapBaseChange K A B)
    (mapBaseChange_surjective K A B hsurj) r e'.toLinearMap e.toLinearMap
    (fun z => (he' z).trans (he z).symm)

end MixedFujita
