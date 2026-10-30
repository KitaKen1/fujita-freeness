/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CartierLocalAdjunctionIso

/-! 純正規化留数の一意性・独立構成した写像の方程式変更。 check-283：実商の全射性から微分の全持ち上げを内部供給し、純ambient dg楔積だけで実引き戻し標準加群の線形写像を検出することを証明。純正規化公式による留数の一意性、および任意に独立構成した二留数の方程式変更則を証明。同じ有効Cartier因子の二つの実正則方程式から、実イデアルの一致を通じて実単元を内部抽出。元のCartier係数と実線束pullback frameの全部分開の変換則を証明。実Cartier切断の同一affineチャート・固定座標の下で、二方程式から正規化留数とframe単元をそれぞれ内部構成し、逆向きの係数変化が打ち消し合うことから実局所標準随伴層同型の一致を構成。異なる座標・チャート間の一致、大域留数貼合せ、SNC反復随伴、数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite KaehlerDifferential
open TauCeti.AlgebraicGeometry.Scheme
open OAI.ReverseLogKodaira.DifferentialBaseChange
open OAI.ReverseLogKodaira.CanonicalAdjunction
namespace MixedFujita
universe u
attribute [local instance] cartierGlobalStalkAlgebra cartierGlobalStalkFunctionFieldTower
  cartierBaseGlobalAlgebra cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- Pure ambient dg wedges detect every B-linear map from the actual pulled
canonical line. Actual quotient surjectivity supplies all differential lifts. -/
theorem pure_pulled_residue_linear_ext
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (g : A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (P Q : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) →ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hPQ : ∀ z : Fin r → Ω[A⁄K],
      P ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z)) =
        Q ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z))) : P = Q := by
  classical
  have hp := KaehlerDifferential.map_surjective_of_surjective K K A B hsurj
  have he : P.comp R.symm.toLinearMap = Q.comp R.symm.toLinearMap := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B r Ω[B⁄K])
    rintro _ ⟨v, rfl⟩
    choose z hz using fun j => hp (v j)
    have hv : KaehlerDifferential.map K K A B ∘ z = v := funext hz
    rw [← hv]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    have hback : R.symm (exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) =
        (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (Fin.append (fun _ : Fin 1 => D K A g) z) := by
      apply R.injective
      rw [R.apply_symm_apply, hR]
    rw [hback]
    exact hPQ z
  apply LinearMap.ext
  intro w
  have h := LinearMap.congr_fun he (R w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, R.symm_apply_apply] using h


/-- The PURE normalized formula already uniquely determines the actual
residue, independently of all splitting and construction choices. -/
theorem pure_pulled_canonical_residue_unique
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (g : A) (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (R R' : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[A⁄K],
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) : R = R' := by
  apply LinearEquiv.toLinearMap_injective
  exact pure_pulled_residue_linear_ext g hsurj r R hR R.toLinearMap R'.toLinearMap
    (fun z => (hR z).trans (hR' z).symm)


/-- On the actual pulled canonical line, the numerator dg scales by the
actual quotient image of a when g is replaced by a*g. -/
theorem pulled_equation_wedge_scaling
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (g a : A) (hg : algebraMap A B g = 0) (r : ℕ)
    (b : Module.Basis (Fin (1 + r)) A Ω[A⁄K]) (z : Fin r → Ω[A⁄K]) :
    algebraMap A B a • ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
      (1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A (a * g)) z) := by
  apply (finiteFreeExteriorBaseChangeEquiv (B := B) b (1 + r)).injective
  rw [map_smul, finiteFreeExteriorBaseChangeEquiv_tmul_wedge,
    finiteFreeExteriorBaseChangeEquiv_tmul_wedge, one_smul]
  have hw (v : Ω[A⁄K]) :
      (fun i => (1 : B) ⊗ₜ[A] (Fin.append (fun _ : Fin 1 => v) z) i) =
        Fin.append (fun _ : Fin 1 => (1 : B) ⊗ₜ[A] v) (fun i => (1 : B) ⊗ₜ[A] z i) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Fin.append_left, Fin.append_right]
  rw [hw, hw, quotient_equation_differential_mul g a hg,
    exteriorPower_wedge_append_one_smul, one_smul]


/-- ANY two PURE normalized residues satisfy the equation-change law. No
compatibly chosen pair of residue maps is required. -/
theorem pure_pulled_residue_equation_change
    {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    (g a : A) (hg : algebraMap A B g = 0)
    (hsurj : Function.Surjective (algebraMap A B)) (r : ℕ)
    (b : Module.Basis (Fin (1 + r)) A Ω[A⁄K])
    (R R' : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄K])) ≃ₗ[B] ⋀[B]^r Ω[B⁄K])
    (hR : ∀ z : Fin r → Ω[A⁄K],
      R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A g) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z))
    (hR' : ∀ z : Fin r → Ω[A⁄K],
      R' ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
        (Fin.append (fun _ : Fin 1 => D K A (a * g)) z)) =
          exteriorPower.ιMulti B r (KaehlerDifferential.map K K A B ∘ z)) :
    ∀ w, R' (algebraMap A B a • w) = R w := by
  have hmaps : (algebraMap A B a) • R'.toLinearMap = R.toLinearMap := by
    apply pure_pulled_residue_linear_ext g hsurj r R hR
    intro z
    change algebraMap A B a • R' _ = R _
    rw [← map_smul, pulled_equation_wedge_scaling g a hg r b, hR', hR]
  intro w
  have h := LinearMap.congr_fun hmaps w
  simpa only [LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul] using h


/-- A genuine top wedge of a basis detects its scalar coefficient. This
public basis-level lemma avoids unfolding any chosen coordinate construction. -/
theorem topExterior_wedge_smul_cancel
    {T M : Type*} [CommRing T] [AddCommGroup M] [Module T M] {n : ℕ}
    (b : Module.Basis (Fin n) T M) {a a' : T}
    (h : a • exteriorPower.ιMulti T n b = a' • exteriorPower.ιMulti T n b) : a = a' := by
  have hc := congrArg (determinantCoordinate b) h
  simpa only [map_smul, determinantCoordinate_wedge, Module.Basis.det_self,
    smul_eq_mul, mul_one] using hc

end MixedFujita
