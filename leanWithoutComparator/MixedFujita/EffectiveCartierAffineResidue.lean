/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CanonicalResidueFrameUnits
public import MixedFujita.EffectiveCartierCoefficientSupport
public import MixedFujita.EtaleCoordinateDifferentials

/-! 実有効Cartier affine切断の商データと座標付き留数。 check-280：実引き戻し標準加群のチャート制限写像を構成し、任意の可換環図式で外積基底変更との自然性を証明。元の正則滑らか主商と実局所化から、両チャートの正規化留数同型を内部構成し、局所化と方程式の単元変更を合わせた制限則を実引き戻し標準加群上へ移送。有効Cartier因子の実閉部分スキームのaffine関数環について、方程式の非零因子性・実閉埋込みの全射性・核=(g)を内部供給。周囲と切断の実etale座標から形式的滑らかさと微分基底を供給し、実Cartier切断の正規化留数・frame単元性へ接続。標準Cartier層との同定・大域留数層同型・数値随伴は残る。 -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
open KaehlerDifferential
open OAI.ReverseLogKodaira.DifferentialBaseChange
namespace MixedFujita

variable {K A B S C : Type*} [CommRing K] [CommRing A] [CommRing B]
  [CommRing S] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K S] [Algebra K C]
  [Algebra A B] [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
  [IsScalarTower K A B] [IsScalarTower K A S] [IsScalarTower K A C]
  [IsScalarTower K B C] [IsScalarTower K S C]
  [IsScalarTower A B C] [IsScalarTower A S C]


open AlgebraicGeometry CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme
/-- A genuine affine effective Cartier cut supplies the complete regular
principal quotient data internally, using its actual closed immersion. -/
theorem effectiveCartier_affine_principal_quotient_data
    {X : Scheme} [IsIntegral X] (D : CartierDivisor X) (hD : D.IsEffective)
    (U : X.affineOpens) [Nonempty U.1] (g : Γ(X, U.1)) (hg : g ≠ 0)
    (hEq : rationalUnitClass X U.1
      (Additive.ofMul (regularEquationRationalUnit X U.1 g hg)) = D |_ U.1) :
    (∀ a : Γ(X, U.1), a * g = 0 → a = 0) ∧
      Function.Surjective (((effectiveCartierIdealSheaf D hD).subschemeι.app U).hom) ∧
      RingHom.ker (((effectiveCartierIdealSheaf D hD).subschemeι.app U).hom) =
        Ideal.span {g} := by
  refine ⟨fun a h => (mul_eq_zero.mp h).resolve_right hg,
    (effectiveCartierIdealSheaf D hD).subschemeι_app_surjective U, ?_⟩
  rw [(effectiveCartierIdealSheaf D hD).ker_subschemeι_app,
    effectiveCartierIdealSheaf_ideal_eq_span D hD U g hg hEq]


/-- Étale polynomial coordinates supply formal smoothness over the base field. -/
theorem formallySmooth_of_etale_coordinates
    {k T : Type*} [Field k] [CommRing T] [Algebra k T] {n : ℕ}
    (x : MvPolynomial (Fin n) k →ₐ[k] T) (hx : x.toRingHom.FormallyEtale) :
    Algebra.FormallySmooth k T := by
  let := x.toRingHom.toAlgebra
  let : IsScalarTower k (MvPolynomial (Fin n) k) T :=
    IsScalarTower.of_algebraMap_eq fun a => (x.commutes a).symm
  let : Algebra.FormallyEtale (MvPolynomial (Fin n) k) T := hx
  exact Algebra.FormallySmooth.comp k (MvPolynomial (Fin n) k) T

universe u
attribute [local instance] cartierBaseOpenAlgebra


/-- On an actual smooth affine Cartier cut, étale coordinate charts on the
ambient and cut construct the normalized residue and its unit on canonical
frames. Neither a quotient certificate nor a residue map is an input. The
base-field action on the cut is the one induced by its actual closed immersion. -/
theorem smooth_effectiveCartier_affine_pulled_residue_frame
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    (D : CartierDivisor X) (hD : D.IsEffective)
    (U : X.affineOpens) [Nonempty U.1] (g : Γ(X, U.1)) (hg : g ≠ 0)
    (hEq : rationalUnitClass X U.1
      (Additive.ofMul (regularEquationRationalUnit X U.1 g hg)) = D |_ U.1)
    (r : ℕ) (x : MvPolynomial (Fin (1 + r)) k →ₐ[k] Γ(X, U.1))
    (hx : x.toRingHom.FormallyEtale) :
    let A := Γ(X, U.1)
    let I := effectiveCartierIdealSheaf D hD
    let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)
    let q : A →+* B := (I.subschemeι.app U).hom
    let : Algebra A B := q.toAlgebra
    let : Algebra k B := (q.comp (algebraMap k A)).toAlgebra
    let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun a => rfl
    ∀ (y : MvPolynomial (Fin r) k →ₐ[k] B) (hy : y.toRingHom.FormallyEtale),
      ∃ R : (B ⊗[A] (⋀[A]^(1 + r) Ω[A⁄k])) ≃ₗ[B] ⋀[B]^r Ω[B⁄k],
        (∀ z : Fin r → Ω[A⁄k],
          R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
            (Fin.append (fun _ : Fin 1 => KaehlerDifferential.D k A g) z)) =
              exteriorPower.ιMulti B r (KaehlerDifferential.map k k A B ∘ z)) ∧
        ∃ v : Bˣ, R ((1 : B) ⊗ₜ[A] exteriorPower.ιMulti A (1 + r)
          (etaleCoordinateBasis x hx)) =
            (v : B) • exteriorPower.ιMulti B r (etaleCoordinateBasis y hy) := by
  let A := Γ(X, U.1)
  let I := effectiveCartierIdealSheaf D hD
  let B := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)
  let q : A →+* B := (I.subschemeι.app U).hom
  let : Algebra A B := q.toAlgebra
  let : Algebra k B := (q.comp (algebraMap k A)).toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun a => rfl
  dsimp only
  intro y hy
  let : Algebra.FormallySmooth k A := formallySmooth_of_etale_coordinates x hx
  let : Algebra.FormallySmooth k B := formallySmooth_of_etale_coordinates y hy
  obtain ⟨hreg, hsurj, hker⟩ := effectiveCartier_affine_principal_quotient_data D hD U g hg hEq
  obtain ⟨R, _, hR, hv⟩ := smooth_principal_quotient_pulled_canonical_residue_frame
    (K := k) (A := A) (B := B) g hreg hsurj hker r
      (etaleCoordinateBasis x hx) (etaleCoordinateBasis y hy)
  exact ⟨R, hR, hv⟩

end MixedFujita
