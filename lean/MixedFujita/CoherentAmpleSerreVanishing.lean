/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.PolynomialHyperplaneSerreVanishing
public import MixedFujita.CartierSerreResidueDescent
public import MixedFujita.CartierCoherentTensor
public import MixedFujita.CartierAmpleDefinition

/-! 元ample Cartier因子の任意連接係数・全剰余類Serre消滅。 See reports/check-237-component-ample-serre-section-lifting.json for the verified scope. Ampleness on actual integral components gives full coherent Serre vanishing on the original possibly nonreduced proper scheme and actual eventual quotient-section lifting on effective Cartier cuts over any field. Component ampleness is an explicit input. The cohomological converse, nonreduced cut global generation, universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Serre vanishing for every actual coherent coefficient and every natural
power of an ORIGINAL ample Cartier divisor, including all residue classes. -/
theorem cartierIsAmpleProj_coherent_tensor_serreVanishing
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))]
    (H : CartierDivisor X) (hH : CartierIsAmpleProj K H)
    (M : X.Modules) [M.IsCoherent] :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology ((n • H).sheaf ⊗ M) (q + 1)) := by
  classical
  obtain ⟨m, hm, n, e, hec, he, g, hg, hgX, f, hmH⟩ := hH
  let := hec
  have hn : 0 < n := by
    obtain ⟨i, _⟩ := polynomialProjective_exists_coordinate_chart n K (e (genericPoint X))
    exact Nat.zero_lt_of_lt i.isLt
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let J := projectiveHyperplaneCartier e g hg hgX
  let a : (m • H).sheaf ≅ J.sheaf :=
    eqToIso (congrArg CartierDivisor.sheaf hmH) ≪≫ cartierSheafPrincipalShiftIso J f
  have hres (i : Fin m) : ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ q : ℕ,
      Subsingleton (Scheme.Modules.Cohomology
        ((j • (m • H)).sheaf ⊗ ((i.val • H).sheaf ⊗ M)) (q + 1)) := by
    let := cartierTensorModule_isCoherent (i.val • H) M
    obtain ⟨j₀, hj₀⟩ := projectiveHyperplane_tensor_serreVanishing e g hg hgX
      ((i.val • H).sheaf ⊗ M)
    refine ⟨j₀, fun j hj q => ?_⟩
    let := hj₀ j hj q
    exact (actualCohomologyLinearEquivOfIso
      (tensorIso (cartierNaturalMultiplesSheafIsoOfIso (m • H) J a j) (Iso.refl _))
      (q + 1)).subsingleton
  choose B hB using hres
  let b := Finset.univ.sup B
  refine ⟨b * m, fun n hn q => ?_⟩
  let i : Fin m := ⟨n % m, Nat.mod_lt n (by omega)⟩
  let := hB i (n / m) ((Finset.le_sup (f := B) (Finset.mem_univ i)).trans
    ((Nat.le_div_iff_mul_le (by omega)).mpr hn)) q
  let c : ((n / m) • (m • H)).sheaf ⊗ ((i.val • H).sheaf ⊗ M) ≅
      ((m * (n / m) + i.val) • H).sheaf ⊗ M :=
    (α_ _ _ _).symm ≪≫
      tensorIso (cartierTensorSheafIso ((n / m) • (m • H)) (i.val • H)) (Iso.refl M) ≪≫
      eqToIso (congrArg (fun D : CartierDivisor X => D.sheaf ⊗ M) (by
        rw [smul_smul, ← add_nsmul, Nat.mul_comm (n / m) m]))
  have heq : m * (n / m) + i.val = n := Nat.div_add_mod n m
  let c' := c ≪≫ eqToIso (congrArg (fun t : ℕ => (t • H).sheaf ⊗ M) heq)
  exact (actualCohomologyLinearEquivOfIso c' (q + 1)).symm.subsingleton

end MixedFujita
