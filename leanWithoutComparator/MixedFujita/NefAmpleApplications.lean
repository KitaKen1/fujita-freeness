/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.NefAddAmpleProof
public import MixedFujita.BigAddNefProjective
public import MixedFujita.LinearEffectiveFreenessAmple
public import MixedFujita.SemiampleContractionProof

/-! 元klt・Kodaira摂動、projective big＋nefとF2の三入力還元。 See reports/check-240-weak-morse-integer-descent-nef-add-ample.json for the verified scope. Original NefAddAmpleStatement, weak algebraic Morse nonvanishing, klt and Kodaira perturbation are proved. Big plus nef is proved here with an original ample divisor on a normal positive-dimensional source; unrestricted proper BigAddNefStatement is not asserted. General KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Big plus nef is big on every normal projective source in the original
positive-dimensional scope, with no nef-plus-ample hypothesis supplied. -/
theorem cartierIsBig_add_of_isNef_on_projective
    {K : Type u} [Field K] [IsAlgClosed K] [CharZero K] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of K))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K))] {n : ℕ}
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    {H : CartierDivisor X} (hH : CartierIsAmpleProj K H)
    {B N : CartierDivisor X} (hB : CartierIsBig K B) (hN : CartierIsNef K N) :
    CartierIsBig K (B + N) :=
  cartierIsBig_add_of_isNef_of_nefAddAmple nefAddAmpleStatement_holds hdim hn hnorm hH hB hN


/-- The original klt perturbation statement follows with no nef-plus-ample
assumption left as an input. -/
theorem kltPerturbationStatement_holds : KltPerturbationStatement.{u} :=
  kltPerturbation_of_nefAddAmple nefAddAmpleStatement_holds


/-- Kodaira perturbation is supplied internally from the proved original
klt perturbation and the previously proved normal Kodaira lemma. -/
theorem kodairaPerturbationStatement_holds : KodairaPerturbationStatement.{u} :=
  kodairaPerturbation_of_kltPerturbation kltPerturbationStatement_holds


/-- F2 for ample divisors now requires only the original K-NF statement. -/
theorem linearEffectiveFreenessAmple_of_kawamataNumericalFreeness
    (hKNF : KawamataNumericalFreeness.{u}) : LinearEffectiveFreenessAmple.{u} :=
  linearEffectiveFreenessAmple_of_kawamataNumericalFreeness_of_nefAddAmple
    hKNF nefAddAmpleStatement_holds


/-- The full original F2 reduction no longer assumes nef-plus-ample,
Kodaira perturbation or contraction; only K-NF, klt BPF and Ambro remain inputs. -/
theorem linearEffectiveFreeness_of_kawamataNumericalFreeness_of_basePointFree_of_ambro
    (hKNF : KawamataNumericalFreeness.{u}) (hbpf : KltBasePointFreeStatement.{u})
    (hamb : AmbroContractionStatement.{u}) :
    LinearEffectiveFreeness.{u} :=
  linearEffectiveFreeness_of_kawamataNumericalFreeness_of_basePointFree_of_nefAddAmple
    hKNF hbpf semiampleContractionPositiveStatement_holds nefAddAmpleStatement_holds hamb

end MixedFujita
