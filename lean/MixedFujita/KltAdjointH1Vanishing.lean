/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.BirationalExceptionalH1Descent
public import MixedFujita.AmpleTargetCartierPullbackIso
public import MixedFujita.SignedSNCKawamataViehweg
public import MixedFujita.KltRoundupExceptional
public import MixedFujita.HironakaSNCModelExistence
public import MixedFujita.ProperNormalBigAddNef

/-! 通常KVから元klt随伴・全q≥aのBPF用実H1消滅。 See reports/check-242-H1-descent-klt-adjoint-vanishing.json for the verified scope. Actual H1 direct-image descent needs no local higher acyclicity. The usual smooth SNC KV statement implies actual signed-roundup and original projective klt adjoint H1 vanishing. Usual general KV is still an explicit unproved input; klt BPF global generation, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000
open TopCat.Presheaf TopCat.Sheaf
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra functionFieldBaseAlgebra


/-- The usual smooth SNC KV statement supplies H1 vanishing for every
ORIGINAL projective effective klt pair and every nef-and-big adjoint Cartier
class. The actual resolution, roundup, fractional boundary and H1 descent are
all internal; no klt vanishing theorem is used as a separate input. -/
theorem klt_adjoint_H1_vanishing_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (d : ℕ) (hd : 1 ≤ d)
    (D : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX d D)
    (hklt : LogPairIsKlt cX fX d D) (P : CartierDivisor X)
    (hnef : CartierIsNef K (d • P - D)) (hbig : CartierIsBig K (d • P - D)) :
    Subsingleton (Scheme.Modules.Cohomology P.sheaf 1) := by
  obtain ⟨H, hH⟩ := hProj
  obtain ⟨T, hTi, hTo, hTN, hTs, p, hdom, hover, hprop, hp, cT, r, ξ,
      hinj, hξ, hsnc, hsupp, hG, J, hJ⟩ :=
    exists_projective_snc_model_with_ample cX fX d D (fun i : PEmpty.{1} => i.elim) hH
  let := hTi
  let := hTo
  let := hTN
  let := hTs
  let := hdom
  let := hover
  let := hprop
  let : IsProper (T ↘ Spec (CommRingCat.of K)) := by
    rw [← HomIsOver.comp_over (f := p)]
    infer_instance
  let : Smooth (T ↘ Spec (CommRingCat.of K)) := SmoothOfRelativeDimension.smooth n _
  have hnormT : ∀ t : T, IsIntegrallyClosed (T.presheaf.stalk t) :=
    fun t => smooth_stalk_isIntegrallyClosed (K := K) t
  obtain ⟨E, hE, hEc, hexc⟩ := exists_effective_exceptional_klt_boundary_roundup p hp
    hnorm hcov cX fX d hd D heff hklt cT ξ hinj hξ hsnc hsupp
  let C := crepantBoundaryCartier p hp cX fX d D cT etaleCharts_cover
  let fT := crepantPullbackFormUnit p hp cX fX cT
  let P₀ := cartierPullback p P - principalCartierDivisor T fT
  have hadj : d • (P₀ - smoothCanonicalDivisor cT) - C = cartierPullback p (d • P - D) := by
    have hrec := crepantBoundaryCartier_smooth_recombine p hp cX fX d D cT
    dsimp [P₀, C, fT]
    rw [cartierPullback_sub, cartierPullback_nsmul, ← hrec]
    module
  have hnefT : CartierIsNef K (d • (P₀ - smoothCanonicalDivisor cT) - C) := by
    rw [hadj]
    exact cartierIsNef_cartierPullback_of_ample hH hnef p
  have hbigT : CartierIsBig K (d • (P₀ - smoothCanonicalDivisor cT) - C) := by
    rw [hadj]
    exact cartierIsBig_cartierPullback hnorm hnormT p hp
      ((etaleChart_topologicalKrullDim cT).trans (etaleChart_topologicalKrullDim cX).symm) hbig
  have hsrc := signed_snc_roundup_H1_vanishing_of_usual_KV K hKV cT ξ hinj hξ hsnc
    C E P₀ d hd hsupp hEc hnefT hbigT
  have he : (P₀ + E) + principalCartierDivisor T fT = cartierPullback p P + E := by dsimp [P₀]; abel
  let b : (P₀ + E).sheaf ≅ (cartierPullback p P + E).sheaf :=
    (cartierSheafPrincipalShiftIso (P₀ + E) fT).symm ≪≫ eqToIso (congrArg CartierDivisor.sheaf he)
  let : Subsingleton (Scheme.Modules.Cohomology (P₀ + E).sheaf 1) := hsrc
  let : Subsingleton (Scheme.Modules.Cohomology (cartierPullback p P + E).sheaf 1) :=
    (actualCohomologyLinearEquivOfIso b 1).symm.subsingleton
  obtain ⟨aP⟩ := cartierPullback_sheaf_iso_modulePullback_of_ample_target K p H hH P
  let a : ((Scheme.Modules.pullback p).obj P.sheaf ⊗ E.sheaf) ≅
      (cartierPullback p P + E).sheaf := tensorIso aP (Iso.refl _) ≪≫ cartierTensorSheafIso _ _
  exact proper_birational_exceptional_cartier_H1_descent K p hp hnorm hnormT E hE hexc P
    (actualCohomologyLinearEquivOfIso a 1).subsingleton


/-- Under the ORIGINAL klt BPF adjoint hypotheses, usual KV supplies
H1(qD)=0 for EVERY q at least the given integer a. Big-plus-nef and all
roundup/model comparisons are theorems, not additional vanishing inputs. -/
theorem klt_nef_multiples_H1_vanishing_of_usual_KV
    (K : Type u) [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ}
    (hKV : KawamataViehwegVanishingSNC K n)
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (hdim : topologicalKrullDim X = n) (hn : 1 ≤ n)
    (hnorm : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hcov : CodimOneChartCovered n K X)
    (hProj : ∃ H : CartierDivisor X, CartierIsAmpleProj K H)
    (cX : EtaleChart K X n) (fX : X.functionFieldˣ) (r : ℕ) (hr : 1 ≤ r)
    (D' : CartierDivisor X) (heff : LogPairBoundaryEffective cX fX r D')
    (hklt : LogPairIsKlt cX fX r D') (D : CartierDivisor X) (hD : CartierIsNef K D)
    (a : ℕ) (_ha : 1 ≤ a) (hnef : CartierIsNef K ((r * a) • D - D'))
    (hbig : CartierIsBig K ((r * a) • D - D')) (q : ℕ) (hq : a ≤ q) :
    Subsingleton (Scheme.Modules.Cohomology (q • D).sheaf 1) := by
  have he : r • (q • D) - D' = ((r * a) • D - D') + (r * (q - a)) • D := by
    have hqa : r * q = r * a + r * (q - a) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hq]
    rw [smul_smul, hqa, add_nsmul]
    abel
  have htail : CartierIsNef K ((r * (q - a)) • D) := cartierIsNef_nsmul hD _
  apply klt_adjoint_H1_vanishing_of_usual_KV K hKV hnorm hcov hProj cX fX r hr D' heff hklt (q • D)
  · rw [he]
    exact cartierIsNef_add hnef htail
  · rw [he]
    exact proper_normal_cartierIsBig_add_of_isNef K n hdim hn hnorm _ _ hbig htail

end MixedFujita
