/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentAmpleSerreVanishing
public import MixedFujita.CartierSGAAmplenessDictionary
public import MixedFujita.ClosedImmersionCohomology
public import MixedFujita.CohomologyOneSectionLifting

/-! 実SGA Serre消滅の零層・拡大・閉順像辞書。 See reports/check-237-component-ample-serre-section-lifting.json for the verified scope. Ampleness on actual integral components gives full coherent Serre vanishing on the original possibly nonreduced proper scheme and actual eventual quotient-section lifting on effective Cartier cuts over any field. Component ampleness is an explicit input. The cohomological converse, nonreduced cut global generation, universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Eventual positive-degree cohomology vanishing, with one threshold for
all positive degrees, for a fixed coherent coefficient. -/
def sgaEventuallyCohomologyVanish {X : Scheme.{u}} (L : X.LineBundle)
    (M : X.Modules) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ,
    Subsingleton (Scheme.Modules.Cohomology (L.twist M (n : ℤ)) (q + 1))


/-- An actual ample line bundle on a proper integral source satisfies full
coherent Serre vanishing over every field. -/
theorem sga_isAmple_coherent_serreVanishing
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of K))] [IsProper (X ↘ Spec (CommRingCat.of K))]
    (L : X.LineBundle) (hL : L.IsAmple) (M : X.Modules) [M.IsCoherent] :
    sgaEventuallyCohomologyVanish L M := by
  let D := sgaLineBundleCartierDivisor L
  let a := sgaLineBundleCartierIso L
  have hD := (cartierIsAmpleProj_iff_sga_of_iso K L D a).mpr hL
  obtain ⟨n₀, hn₀⟩ := cartierIsAmpleProj_coherent_tensor_serreVanishing D hD M
  refine ⟨n₀, fun n hn q => ?_⟩
  let := hn₀ n hn q
  exact (actualCohomologyLinearEquivOfIso
    ((sgaTwistTensorIso L M n).symm ≪≫
      tensorIso (sgaLineBundleNatPowerCartierIso L D a n) (Iso.refl M))
    (q + 1)).subsingleton


/-- Vanishing coefficients remain cohomologically zero after any twist. -/
theorem sgaEventuallyCohomologyVanish_zero_sections
    {X : Scheme.{u}} (L : X.LineBundle) (M : X.Modules)
    (hM : ∀ (V : X.Opens) (s : Γ(M, V)), s = 0) :
    sgaEventuallyCohomologyVanish L M := by
  have hid : 𝟙 M = 0 := Scheme.Modules.hom_ext _ _ fun V => by
    ext s
    exact (hM V _).trans (hM V _).symm
  refine ⟨0, fun n _ q => ?_⟩
  have ht : 𝟙 (L.twist M (n : ℤ)) = 0 := by
    calc
      _ = (Scheme.LineBundle.twistFunctor X L n).map (𝟙 M) :=
        ((Scheme.LineBundle.twistFunctor X L n).map_id M).symm
      _ = (Scheme.LineBundle.twistFunctor X L n).map 0 := congrArg _ hid
      _ = 0 := Functor.map_zero _ _ _
  apply subsingleton_of_forall_eq 0
  intro z
  have h := congrArg (fun f => Scheme.Modules.cohomologyMapLinear f (q + 1) z) ht
  simpa only [Scheme.Modules.cohomologyMapLinear_id, LinearMap.id_apply,
    Scheme.Modules.cohomologyMapLinear_zero, LinearMap.zero_apply] using h


/-- Full coherent eventual vanishing is closed under extensions. The
threshold is the maximum of the two internally obtained thresholds. -/
theorem sgaEventuallyCohomologyVanish_of_shortExact
    {X : Scheme.{u}} (L : X.LineBundle) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : sgaEventuallyCohomologyVanish L S.X₁)
    (h₃ : sgaEventuallyCohomologyVanish L S.X₃) :
    sgaEventuallyCohomologyVanish L S.X₂ := by
  obtain ⟨n₁, hn₁⟩ := h₁
  obtain ⟨n₃, hn₃⟩ := h₃
  refine ⟨max n₁ n₃, fun n hn q => ?_⟩
  exact Scheme.Modules.subsingleton_cohomology_X₂
    (Scheme.LineBundle.shortExact_map_twistFunctor L n hS) (q + 1)
    (hn₁ n ((le_max_left _ _).trans hn) q)
    (hn₃ n ((le_max_right _ _).trans hn) q)


/-- Eventual vanishing commutes with an actual closed pushforward. The
source may be nonreduced, reducible or empty. -/
theorem sgaEventuallyCohomologyVanish_closed_pushforward_iff
    {X Y : Scheme.{u}} (L : X.LineBundle) (i : Y ⟶ X) [IsClosedImmersion i]
    (M : Y.Modules) :
    sgaEventuallyCohomologyVanish L ((Scheme.Modules.pushforward i).obj M) ↔
      sgaEventuallyCohomologyVanish (L.pullback i) M := by
  have a (n q : ℕ) :
      Scheme.Modules.Cohomology (L.twist ((Scheme.Modules.pushforward i).obj M) (n : ℤ)) (q + 1) ≃+
        Scheme.Modules.Cohomology ((L.pullback i).twist M (n : ℤ)) (q + 1) :=
    (actualCohomologyLinearEquivOfIso (L.twistPushforwardIso i M n) (q + 1)).toAddEquiv.symm.trans
      (closedImmersionCohomologyAddEquiv i ((L.pullback i).twist M n) (q + 1))
  constructor
  · rintro ⟨n₀, hn₀⟩
    refine ⟨n₀, fun n hn q => ?_⟩
    let := hn₀ n hn q
    exact (a n q).symm.subsingleton
  · rintro ⟨n₀, hn₀⟩
    refine ⟨n₀, fun n hn q => ?_⟩
    let := hn₀ n hn q
    exact (a n q).subsingleton

end MixedFujita
