/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.SGACoherentSerreVanishing
public import MixedFujita.ProperCartierCohomology
public import MixedFujita.SGATwistPullbackIso
public import SGA.Foundations.Cohomology.Devissage

/-! 固定閉部分源への実線冪商写像と連接Serre消滅による切断全射。 See reports/check-238-cohomological-semiampleness-nonvanishing-reduction.json for the verified scope. Coherent Serre vanishing constructs a positive globally generated power on any noetherian scheme. Actual integral cut component ampleness gives original effective-Cartier semiampleness. Dimension induction reduces the unchanged universal nef-plus-ample statement to universal positive-multiple nonvanishing. This nonvanishing assertion, general nef-plus-ample, KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

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


/-- The actual unit pull-push sequence along any closed immersion has a
coherent kernel on a noetherian scheme. -/
theorem closedImmersion_unitPullPush_kernel_isCoherent
    {X Y : Scheme.{u}} [IsNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i] :
    (kernel (CohomologyAux.unitPushPull i (CohomologyAux.unitModule X))).IsCoherent := by
  let O := CohomologyAux.unitModule X
  let : SheafOfModules.isInvertible X O := inferInstance
  let : O.IsCoherent := invertible_module_isCoherent O
  let : O.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let Q := (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj O)
  let : Q.IsQuasicoherent := CohomologyAux.isQuasicoherent_pushforward i _
  have hS := CohomologyAux.shortExact_idealMul i O
  let : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull i O)).X₂.IsCoherent :=
    inferInstanceAs O.IsCoherent
  let : (ShortComplex.kernelSequence (CohomologyAux.unitPushPull i O)).X₁.IsQuasicoherent :=
    CohomologyAux.isQuasicoherent_kernel _
  exact CohomologyAux.isCoherent_X₁_of_shortExact hS


/-- Full coherent Serre vanishing gives eventual surjectivity onto the
actual pulled line power along every fixed closed immersion. The map is
constructed from the twisted unit sequence; no adjunction compatibility
witness or generation hypothesis is supplied. -/
theorem sga_eventually_surjective_to_closed_pullback_of_coherent_serre
    {X Y : Scheme.{u}} [IsNoetherian X] (L : X.LineBundle)
    (hL : ∀ (M : X.Modules) [M.IsCoherent], sgaEventuallyCohomologyVanish L M)
    (i : Y ⟶ X) [IsClosedImmersion i] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ f : L.toModules (n : ℤ) ⟶ (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback i).obj (L.toModules (n : ℤ))),
        Function.Surjective (Scheme.Modules.Hom.app f ⊤) := by
  let O := CohomologyAux.unitModule X
  let S := ShortComplex.kernelSequence (CohomologyAux.unitPushPull i O)
  have hS : S.ShortExact := CohomologyAux.shortExact_idealMul i O
  let : S.X₁.IsCoherent := closedImmersion_unitPullPush_kernel_isCoherent i
  obtain ⟨n₀, hn₀⟩ := hL S.X₁
  refine ⟨n₀, fun n hn => ?_⟩
  let T := S.map (Scheme.LineBundle.twistFunctor X L n)
  have hT : T.ShortExact := Scheme.LineBundle.shortExact_map_twistFunctor L n hS
  have hsurj : Function.Surjective (Scheme.Modules.Hom.app T.g ⊤) :=
    fun t => Scheme.Modules.sections_surjective hT (hn₀ n hn 0) t
  let a : T.X₂ ≅ L.toModules (n : ℤ) := sgaTwistUnitIso L n
  let b : T.X₃ ≅ (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (L.toModules (n : ℤ))) :=
    (Scheme.LineBundle.twistFunctor X L n).mapIso
      ((Scheme.Modules.pushforward i).mapIso (Scheme.Modules.pullbackObjUnitIso i)) ≪≫
    (L.twistPushforwardIso i (CohomologyAux.unitModule Y) n).symm ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (sgaTwistUnitIso (L.pullback i) n ≪≫ (sgaLineBundlePullbackPowerIso L i n).symm)
  refine ⟨a.inv ≫ T.g ≫ b.hom, ?_⟩
  intro t
  obtain ⟨s, hs⟩ := hsurj (Scheme.Modules.Hom.app b.inv ⊤ t)
  refine ⟨Scheme.Modules.Hom.app a.hom ⊤ s, ?_⟩
  change Scheme.Modules.Hom.app b.hom ⊤ (Scheme.Modules.Hom.app T.g ⊤
    (Scheme.Modules.Hom.app a.inv ⊤ (Scheme.Modules.Hom.app a.hom ⊤ s))) = t
  have ha : Scheme.Modules.Hom.app a.inv ⊤ (Scheme.Modules.Hom.app a.hom ⊤ s) = s :=
    ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) a.hom_inv_id) s
  rw [ha, hs]
  exact ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f ⊤) b.inv_hom_id) t

end MixedFujita
