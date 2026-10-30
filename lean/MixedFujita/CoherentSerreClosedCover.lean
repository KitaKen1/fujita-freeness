/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module
public import MixedFujita.CoherentSerreSupportDevissage

/-! 有限閉被覆と整既約成分上amplenessから非被約全体のSerre消滅。 See reports/check-237-component-ample-serre-section-lifting.json for the verified scope. Ampleness on actual integral components gives full coherent Serre vanishing on the original possibly nonreduced proper scheme and actual eventual quotient-section lifting on effective Cartier cuts over any field. Component ampleness is an explicit input. The cohomological converse, nonreduced cut global generation, universal nef-plus-ample semiampleness, general KV, klt BPF, Ambro and full F1/F2 remain unproved. -/

@[expose] public section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Opposite Limits MonoidalCategory
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme
namespace MixedFujita
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra


/-- Full coherent Serre vanishing glues across any finite actual closed
cover, including all nilpotent layers on the ambient scheme. -/
theorem sga_coherent_serreVanishing_of_finite_closed_cover
    {X : Scheme.{u}} [IsNoetherian X] (L : X.LineBundle)
    {ι : Type u} [Finite ι] (Z : ι → Scheme.{u}) (i : ∀ a, Z a ⟶ X)
    [∀ a, IsClosedImmersion (i a)]
    (hcover : ⋃ a, Set.range (i a) = Set.univ)
    (hZ : ∀ a (M : (Z a).Modules) [M.IsCoherent],
      sgaEventuallyCohomologyVanish (L.pullback (i a)) M)
    (M : X.Modules) [M.IsCoherent] : sgaEventuallyCohomologyVanish L M := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let P := sgaEventuallyCohomologyVanish L
  have hzero : ∀ N : X.Modules, N.IsCoherent → (∀ V (s : Γ(N, V)), s = 0) → P N :=
    fun N _ hN => sgaEventuallyCohomologyVanish_zero_sections L N hN
  have hext : ∀ S : ShortComplex X.Modules, S.ShortExact → S.X₁.IsCoherent →
      S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂ :=
    fun S hS _ _ _ h₁ h₃ => sgaEventuallyCohomologyVanish_of_shortExact L hS h₁ h₃
  have hsingle (a : ι) (N : X.Modules) [N.IsCoherent]
      (hN : CohomologyAux.VanishesOff N (Set.range (i a))) : P N := by
    apply CohomologyAux.prop_of_vanishesOff_range P hzero hext (i a) ?_ N hN
    intro Q hQ
    let := hQ
    let : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
    let : Q.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
    let : ((Scheme.Modules.pullback (i a)).obj Q).IsCoherent := ⟨inferInstance, inferInstance⟩
    exact (sgaEventuallyCohomologyVanish_closed_pushforward_iff L (i a) _).mpr (hZ a _)
  have hfinite (s : Finset ι) : ∀ (N : X.Modules) [N.IsCoherent],
      CohomologyAux.VanishesOff N (⋃ a ∈ s, Set.range (i a)) → P N := by
    induction s using Finset.induction_on with
    | empty =>
      intro N _ hN
      have hN' : CohomologyAux.VanishesOff N ∅ := by simpa only [Finset.notMem_empty,
        Set.iUnion_of_empty, Set.iUnion_empty] using hN
      exact hzero N inferInstance (fun V t => hN' V (Set.disjoint_empty _) t)
    | @insert a s ha ih =>
      intro N _ hN
      have hunion : (⋃ b ∈ insert a s, Set.range (i b)) =
          (⋃ b ∈ s, Set.range (i b)) ∪ Set.range (i a) := by ext x; simp [or_comm]
      rw [hunion] at hN
      exact CohomologyAux.prop_of_vanishesOff_union P hext
        (i a).isClosedEmbedding.isClosed_range
        (fun Q hQ hsmall => @ih Q hQ hsmall)
        (fun Q hQ hsmall => @hsingle a Q hQ hsmall) N hN
  apply hfinite Finset.univ M
  have htop : (⋃ a ∈ (Finset.univ : Finset ι), Set.range (i a)) = Set.univ := by
    simpa only [Finset.mem_univ, Set.iUnion_true] using hcover
  rw [htop]
  exact CohomologyAux.vanishesOff_univ M


/-- It suffices to check ampleness on the integral schemes of the finitely
many irreducible components. The ambient scheme retains its nilpotents. -/
theorem proper_sga_coherent_serreVanishing_of_component_ample
    (K : Type u) [Field K] {Y : Scheme.{u}}
    [Y.Over (Spec (CommRingCat.of K))] [IsProper (Y ↘ Spec (CommRingCat.of K))]
    (L : Y.LineBundle)
    (hL : ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z],
      Set.range i ∈ irreducibleComponents Y → (L.pullback i).IsAmple)
    (M : Y.Modules) [M.IsCoherent] : sgaEventuallyCohomologyVanish L M := by
  classical
  let := properOverField_scheme_isNoetherian (K := K) (X := Y)
  let ι := {T : Set Y // T ∈ irreducibleComponents Y}
  let : Finite ι := NoetherianSpace.finite_irreducibleComponents.to_subtype
  choose Z i hi hZ hrange using fun a : ι =>
    CohomologyAux.exists_integral_closedImmersion a.val
      (isClosed_of_mem_irreducibleComponents a.val a.property) a.property.1
  let : ∀ a, IsClosedImmersion (i a) := hi
  let : ∀ a, IsIntegral (Z a) := hZ
  have hcover : ⋃ a, Set.range (i a) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    let a : ι := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    exact Set.mem_iUnion.mpr ⟨a, (hrange a).symm ▸ mem_irreducibleComponent⟩
  apply sga_coherent_serreVanishing_of_finite_closed_cover L Z i hcover ?_ M
  intro a N _
  let : (Z a).Over (Spec (CommRingCat.of K)) := ⟨i a ≫ (Y ↘ Spec (CommRingCat.of K))⟩
  let : IsProper (Z a ↘ Spec (CommRingCat.of K)) := by
    change IsProper (i a ≫ (Y ↘ Spec (CommRingCat.of K)))
    infer_instance
  exact sga_isAmple_coherent_serreVanishing K (L.pullback (i a))
    (hL (Z a) (i a) ((hrange a).symm ▸ a.property)) N

end MixedFujita
