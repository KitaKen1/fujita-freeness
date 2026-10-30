/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.SmoothSchemeComponents

/-!
Connected smooth schemes over a field are integral (step 10, R4-3).

* `connectedSpace_of_idempotent`: a nonempty scheme whose global functions have only the trivial
  idempotents is connected. A clopen subset and its complement are disjoint opens covering the
  scheme; the functions `1` and `0` on them glue to an idempotent, and a nonempty open has nonzero
  functions (its stalks are local rings).
* `idempotent_eq_zero_or_one_of_finrank_eq_one`: over a field `k`, a `k`-algebra of dimension one
  has only the trivial idempotents.
* `isIntegral_of_smooth_of_connectedSpace`: a noetherian connected scheme smooth over a field is
  integral: the stalks are domains, so the irreducible components are disjoint, closed and open
  (`scheme_component_isOpen`).

For the fibre `T_κ` of the closure, check 514 gives `dim_κ Γ(T_κ, O) = dim_K Γ(T, O) = 1`, so
`T_κ` is connected and hence integral.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace MixedFujita

universe u

/-- A function on a nonempty open is nonzero if `1` is. -/
theorem one_ne_zero_of_nonempty_open {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    (1 : Γ(X, U)) ≠ 0 := by
  intro h
  have := congrArg (X.presheaf.germ U x hx) h
  rw [map_one, map_zero] at this
  exact one_ne_zero this

/-- **A scheme whose global functions have only the trivial idempotents is connected.** -/
theorem connectedSpace_of_idempotent {X : Scheme.{u}} [Nonempty X]
    (h : ∀ e : Γ(X, ⊤), e * e = e → e = 0 ∨ e = 1) : ConnectedSpace X := by
  refine { toPreconnectedSpace := ?_, toNonempty := inferInstance }
  refine preconnectedSpace_iff_clopen.2 fun s hs => ?_
  let U : Bool → X.Opens := fun b => if b then ⟨s, hs.2⟩ else ⟨sᶜ, hs.1.isOpen_compl⟩
  have hdisj : U true ⊓ U false ≤ ⊥ := by
    intro x hx
    exact hx.2 hx.1
  have hcov : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hxs : x ∈ s
    · exact ⟨true, hxs⟩
    · exact ⟨false, hxs⟩
  -- sections over the empty intersection agree
  have hempty : ∀ (V : X.Opens), V ≤ ⊥ → ∀ a b : Γ(X, V), a = b := by
    intro V hV a b
    exact X.sheaf.eq_of_locally_eq' (U := (Empty.elim : Empty → X.Opens)) V
      (fun i => i.elim) (by simpa using hV) a b (fun i => i.elim)
  let sf : ∀ b, Γ(X, U b) := fun b => if b then 1 else 0
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U sf := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rfl
    · apply hempty
      cases i <;> cases j
      · exact absurd rfl hij
      · exact inf_comm (U true) (U false) ▸ hdisj
      · exact hdisj
      · exact absurd rfl hij
  obtain ⟨e₀, he₀, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcov sf
    hcompat
  have hres : ∀ (b : Bool) (a : Γ(X, ⊤)), X.sheaf.1.map (homOfLE (le_top : U b ≤ ⊤)).op a =
      X.presheaf.map (homOfLE le_top).op a := fun _ _ => rfl
  have hidem : e₀ * e₀ = e₀ := by
    refine X.sheaf.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hcov _ _ fun b => ?_
    rw [map_mul, he₀ b]
    cases b
    · exact mul_zero _
    · exact mul_one _
  rcases h e₀ hidem with h0 | h1
  · -- the clopen subset is empty
    left
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have h : X.presheaf.map (homOfLE (le_top : U true ≤ ⊤)).op e₀ = 1 :=
      (hres true e₀).symm.trans (he₀ true)
    rw [h0, map_zero] at h
    exact one_ne_zero_of_nonempty_open (U true) x hx h.symm
  · -- the complement is empty
    right
    rw [Set.eq_univ_iff_forall]
    intro x
    by_contra hx
    have h : X.presheaf.map (homOfLE (le_top : U false ≤ ⊤)).op e₀ = 0 :=
      (hres false e₀).symm.trans (he₀ false)
    rw [h1, map_one] at h
    exact one_ne_zero_of_nonempty_open (U false) x hx h

/-- Over a field, a one-dimensional algebra has only the trivial idempotents. -/
theorem idempotent_eq_zero_or_one_of_finrank_eq_one {k B : Type*} [Field k] [CommRing B]
    [Algebra k B] (h : Module.finrank k B = 1) (e : B) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have : Nontrivial B := Module.nontrivial_of_finrank_pos (h ▸ Nat.one_pos)
  have hbot : (⊥ : Subalgebra k B) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hmem : e ∈ (⊥ : Subalgebra k B) := hbot ▸ Algebra.mem_top
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hmem
  rw [← map_mul] at he
  have hc : c * c = c := by
    have hinj : Function.Injective (algebraMap k B) := (algebraMap k B).injective
    exact hinj he
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := c)).1 hc with rfl | rfl
  · left; exact map_zero _
  · right; exact map_one _

/-- **A noetherian connected scheme smooth over a field is integral.** -/
theorem isIntegral_of_smooth_of_connectedSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (g : X ⟶ Spec (CommRingCat.of K)) [Smooth g] [NoetherianSpace X] [ConnectedSpace X] :
    IsIntegral X := by
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := smoothScheme_stalk_isDomain g
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IrreducibleSpace X := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hZ := irreducibleComponent_mem_irreducibleComponents x
    have hopen := scheme_component_isOpen (irreducibleComponent x) hZ
    have hclosed := isClosed_of_mem_irreducibleComponents (irreducibleComponent x) hZ
    have huniv : irreducibleComponent x = Set.univ :=
      (isClopen_iff.1 ⟨hclosed, hopen⟩).resolve_left
        (Set.nonempty_iff_ne_empty.1 ⟨x, mem_irreducibleComponent⟩)
    have hirr : IsIrreducible (Set.univ : Set X) := huniv ▸ hZ.1
    exact { isPreirreducible_univ := hirr.2, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end MixedFujita
