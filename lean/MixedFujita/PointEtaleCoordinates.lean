/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreChart
public import MixedFujita.FibreTransversality
public import MixedFujita.LemmaThreeFromRestriction

/-!
Étale coordinates prescribed at a rational point (step 9, generic restriction).

`DifferentialsIndependentAt K χ g`: the differentials of the functions g_l are linearly independent
at the K-point χ, i.e. in K ⊗_{R,χ} Ω_{R/K}. Independence descends along maps of algebras
(`differentialsIndependentAt_of_comp`), and for a product A ⊗ B the functions a_i ⊗ 1 and
1 ⊗ u_l have independent differentials at (ψ, w) when the a_i do at ψ and the u_l at w
(`differentialsIndependentAt_tensor`): restrict to the two slices id ⊗ w and ψ ⊗ id.

On a scheme X smooth of relative dimension N over K, at a K-point x of an affine open V:
* there are N functions on V with independent differentials at x (`exists_differentialsIndependentAt`):
  the differentials of the functions of V span the differentials of the local ring on its residue
  field, which has the dimension N of an étale chart;
* N functions on V with independent differentials at x are the coordinates of an étale chart around
  x inside V (`exists_etaleChart_of_differentialsIndependentAt`): saturating any chart with them as
  tangent coordinates (`exists_fibreChart` with n = 0) and shrinking the chart to where its
  coordinates are the restrictions of the functions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme
open scoped TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

section Independence

variable (K : Type*) [Field K] {R R' : Type*} [CommRing R] [CommRing R'] [Algebra K R]
  [Algebra K R']

/-- The differentials of a family of functions are linearly independent at a K-point χ. -/
def DifferentialsIndependentAt (χ : R →ₐ[K] K) {ι : Type*} (g : ι → R) : Prop :=
  letI := χ.toRingHom.toAlgebra
  LinearIndependent K (fun l => (1 : K) ⊗ₜ[R] KaehlerDifferential.D K R (g l))

variable {K}

/-- Independence of differentials descends along maps of algebras. -/
theorem differentialsIndependentAt_of_comp (f : R →ₐ[K] R') (χ : R' →ₐ[K] K) {ι : Type*}
    (g : ι → R) (h : DifferentialsIndependentAt K χ (f ∘ g)) :
    DifferentialsIndependentAt K (χ.comp f) g := by
  letI : Algebra R R' := f.toRingHom.toAlgebra
  haveI : IsScalarTower K R R' := IsScalarTower.of_algebraMap_eq fun k => (f.commutes k).symm
  letI : Algebra R' K := χ.toRingHom.toAlgebra
  letI : Algebra R K := (χ.comp f).toRingHom.toAlgebra
  haveI : IsScalarTower R R' K := IsScalarTower.of_algebraMap_eq' rfl
  dsimp only [DifferentialsIndependentAt] at h ⊢
  refine LinearIndependent.of_comp (residueKaehlerMap K (R := R) (O' := R') K) ?_
  convert h using 1
  funext l
  rw [Function.comp_apply, residueKaehlerMap_tmul]
  rfl

/-- The functions a_i ⊗ 1 and 1 ⊗ u_l of a product have independent differentials at (ψ, w) when
the a_i have at ψ and the u_l at w. -/
theorem differentialsIndependentAt_tensor {A B : Type*} [CommRing A] [CommRing B] [Algebra K A]
    [Algebra K B] (ψ : A →ₐ[K] K) (w : B →ₐ[K] K) {n d : ℕ} (a : Fin n → A) (u : Fin d → B)
    (ha : DifferentialsIndependentAt K ψ a) (hu : DifferentialsIndependentAt K w u) :
    DifferentialsIndependentAt K (Algebra.TensorProduct.lift ψ w (fun _ _ => Commute.all _ _))
      (Fin.append (fun i => a i ⊗ₜ[K] (1 : B)) (fun l => (1 : A) ⊗ₜ[K] u l)) := by
  classical
  set χ := Algebra.TensorProduct.lift ψ w (fun _ _ => Commute.all _ _) with hχ
  -- the two slices
  let ε₁ : A ⊗[K] B →ₐ[K] A :=
    Algebra.TensorProduct.lift (AlgHom.id K A) ((Algebra.ofId K A).comp w)
      (fun _ _ => Commute.all _ _)
  let ε₂ : A ⊗[K] B →ₐ[K] B :=
    Algebra.TensorProduct.lift ((Algebra.ofId K B).comp ψ) (AlgHom.id K B)
      (fun _ _ => Commute.all _ _)
  have h₁ : ψ.comp ε₁ = χ := by
    ext x
    · simp [ε₁, hχ]
    · simp [ε₁, hχ]
  have h₂ : w.comp ε₂ = χ := by
    ext x
    · simp [ε₂, hχ]
    · simp [ε₂, hχ]
  letI : Algebra (A ⊗[K] B) K := χ.toRingHom.toAlgebra
  dsimp only [DifferentialsIndependentAt] at ha hu ⊢
  rw [Fintype.linearIndependent_iff]
  intro c hc
  rw [Fin.sum_univ_add] at hc
  simp only [Fin.append_left, Fin.append_right] at hc
  -- restrict to the slice id ⊗ w
  have hA : ∀ i, c (Fin.castAdd d i) = 0 := by
    letI : Algebra (A ⊗[K] B) A := ε₁.toRingHom.toAlgebra
    haveI : IsScalarTower K (A ⊗[K] B) A :=
      IsScalarTower.of_algebraMap_eq fun k => (ε₁.commutes k).symm
    letI : Algebra A K := ψ.toRingHom.toAlgebra
    haveI : IsScalarTower (A ⊗[K] B) A K := IsScalarTower.of_algebraMap_eq fun x => by
      change χ x = ψ (ε₁ x)
      rw [← h₁]
      rfl
    have h := congrArg (residueKaehlerMap K (R := A ⊗[K] B) (O' := A) K) hc
    rw [map_add, map_sum, map_sum, map_zero] at h
    simp only [map_smul, residueKaehlerMap_tmul] at h
    have e1 : ∀ i, algebraMap (A ⊗[K] B) A (a i ⊗ₜ[K] (1 : B)) = a i := by
      intro i
      change ε₁ (a i ⊗ₜ[K] (1 : B)) = a i
      simp [ε₁]
    have e2 : ∀ l, algebraMap (A ⊗[K] B) A ((1 : A) ⊗ₜ[K] u l) = algebraMap K A (w (u l)) := by
      intro l
      change ε₁ ((1 : A) ⊗ₜ[K] u l) = _
      simp [ε₁]
    simp only [e1, e2, Derivation.map_algebraMap, TensorProduct.tmul_zero, smul_zero,
      Finset.sum_const_zero, add_zero] at h
    exact Fintype.linearIndependent_iff.mp ha (fun i => c (Fin.castAdd d i)) h
  -- restrict to the slice ψ ⊗ id
  have hB : ∀ l, c (Fin.natAdd n l) = 0 := by
    letI : Algebra (A ⊗[K] B) B := ε₂.toRingHom.toAlgebra
    haveI : IsScalarTower K (A ⊗[K] B) B :=
      IsScalarTower.of_algebraMap_eq fun k => (ε₂.commutes k).symm
    letI : Algebra B K := w.toRingHom.toAlgebra
    haveI : IsScalarTower (A ⊗[K] B) B K := IsScalarTower.of_algebraMap_eq fun x => by
      change χ x = w (ε₂ x)
      rw [← h₂]
      rfl
    have h := congrArg (residueKaehlerMap K (R := A ⊗[K] B) (O' := B) K) hc
    rw [map_add, map_sum, map_sum, map_zero] at h
    simp only [map_smul, residueKaehlerMap_tmul] at h
    have e1 : ∀ i, algebraMap (A ⊗[K] B) B (a i ⊗ₜ[K] (1 : B)) = algebraMap K B (ψ (a i)) := by
      intro i
      change ε₂ (a i ⊗ₜ[K] (1 : B)) = _
      simp [ε₂]
    have e2 : ∀ l, algebraMap (A ⊗[K] B) B ((1 : A) ⊗ₜ[K] u l) = u l := by
      intro l
      change ε₂ ((1 : A) ⊗ₜ[K] u l) = u l
      simp [ε₂]
    simp only [e1, e2, Derivation.map_algebraMap, TensorProduct.tmul_zero, smul_zero,
      Finset.sum_const_zero, zero_add] at h
    exact Fintype.linearIndependent_iff.mp hu (fun l => c (Fin.natAdd n l)) h
  intro j
  induction j using Fin.addCases with
  | left i => exact hA i
  | right l => exact hB l

end Independence

section Span

variable (K : Type*) [Field K] {R O F : Type*} [CommRing R] [CommRing O] [Field F]
  [Algebra K O] [Algebra R O] [Algebra O F]

/-- On a field over a localization, the differentials of the functions of the ring span. -/
theorem span_tmul_D_algebraMap_eq_top (M : Submonoid R) [IsLocalization M O] :
    Submodule.span F (Set.range fun r : R =>
      (1 : F) ⊗ₜ[O] KaehlerDifferential.D K O (algebraMap R O r)) = ⊤ := by
  set S := Submodule.span F (Set.range fun r : R =>
      (1 : F) ⊗ₜ[O] KaehlerDifferential.D K O (algebraMap R O r)) with hS
  have hmem : ∀ r : R, (1 : F) ⊗ₜ[O] KaehlerDifferential.D K O (algebraMap R O r) ∈ S :=
    fun r => Submodule.subset_span ⟨r, rfl⟩
  have key : ∀ o : O, (1 : F) ⊗ₜ[O] KaehlerDifferential.D K O o ∈ S := by
    intro o
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective M o
    set o' := IsLocalization.mk' O r s
    have hrs : algebraMap R O (s : R) * o' = algebraMap R O r := IsLocalization.mk'_spec' O r s
    have hD : algebraMap R O (s : R) • KaehlerDifferential.D K O o' =
        KaehlerDifferential.D K O (algebraMap R O r) -
          o' • KaehlerDifferential.D K O (algebraMap R O (s : R)) := by
      rw [← hrs, Derivation.leibniz, add_sub_cancel_right]
    have hunit : IsUnit (algebraMap O F (algebraMap R O (s : R))) :=
      (IsLocalization.map_units O s).map _
    have h1 : (1 : F) ⊗ₜ[O] (algebraMap R O (s : R) • KaehlerDifferential.D K O o') =
        algebraMap O F (algebraMap R O (s : R)) • ((1 : F) ⊗ₜ[O] KaehlerDifferential.D K O o') := by
      rw [TensorProduct.tmul_smul]
      exact (algebraMap_smul F (algebraMap R O (s : R)) _).symm
    have h2 : (1 : F) ⊗ₜ[O] (algebraMap R O (s : R) • KaehlerDifferential.D K O o') ∈ S := by
      rw [hD, TensorProduct.tmul_sub, TensorProduct.tmul_smul, ← algebraMap_smul F o' (_ : F ⊗[O] Ω[O⁄K])]
      exact Submodule.sub_mem _ (hmem r) (Submodule.smul_mem _ _ (hmem s))
    rw [h1] at h2
    exact (Submodule.smul_mem_iff S hunit.ne_zero).mp h2
  rw [eq_top_iff]
  rintro x -
  induction x with
  | tmul a ω =>
    have hω : ω ∈ Submodule.span O (Set.range (KaehlerDifferential.D K O)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    have h1 : (1 : F) ⊗ₜ[O] ω ∈ S := by
      induction hω using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨o, rfl⟩ := hy
        exact key o
      | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact add_mem hy hz
      | smul c y _ hy =>
        rw [TensorProduct.tmul_smul, ← algebraMap_smul F c]
        exact Submodule.smul_mem _ _ hy
    have h2 : a ⊗ₜ[O] ω = a • ((1 : F) ⊗ₜ[O] ω) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  | add x y hx hy => exact add_mem hx hy

/-- If the differentials of a localization have a basis of N elements on a field, then N functions
of the ring have independent differentials there. -/
theorem exists_linearIndependent_tmul_D_algebraMap (M : Submonoid R) [IsLocalization M O] {N : ℕ}
    (b : Module.Basis (Fin N) F (F ⊗[O] Ω[O⁄K])) :
    ∃ g : Fin N → R, LinearIndependent F
      (fun l => (1 : F) ⊗ₜ[O] KaehlerDifferential.D K O (algebraMap R O (g l))) := by
  classical
  set v : R → F ⊗[O] Ω[O⁄K] := fun r => (1 : F) ⊗ₜ[O] KaehlerDifferential.D K O (algebraMap R O r)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' F v
  have hsp' : ⊤ ≤ Submodule.span F (Set.range (v ∘ a)) := by
    rw [hsp, span_tmul_D_algebraMap_eq_top K M]
  let b' : Module.Basis κ F (F ⊗[O] Ω[O⁄K]) := Module.Basis.mk hli hsp'
  let e : Fin N ≃ κ := b.indexEquiv b'
  refine ⟨fun l => a (e l), ?_⟩
  have h := hli.comp e e.injective
  simpa [v, Function.comp_def] using h

end Span

section Charts

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- Changing the dimension index of a chart along an equality. -/
theorem exists_etaleChart_cast {m n : ℕ} (c : EtaleChart K X m) (h : m = n) :
    ∃ c' : EtaleChart K X n, c'.U = c.U ∧ ∀ (x : X) (hx : x ∈ c.U) (hx' : x ∈ c'.U) (i : Fin n),
      etaleChartStalkCoords c' x hx' (MvPolynomial.X i) =
        etaleChartStalkCoords c x hx (MvPolynomial.X (Fin.cast h.symm i)) := by
  subst h
  exact ⟨c, rfl, fun x hx hx' i => rfl⟩

/-- A chart at η all of whose coordinates are prescribed germs with independent differentials on a
field over the stalk. -/
theorem exists_etaleChart_of_linearIndependent {N : ℕ} (η : X) (c : EtaleChart K X N)
    (hη : η ∈ c.U) (h : Fin N → X.presheaf.stalk η) (F : Type*) [Field F]
    [Algebra (X.presheaf.stalk η) F]
    (hF : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk η),
      algebraMap (X.presheaf.stalk η) F x = 0)
    (hind : LinearIndependent F (fun l => (1 : F) ⊗ₜ[X.presheaf.stalk η]
      KaehlerDifferential.D K (X.presheaf.stalk η) (h l))) :
    ∃ (c' : EtaleChart K X N) (hη' : η ∈ c'.U), c'.U ≤ c.U ∧
      ∀ l, etaleChartStalkCoords c' η hη' (MvPolynomial.X l) = h l := by
  classical
  obtain ⟨c₀, hc₀U, hc₀⟩ := exists_etaleChart_cast c (Nat.zero_add N).symm
  have hη₀ : η ∈ c₀.U := hc₀U ▸ hη
  have hsnc : IsSNCChart c₀ (Fin.elim0 : Fin 0 → X) (Fin.elim0 : Fin 0 → Option (Fin (0 + N))) :=
    ⟨fun i => i.elim0, fun i => i.elim0⟩
  have hind' : LinearIndependent F (Sum.elim
      (fun a : {a : Fin (0 + N) // ∃ k : Fin 0,
          (Fin.elim0 k : Option (Fin (0 + N))) = some a ∧
            η ∈ closure ({(Fin.elim0 k : X)} : Set X)} =>
        (1 : F) ⊗ₜ[X.presheaf.stalk η] KaehlerDifferential.D K (X.presheaf.stalk η)
          (etaleChartStalkCoords c₀ η hη₀ (MvPolynomial.X a.1)))
      (fun l => (1 : F) ⊗ₜ[X.presheaf.stalk η] KaehlerDifferential.D K (X.presheaf.stalk η)
        (h l))) := by
    haveI : IsEmpty {a : Fin (0 + N) // ∃ k : Fin 0,
        (Fin.elim0 k : Option (Fin (0 + N))) = some a ∧
          η ∈ closure ({(Fin.elim0 k : X)} : Set X)} :=
      ⟨fun a => a.2.elim fun k _ => k.elim0⟩
    refine LinearIndependent.sum_type (linearIndependent_empty_type) hind ?_
    rw [Set.range_eq_empty, Submodule.span_empty]
    exact disjoint_bot_left
  obtain ⟨Fc, hFc, σF, hle, -, -, hcoord⟩ :=
    exists_fibreChart (n := 0) (d := N) (Fin.elim0 : Fin 0 → X)
      (Fin.elim0 : Fin 0 → Option (Fin (0 + N))) η c₀ hη₀ hsnc h F hF hind'
  obtain ⟨c', hc'U, hc'⟩ := exists_etaleChart_cast Fc (Nat.zero_add N)
  have hη' : η ∈ c'.U := hc'U ▸ hFc
  refine ⟨c', hη', ?_, fun l => ?_⟩
  · rw [hc'U]
    exact hle.trans (le_of_eq hc₀U)
  · rw [hc' η hFc hη' l, ← hcoord l]
    congr 2
    exact Fin.ext (by simp)

/-- Restriction of sections between opens composes. -/
theorem presheaf_map_map_eq {U₁ U₂ U₃ : X.Opens} (i₁ : U₂ ⟶ U₁) (i₂ : U₃ ⟶ U₂) (i₃ : U₃ ⟶ U₁)
    (s : Γ(X, U₁)) : X.presheaf.map i₂.op (X.presheaf.map i₁.op s) = X.presheaf.map i₃.op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- A chart whose stalk coordinates at x are the germs of sections over an open W₀ can be shrunk
to a chart inside W₀ whose coordinates are the restrictions of these sections. -/
theorem exists_etaleChart_coords_eq_restrict {N : ℕ} (c : EtaleChart K X N) (x : X)
    (hx : x ∈ c.U) (W₀ : X.Opens) (hxW₀ : x ∈ W₀) (g : Fin N → Γ(X, W₀))
    (hg : ∀ i, etaleChartStalkCoords c x hx (MvPolynomial.X i) =
      X.presheaf.germ W₀ x hxW₀ (g i)) :
    ∃ (c' : EtaleChart K X N) (_ : x ∈ c'.U) (hle : c'.U ≤ W₀), c'.U ≤ c.U ∧
      ∀ i, c'.coords (MvPolynomial.X i) = X.presheaf.map (homOfLE hle).op (g i) := by
  classical
  have hloc : ∀ i, ∃ (W : X.Opens) (_ : x ∈ W) (iU : W ⟶ c.U) (iV : W ⟶ W₀),
      X.presheaf.map iU.op (c.coords (MvPolynomial.X i)) = X.presheaf.map iV.op (g i) :=
    fun i => TopCat.Presheaf.germ_eq X.presheaf x hx hxW₀ _ _ (hg i)
  choose W hxW iU iV hW using hloc
  let V : X.Opens := ⟨(⋂ i, (W i : Set X)) ∩ W₀,
    (isOpen_iInter_of_finite fun i => (W i).isOpen).inter W₀.isOpen⟩
  have hxV : x ∈ V := ⟨Set.mem_iInter.mpr hxW, hxW₀⟩
  obtain ⟨f, hfV, hxf⟩ := c.isAffine.exists_basicOpen_le (V := V) ⟨x, hxV⟩ hx
  have hfW₀ : X.basicOpen f ≤ W₀ := fun z hz => (hfV hz).2
  have hfW : ∀ i, X.basicOpen f ≤ W i := fun i z hz => Set.mem_iInter.mp (hfV hz).1 i
  refine ⟨etaleChartBasicOpen c f ⟨⟨x, hxf⟩⟩, hxf, hfW₀, X.basicOpen_le f, fun i => ?_⟩
  change X.presheaf.map (homOfLE (X.basicOpen_le f)).op (c.coords (MvPolynomial.X i)) = _
  rw [← presheaf_map_map_eq (iU i) (homOfLE (hfW i)) (homOfLE (X.basicOpen_le f)), hW i]
  exact presheaf_map_map_eq (iV i) (homOfLE (hfW i)) (homOfLE hfW₀) (g i)

variable {N : ℕ} [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of K))]

omit [SmoothOfRelativeDimension N (X ↘ Spec (CommRingCat.of K))] in
/-- The evaluation of the local ring of a K-point. -/
theorem exists_stalk_evaluation {V : X.Opens} (hV : IsAffineOpen V) (x : X) (hx : x ∈ V)
    (χ : Γ(X, V) →ₐ[K] K) (hχ : ∀ a, χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
    ∃ ev : X.presheaf.stalk x →+* K,
      (∀ a, ev (algebraMap Γ(X, V) (X.presheaf.stalk x) a) = χ a) ∧
      ∀ y ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x), ev y = 0 := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk (⟨x, hx⟩ : V)
  have hunits : ∀ y : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      IsUnit (χ.toRingHom (y : Γ(X, V))) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h0 => y.2 ((hχ _).mp h0)
  refine ⟨IsLocalization.lift hunits, fun a => IsLocalization.lift_eq hunits a, fun y hy => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl y
  have ha : a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal :=
    (IsLocalization.AtPrime.mk'_mem_maximal_iff _ _ a s).mp hy
  rw [IsLocalization.lift_mk']
  change χ a * _ = 0
  rw [(hχ a).mpr ha, zero_mul]

/-- N functions on an affine open with independent differentials at a K-point x. -/
theorem exists_differentialsIndependentAt {V : X.Opens} (hV : IsAffineOpen V) (x : X)
    (hx : x ∈ V) (χ : Γ(X, V) →ₐ[K] K)
    (hχ : ∀ a, χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) :
    ∃ g : Fin N → Γ(X, V), DifferentialsIndependentAt K χ g := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk (⟨x, hx⟩ : V)
  haveI := cartierBaseOpenLocalScalarTower (K := K) x hx
  obtain ⟨ev, hev, -⟩ := exists_stalk_evaluation hV x hx χ hχ
  letI : Algebra (X.presheaf.stalk x) K := ev.toAlgebra
  letI : Algebra Γ(X, V) K := χ.toRingHom.toAlgebra
  haveI : IsScalarTower Γ(X, V) (X.presheaf.stalk x) K :=
    IsScalarTower.of_algebraMap_eq fun a => (hev a).symm
  obtain ⟨c, hc⟩ : ∃ c : EtaleChart K X N, x ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := N)).symm ▸ Opens.mem_top x)
  have hb := (etaleCoordinateBasis _ (etaleChartStalkCoords_formallyEtale c x hc)).baseChange K
  obtain ⟨g, hg⟩ := exists_linearIndependent_tmul_D_algebraMap K
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl hb
  refine ⟨g, ?_⟩
  dsimp only [DifferentialsIndependentAt]
  refine LinearIndependent.of_comp (residueKaehlerMap K (R := Γ(X, V))
    (O' := X.presheaf.stalk x) K) ?_
  convert hg using 1
  funext l
  rw [Function.comp_apply, residueKaehlerMap_tmul]

/-- N functions on an affine open with independent differentials at a K-point x are the
coordinates of an étale chart around x inside the open. -/
theorem exists_etaleChart_of_differentialsIndependentAt {V : X.Opens} (hV : IsAffineOpen V)
    (x : X) (hx : x ∈ V) (χ : Γ(X, V) →ₐ[K] K)
    (hχ : ∀ a, χ a = 0 ↔ a ∈ (hV.primeIdealOf ⟨x, hx⟩).asIdeal) (g : Fin N → Γ(X, V))
    (hg : DifferentialsIndependentAt K χ g) :
    ∃ (c : EtaleChart K X N) (_ : x ∈ c.U) (hle : c.U ≤ V),
      ∀ i, c.coords (MvPolynomial.X i) = X.presheaf.map (homOfLE hle).op (g i) := by
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk (⟨x, hx⟩ : V)
  haveI := cartierBaseOpenLocalScalarTower (K := K) x hx
  obtain ⟨ev, hev, hev0⟩ := exists_stalk_evaluation hV x hx χ hχ
  letI : Algebra (X.presheaf.stalk x) K := ev.toAlgebra
  letI : Algebra Γ(X, V) K := χ.toRingHom.toAlgebra
  haveI : IsScalarTower Γ(X, V) (X.presheaf.stalk x) K :=
    IsScalarTower.of_algebraMap_eq fun a => (hev a).symm
  haveI : Algebra.FormallySmooth Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallySmooth.of_isLocalization (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  dsimp only [DifferentialsIndependentAt] at hg
  have hind := hg.map' (residueKaehlerMap K (R := Γ(X, V)) (O' := X.presheaf.stalk x) K)
    (LinearMap.ker_eq_bot.mpr (residueKaehlerMap_injective K K))
  have hind' : LinearIndependent K (fun l => (1 : K) ⊗ₜ[X.presheaf.stalk x]
      KaehlerDifferential.D K (X.presheaf.stalk x) (X.presheaf.germ V x hx (g l))) := by
    convert hind using 1
    funext l
    rw [Function.comp_apply, residueKaehlerMap_tmul]
    rfl
  obtain ⟨c₀, hc₀⟩ : ∃ c : EtaleChart K X N, x ∈ c.U :=
    Opens.mem_iSup.mp ((etaleCharts_cover (K := K) (X := X) (n := N)).symm ▸ Opens.mem_top x)
  obtain ⟨c₁, hc₁, -, hcoord⟩ := exists_etaleChart_of_linearIndependent x c₀ hc₀
    (fun l => X.presheaf.germ V x hx (g l)) K hev0 hind'
  obtain ⟨c, hxc, hle, -, hc⟩ := exists_etaleChart_coords_eq_restrict c₁ x hc₁ V hx g hcoord
  exact ⟨c, hxc, hle, hc⟩

end Charts

end MixedFujita
