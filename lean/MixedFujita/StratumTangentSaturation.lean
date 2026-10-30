/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.CartierSectionBertini
public import MixedFujita.RelativeCanonicalDivisor

/-!
Tangent coordinates at a point of a simple normal crossing chart (section 5.1 of the manuscript,
the choice of the tangent directions of the image of the centre).

Let η be a point of a simple normal crossing chart and H a set of germs at η, for instance the
pullbacks of the germs of functions on the base. The chart can be changed near η so that some of
the coordinates that do not belong to the family are germs of H (the tangent coordinates) and
every germ of H has all its derivatives in the remaining free coordinates in the maximal ideal of
η: as long as some germ h of H has a derivative in a free coordinate b that is a unit at η, the
coordinate b is replaced by h on a smaller chart, and this happens at most n times. The family
coordinates are never replaced, so the chart stays in simple normal crossing position.

No generic smoothness is used: the statement is the maximality of the set of tangent coordinates.

* The coordinate derivations only depend on the coordinates; the stalk coordinates of the
  restriction of a chart to a basic open and of a chart with one coordinate replaced.
* Replacing a coordinate that does not belong to the family keeps the simple normal crossing
  position.
* The saturation.
* The germs all of whose derivatives in a given set of coordinates lie in the maximal ideal form a
  K-subalgebra that contains the inverses of its units.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open TauCeti.AlgebraicGeometry.Scheme

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false

universe u

section Algebra

variable {K S : Type*} [Field K] [CommRing S] [Algebra K S] {n : ℕ}

/-- The coordinate derivations only depend on the coordinates. -/
theorem etaleCoordinateDerivation_congr {y y' : MvPolynomial (Fin n) K →ₐ[K] S} (h : y = y')
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale) (j : Fin n) :
    etaleCoordinateDerivation y hy j = etaleCoordinateDerivation y' hy' j := by
  subst h
  rfl

/-- The elements of a local K-algebra all of whose derivatives in the coordinates of a set F lie
in the maximal ideal. -/
def coordinateConstantSubalgebra [IsLocalRing S] (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (F : Set (Fin n)) : Subalgebra K S where
  carrier := {s | ∀ b ∈ F, etaleCoordinateDerivation y hy b s ∈ IsLocalRing.maximalIdeal S}
  mul_mem' := by
    intro s t hs ht b hb
    rw [Derivation.leibniz]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (ht b hb)) (Ideal.mul_mem_left _ _ (hs b hb))
  add_mem' := by
    intro s t hs ht b hb
    rw [map_add]
    exact Ideal.add_mem _ (hs b hb) (ht b hb)
  algebraMap_mem' := by
    intro k b _
    rw [Derivation.map_algebraMap]
    exact Ideal.zero_mem _

theorem mem_coordinateConstantSubalgebra [IsLocalRing S] (y : MvPolynomial (Fin n) K →ₐ[K] S)
    (hy : y.toRingHom.FormallyEtale) (F : Set (Fin n)) (s : S) :
    s ∈ coordinateConstantSubalgebra y hy F ↔
      ∀ b ∈ F, etaleCoordinateDerivation y hy b s ∈ IsLocalRing.maximalIdeal S :=
  Iff.rfl

/-- The subalgebra contains the inverses of its units. -/
theorem coordinateConstantSubalgebra_of_mul_eq_one [IsLocalRing S]
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) (F : Set (Fin n))
    {s t : S} (hs : s ∈ coordinateConstantSubalgebra y hy F) (hst : s * t = 1) :
    t ∈ coordinateConstantSubalgebra y hy F := by
  intro b hb
  have h := congrArg (etaleCoordinateDerivation y hy b) hst
  rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
  -- s ∂t = - t ∂s
  have h1 : s * etaleCoordinateDerivation y hy b t =
      -(t * etaleCoordinateDerivation y hy b s) := eq_neg_of_add_eq_zero_left h
  have h2 : etaleCoordinateDerivation y hy b t =
      t * (s * etaleCoordinateDerivation y hy b t) := by
    rw [← mul_assoc, mul_comm t s, hst, one_mul]
  rw [h2, h1]
  exact Ideal.mul_mem_left _ _ (Ideal.neg_mem_iff _ |>.mpr (Ideal.mul_mem_left _ _ (hs b hb)))

/-- A quotient a/b of two elements of the subalgebra with b a unit lies in the subalgebra. -/
theorem coordinateConstantSubalgebra_of_mul_eq [IsLocalRing S]
    (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale) (F : Set (Fin n))
    {a b s : S} (ha : a ∈ coordinateConstantSubalgebra y hy F)
    (hb : b ∈ coordinateConstantSubalgebra y hy F) (hbu : IsUnit b) (hs : s * b = a) :
    s ∈ coordinateConstantSubalgebra y hy F := by
  obtain ⟨u, rfl⟩ := hbu
  have hinv : ((u⁻¹ : Sˣ) : S) ∈ coordinateConstantSubalgebra y hy F :=
    coordinateConstantSubalgebra_of_mul_eq_one y hy F hb (Units.mul_inv u)
  have : s = a * ((u⁻¹ : Sˣ) : S) := by
    rw [← hs, mul_assoc, Units.mul_inv, mul_one]
  rw [this]
  exact Subalgebra.mul_mem _ ha hinv

end Algebra

section Charts

variable {K : Type u} [Field K] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))] {n : ℕ}

attribute [local instance] cartierGlobalStalkAlgebra cartierBaseGlobalAlgebra
  cartierBaseLocalAlgebra cartierBaseOpenAlgebra

/-- The stalk coordinates of the restriction of a chart to a basic open. -/
theorem etaleChartStalkCoords_basicOpen (c : EtaleChart K X n) (g : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen g)) (x : X) (hx : x ∈ X.basicOpen g) :
    etaleChartStalkCoords (etaleChartBasicOpen c g hne) x hx =
      etaleChartStalkCoords c x (X.basicOpen_le g hx) := by
  apply AlgHom.ext
  intro p
  change X.presheaf.germ (X.basicOpen g) x hx
    (X.presheaf.map (homOfLE (X.basicOpen_le g)).op (c.coords p)) = X.presheaf.germ c.U x _ (c.coords p)
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _

/-- The replaced stalk coordinate. -/
theorem etaleChartStalkCoords_replace_self (c : EtaleChart K X n) (j : Fin n) (h : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h)))
    (x : X) (hx : x ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h)) :
    etaleChartStalkCoords (etaleChartReplace c j h hne) x hx (MvPolynomial.X j) =
      X.presheaf.germ c.U x (X.basicOpen_le _ hx) h := by
  change X.presheaf.germ (etaleChartReplace c j h hne).U x hx
    ((etaleChartReplace c j h hne).coords (MvPolynomial.X j)) = _
  rw [etaleChartReplace_coords_self]
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _

/-- The other stalk coordinates of a chart with one coordinate replaced. -/
theorem etaleChartStalkCoords_replace_ne (c : EtaleChart K X n) (j : Fin n) (h : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h)))
    (x : X) (hx : x ∈ X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h))
    {i : Fin n} (hij : i ≠ j) :
    etaleChartStalkCoords (etaleChartReplace c j h hne) x hx (MvPolynomial.X i) =
      etaleChartStalkCoords c x (X.basicOpen_le _ hx) (MvPolynomial.X i) := by
  change X.presheaf.germ (etaleChartReplace c j h hne).U x hx
    ((etaleChartReplace c j h hne).coords (MvPolynomial.X i)) = _
  rw [etaleChartReplace_coords_ne c j h hne hij]
  exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _

/-- The germ of a coordinate derivative on a chart is the coordinate derivative of the germ. -/
theorem etaleChart_germ_coordinateDerivation (c : EtaleChart K X n) (x : X) (hx : x ∈ c.U)
    (j : Fin n) (s : Γ(X, c.U)) :
    X.presheaf.germ c.U x hx (etaleCoordinateDerivation c.coords c.formallyEtale j s) =
      etaleCoordinateDerivation (etaleChartStalkCoords c x hx)
        (etaleChartStalkCoords_formallyEtale c x hx) j (X.presheaf.germ c.U x hx s) :=
  (etaleCoordinateDerivation_comp (sectionStalkAlgHom (K := K) c.U x hx) c.coords c.formallyEtale
    (etaleChartStalkCoords_formallyEtale c x hx) j s).symm

/-- Replacing a coordinate that does not belong to the family keeps the simple normal crossing
position. -/
theorem isSNCChart_etaleChartReplace {c : EtaleChart K X n} {r : ℕ} {ξ : Fin r → X}
    {σ : Fin r → Option (Fin n)} (hc : IsSNCChart c ξ σ) (j : Fin n) (hj : ∀ k, σ k ≠ some j)
    (h : Γ(X, c.U))
    (hne : Nonempty (X.basicOpen (etaleCoordinateDerivation c.coords c.formallyEtale j h))) :
    IsSNCChart (etaleChartReplace c j h hne) ξ σ := by
  have h0 := isSNCChart_basicOpen hc (etaleCoordinateDerivation c.coords c.formallyEtale j h) hne
  refine ⟨h0.1, fun i => ?_⟩
  have hi := h0.2 i
  cases hσ : σ i with
  | none =>
    rw [hσ] at hi
    exact hi
  | some a =>
    rw [hσ] at hi
    have haj : a ≠ j := fun e => hj i (e ▸ hσ)
    change closure ({ξ i} : Set X) ∩ X.basicOpen _ = X.zeroLocus
      ({(etaleChartReplace c j h hne).coords (MvPolynomial.X a)} : Set Γ(X, X.basicOpen _)) ∩
        X.basicOpen _
    rw [etaleChartReplace_coords_ne c j h hne haj]
    exact hi

/-- The saturation, with a given set of tangent coordinates to start from. -/
theorem exists_tangent_saturated_chart_of_card {r : ℕ} (ξ : Fin r → X)
    (σ : Fin r → Option (Fin n)) (η : X) (H : Set (X.presheaf.stalk η)) (m : ℕ) :
    ∀ (c : EtaleChart K X n) (hη : η ∈ c.U) (T : Finset (Fin n)), n ≤ T.card + m →
      IsSNCChart c ξ σ →
      (∀ b ∈ T, (∀ k, σ k ≠ some b) ∧ etaleChartStalkCoords c η hη (MvPolynomial.X b) ∈ H) →
      ∃ (c' : EtaleChart K X n) (hη' : η ∈ c'.U) (T' : Finset (Fin n)), c'.U ≤ c.U ∧ T ⊆ T' ∧
        IsSNCChart c' ξ σ ∧
        (∀ b ∈ T', (∀ k, σ k ≠ some b) ∧
          etaleChartStalkCoords c' η hη' (MvPolynomial.X b) ∈ H) ∧
        (∀ a, a ∉ T' → etaleChartStalkCoords c' η hη' (MvPolynomial.X a) =
          etaleChartStalkCoords c η hη (MvPolynomial.X a)) ∧
        ∀ h ∈ H, ∀ b, (∀ k, σ k ≠ some b) → b ∉ T' →
          etaleCoordinateDerivation (etaleChartStalkCoords c' η hη')
            (etaleChartStalkCoords_formallyEtale c' η hη') b h ∈
              IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  induction m with
  | zero =>
    intro c hη T hm hc hT
    refine ⟨c, hη, T, le_rfl, Finset.Subset.refl T, hc, hT, fun _ _ => rfl, ?_⟩
    intro h _ b _ hbT
    exfalso
    have h1 : T.card < Fintype.card (Fin n) := Finset.card_lt_univ_of_notMem hbT
    rw [Fintype.card_fin] at h1
    omega
  | succ m ih =>
    intro c hη T hm hc hT
    by_cases hex : ∃ h ∈ H, ∃ b, (∀ k, σ k ≠ some b) ∧ b ∉ T ∧
        etaleCoordinateDerivation (etaleChartStalkCoords c η hη)
          (etaleChartStalkCoords_formallyEtale c η hη) b h ∉
            IsLocalRing.maximalIdeal (X.presheaf.stalk η)
    · obtain ⟨h, hh, b, hb, hbT, hder⟩ := hex
      -- a section representing h on a smaller chart
      obtain ⟨V, hηV, s, hs⟩ := X.presheaf.exists_germ_eq h
      obtain ⟨g, hgV, hηg⟩ := c.isAffine.exists_basicOpen_le (V := V) ⟨η, hηV⟩ hη
      have hc₁ : IsSNCChart (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) ξ σ :=
        isSNCChart_basicOpen hc g _
      have hcoords₁ : etaleChartStalkCoords (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) η hηg =
          etaleChartStalkCoords c η hη := etaleChartStalkCoords_basicOpen c g _ η hηg
      obtain ⟨h₁, hh₁⟩ : ∃ h₁ : Γ(X, (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).U),
          X.presheaf.germ (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).U η hηg h₁ = h :=
        ⟨X.presheaf.map (homOfLE hgV).op s,
          (TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _).trans hs⟩
      -- the derivative of the section is a unit at η
      have hηd : η ∈ X.basicOpen (etaleCoordinateDerivation
          (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).coords
          (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).formallyEtale b h₁) := by
        refine (X.mem_basicOpen _ η hηg).mpr ?_
        have key := etaleChart_germ_coordinateDerivation (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) η
          hηg b h₁
        rw [hh₁, etaleCoordinateDerivation_congr hcoords₁ _
          (etaleChartStalkCoords_formallyEtale c η hη) b] at key
        have hu : IsUnit (X.presheaf.germ (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).U η hηg
            (etaleCoordinateDerivation (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).coords
              (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩).formallyEtale b h₁)) := by
          rw [key]
          exact IsLocalRing.notMem_maximalIdeal.mp hder
        exact hu
      have hc₂ : IsSNCChart (etaleChartReplace (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) b h₁
          ⟨⟨η, hηd⟩⟩) ξ σ := isSNCChart_etaleChartReplace hc₁ b hb h₁ _
      have hcard : n ≤ (insert b T).card + m := by
        rw [Finset.card_insert_of_notMem hbT]
        omega
      obtain ⟨c', hη', T', hle, hTT', hc', hT', hsame, hsat⟩ := ih
        (etaleChartReplace (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) b h₁ ⟨⟨η, hηd⟩⟩) hηd
        (insert b T) hcard hc₂ (by
          intro b' hb'
          rcases Finset.mem_insert.mp hb' with rfl | hb'T
          · refine ⟨hb, ?_⟩
            rw [etaleChartStalkCoords_replace_self (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) b' h₁ _ η
              hηd, hh₁]
            exact hh
          · refine ⟨(hT b' hb'T).1, ?_⟩
            have hne : b' ≠ b := fun e => hbT (e ▸ hb'T)
            rw [etaleChartStalkCoords_replace_ne (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) b h₁ _ η
              hηd hne, hcoords₁]
            exact (hT b' hb'T).2)
      refine ⟨c', hη', T', hle.trans ((X.basicOpen_le _).trans (X.basicOpen_le g)),
        (Finset.subset_insert b T).trans hTT', hc', hT', ?_, hsat⟩
      intro a ha
      have haT : a ∉ insert b T := fun h' => ha (hTT' h')
      have hab : a ≠ b := fun e => haT (e ▸ Finset.mem_insert_self b T)
      rw [hsame a ha, etaleChartStalkCoords_replace_ne (etaleChartBasicOpen c g ⟨⟨η, hηg⟩⟩) b h₁
        _ η hηd hab, hcoords₁]
    · refine ⟨c, hη, T, le_rfl, Finset.Subset.refl T, hc, hT, fun _ _ => rfl, ?_⟩
      intro h hh b hb hbT
      by_contra hder
      exact hex ⟨h, hh, b, hb, hbT, hder⟩

/-- Tangent coordinates at a point of a simple normal crossing chart. For a set H of germs at η,
the chart can be changed near η, keeping the simple normal crossing position, so that the
coordinates of a set T, none of which belongs to the family, are germs of H, the other coordinates
are unchanged at η, and every derivative of a germ of H in a coordinate outside T that does not
belong to the family lies in the maximal ideal of η. -/
theorem exists_tangent_saturated_chart {r : ℕ} (ξ : Fin r → X) (σ : Fin r → Option (Fin n))
    (η : X) (H : Set (X.presheaf.stalk η)) (c : EtaleChart K X n) (hη : η ∈ c.U)
    (hc : IsSNCChart c ξ σ) :
    ∃ (c' : EtaleChart K X n) (hη' : η ∈ c'.U) (T : Finset (Fin n)), c'.U ≤ c.U ∧
      IsSNCChart c' ξ σ ∧
      (∀ b ∈ T, (∀ k, σ k ≠ some b) ∧
        etaleChartStalkCoords c' η hη' (MvPolynomial.X b) ∈ H) ∧
      (∀ a, a ∉ T → etaleChartStalkCoords c' η hη' (MvPolynomial.X a) =
        etaleChartStalkCoords c η hη (MvPolynomial.X a)) ∧
      ∀ h ∈ H, ∀ b, (∀ k, σ k ≠ some b) → b ∉ T →
        etaleCoordinateDerivation (etaleChartStalkCoords c' η hη')
          (etaleChartStalkCoords_formallyEtale c' η hη') b h ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
  obtain ⟨c', hη', T', hle, -, hc', hT', hsame, hsat⟩ :=
    exists_tangent_saturated_chart_of_card ξ σ η H n c hη ∅ (by simp) hc (by simp)
  exact ⟨c', hη', T', hle, hc', hT', hsame, hsat⟩

end Charts

end MixedFujita
