/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.FibreWittLifts

/-!
The lifts on the Čech intersections of the fibre (step 10, R4-6).

For a family of opens `U_i` of `X` and étale coordinates `y_i` on opens `W_i ⊇ U_i`, the lifts on a
Čech intersection `U_x = ⋂_a U_{x_a}` are `W₂(κ) ⊗_A Γ(X, U_x)` (check 548).

* `fibreCechπ`: the reduction onto the functions on the intersection `⋂_a g⁻¹U_{x_a}` of the
  preimages. It is surjective, its kernel is `p` times the lifts, `p` kills only the kernel for `X`
  flat over `A`, the Teichmüller lifts map to the constants, and it commutes with restriction
  (`fibreCechπ_map`: the hypothesis `hR` of check 491, and the comparison of two families).
* `fibreCechFrobenius`: the coordinate Frobenius lift of the vertex `j`, for the coordinates of `x_j`
  restricted to `U_x` (`fibreCechCoordinates`). It lifts the `p`-th power map, fixes the Teichmüller
  lifts and the coordinates up to `p`-th powers, and commutes with restriction
  (`fibreCechFrobenius_restrict`: the hypothesis `hRF` of check 491; `fibreCechFrobenius_mono`: the
  comparison of a family `U' ≤ U` with the same coordinates), by the uniqueness of check 520.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TensorProduct

namespace MixedFujita

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] structureSectionsAlgebra sectionsRingModule

universe u

section Coordinates

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] {n : ℕ}

/-- Restricting coordinates twice is restricting them once. -/
theorem restrictCoordinates_restrictCoordinates {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) :
    restrictCoordinates h' (restrictCoordinates h y) = restrictCoordinates (h'.trans h) y := by
  apply MvPolynomial.algHom_ext
  intro j
  change (X.presheaf.map (homOfLE h').op).hom
      ((X.presheaf.map (homOfLE h).op).hom (y (MvPolynomial.X j))) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom (y (MvPolynomial.X j))
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

omit [X.Over (Spec (CommRingCat.of A))] in
/-- The restriction along an equality of opens is bijective. -/
theorem presheaf_map_homOfLE_eq_bijective {P Q : X.Opens} (hPQ : P = Q) :
    Function.Bijective (X.presheaf.map (homOfLE hPQ.le).op).hom := by
  subst hPQ
  have h1 : X.presheaf.map (homOfLE (le_refl P)).op = 𝟙 _ := by
    rw [show homOfLE (le_refl P) = 𝟙 P from rfl, op_id, X.presheaf.map_id]
  rw [show homOfLE (Eq.le (rfl : P = P)) = homOfLE (le_refl P) from rfl, h1]
  exact ⟨fun a b hab => hab, fun b => ⟨b, rfl⟩⟩

end Coordinates

section Frobenius

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A : Type u} [CommRing A] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] {n : ℕ}

/-- The coordinate Frobenius depends only on the coordinates. -/
theorem fibreWittFrobenius_congr {V : X.Opens} {y y' : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)}
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale) (hyy : y = y')
    [Nontrivial (κ ⊗[A] Γ(X, V))] :
    fibreWittFrobenius p κ h y hy = fibreWittFrobenius p κ h y' hy' := by
  subst hyy
  rfl

/-- **Restriction commutes with the coordinate Frobenius lifts** of coordinates and of their
restriction. -/
theorem fibreWittFrobenius_restrict_of_eq {V V' : X.Opens} (hle : V' ≤ V)
    (y : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V)) (y' : MvPolynomial (Fin n) A →ₐ[A] Γ(X, V'))
    (hy : y.toRingHom.FormallyEtale) (hy' : y'.toRingHom.FormallyEtale)
    (hyy : restrictCoordinates hle y = y')
    [Nontrivial (κ ⊗[A] Γ(X, V))] [Nontrivial (κ ⊗[A] Γ(X, V'))] (z : WittTwo p κ ⊗[A] Γ(X, V)) :
    fibreWittRestrict p κ hle (fibreWittFrobenius p κ h y hy z) =
      fibreWittFrobenius p κ h y' hy' (fibreWittRestrict p κ hle z) := by
  subst hyy
  exact RingHom.congr_fun (fibreWittFrobenius_restrict p κ h hle y hy hy') z

end Frobenius

section Cech

variable (p : ℕ) [Fact p.Prime] (κ : Type u) [Field κ] [CharP κ p] [PerfectRing κ p]
  {A : Type u} [CommRing A] [Algebra A κ] [Algebra A (WittTwo p κ)]
  (h : ∀ a : A, wittTwoReduction p κ (algebraMap A (WittTwo p κ) a) = algebraMap A κ a)
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of A))] [Y.Over (Spec (CommRingCat.of κ))]
  {g : Y ⟶ X}
  (H : IsPullback g (Y ↘ Spec (CommRingCat.of κ)) (X ↘ Spec (CommRingCat.of A))
    (Spec.map (CommRingCat.ofHom (algebraMap A κ))))
  {ι : Type*}

section Reduction

/-- **The reduction of the lifts on a Čech intersection** onto the functions on the intersection of
the preimages. -/
noncomputable def fibreCechπ (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x)) :
    WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x) →+*
      Γ(Y, TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x) :=
  (Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom.comp
    (fibreWittπ p κ h H hU)

omit [PerfectRing κ p] in
theorem fibreCechπ_surjective (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x)) :
    Function.Surjective (fibreCechπ p κ h H U x hU) :=
  (presheaf_map_homOfLE_eq_bijective (CohomologyAux.cechOpen_preimage g U x)).2.comp
    (fibreWittπ_surjective p κ h H hU)

/-- **The kernel of the reduction is `p` times the lifts** (`hker`). -/
theorem fibreCechπ_exists_eq_p_mul (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))
    (hz : fibreCechπ p κ h H U x hU z = 0) :
    ∃ y, z = (p : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x)) * y := by
  apply fibreWittπ_exists_eq_p_mul p κ h H hU z
  apply (presheaf_map_homOfLE_eq_bijective (CohomologyAux.cechOpen_preimage g U x)).1
  rw [map_zero]
  exact hz

omit [PerfectRing κ p] in
/-- **`p` kills only elements of the kernel**, for `X` flat over `A` (`hann`). -/
theorem fibreCechπ_eq_zero_of_p_mul_eq_zero [Flat (X ↘ Spec (CommRingCat.of A))]
    (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι) (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))
    (hz : (p : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x)) * z = 0) :
    fibreCechπ p κ h H U x hU z = 0 := by
  change (Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom
    (fibreWittπ p κ h H hU z) = 0
  rw [fibreWittπ_eq_zero_of_p_mul_eq_zero p κ h H hU z hz, map_zero]

omit [PerfectRing κ p] in
/-- The Teichmüller lifts map to the constants. -/
theorem fibreCechπ_teichmuller (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x)) (k : κ) :
    fibreCechπ p κ h H U x hU
        (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, TopCat.Presheaf.cechOpen U x))) =
      algebraMap κ Γ(Y, TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x) k := by
  change (Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom
    (fibreWittπ p κ h H hU _) = _
  rw [fibreWittπ_teichmuller]
  exact AlgHom.commutes (structureRestrictAlgHom κ Y (CohomologyAux.cechOpen_preimage g U x).le) k

omit [PerfectRing κ p] in
/-- **The reduction commutes with restriction** (`hR` of check 491). -/
theorem fibreCechπ_map {ι' : Type*} (U : ι → X.Opens) (U' : ι' → X.Opens) {m m' : ℕ}
    (x : Fin m → ι) (x' : Fin m' → ι') (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (hU' : IsAffineOpen (TopCat.Presheaf.cechOpen U' x'))
    (hle : TopCat.Presheaf.cechOpen U' x' ≤ TopCat.Presheaf.cechOpen U x)
    (hle' : TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U' i) x' ≤
      TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x)
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x)) :
    fibreCechπ p κ h H U' x' hU' (fibreWittRestrict p κ hle z) =
      (Y.presheaf.map (homOfLE hle').op).hom (fibreCechπ p κ h H U x hU z) := by
  change (Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U' x').le).op).hom
      (fibreWittπ p κ h H hU' (fibreWittRestrict p κ hle z)) =
    (Y.presheaf.map (homOfLE hle').op).hom
      ((Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom
        (fibreWittπ p κ h H hU z))
  rw [fibreWittπ_restrict p κ h H hU hU' hle z, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  rfl

include H in
/-- The fibre functions on a nonempty intersection of preimages are nonzero. -/
theorem nontrivial_fibreCech (U : ι → X.Opens) {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (hne : Nonempty (TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x)) :
    Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x)) := by
  rw [CohomologyAux.cechOpen_preimage g U x] at hne
  exact nontrivial_fibreWitt_tensor κ H hU hne

end Reduction

section CechFrobenius

variable {n : ℕ} (W : ι → X.Opens) (y : ∀ i, MvPolynomial (Fin n) A →ₐ[A] Γ(X, W i))

/-- The coordinates of the vertex `x_j` restricted to the Čech intersection. -/
noncomputable def fibreCechCoordinates (U : ι → X.Opens) (hUW : ∀ i, U i ≤ W i) {m : ℕ}
    (x : Fin m → ι) (j : Fin m) :
    MvPolynomial (Fin n) A →ₐ[A] Γ(X, TopCat.Presheaf.cechOpen U x) :=
  restrictCoordinates ((TopCat.Presheaf.cechOpen_le U x j).trans (hUW (x j))) (y (x j))

theorem fibreCechCoordinates_X (U : ι → X.Opens) (hUW : ∀ i, U i ≤ W i) {m : ℕ}
    (x : Fin m → ι) (j : Fin m) (t : Fin n) :
    fibreCechCoordinates W y U hUW x j (MvPolynomial.X t) =
      (X.presheaf.map (homOfLE ((TopCat.Presheaf.cechOpen_le U x j).trans (hUW (x j)))).op).hom
        (y (x j) (MvPolynomial.X t)) :=
  rfl

theorem fibreCechCoordinates_formallyEtale (hW : ∀ i, IsAffineOpen (W i))
    (hy : ∀ i, (y i).toRingHom.FormallyEtale) (U : ι → X.Opens) (hUW : ∀ i, U i ≤ W i) {m : ℕ}
    (x : Fin m → ι) (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x)) (j : Fin m) :
    (fibreCechCoordinates W y U hUW x j).toRingHom.FormallyEtale :=
  restrictCoordinates_formallyEtale (hW (x j)) hU _ (y (x j)) (hy (x j))

/-- Restricting the coordinates of a vertex to a smaller intersection with the same vertex. -/
theorem restrictCoordinates_fibreCechCoordinates {ι' : Type*} (W' : ι' → X.Opens)
    (y' : ∀ i, MvPolynomial (Fin n) A →ₐ[A] Γ(X, W' i)) (U : ι → X.Opens) (U' : ι' → X.Opens)
    (hUW : ∀ i, U i ≤ W i) (hUW' : ∀ i, U' i ≤ W' i) {m m' : ℕ} (x : Fin m → ι)
    (x' : Fin m' → ι') (j : Fin m) (j' : Fin m')
    (hle : TopCat.Presheaf.cechOpen U' x' ≤ TopCat.Presheaf.cechOpen U x)
    (hvert : ∀ hle' : TopCat.Presheaf.cechOpen U' x' ≤ W (x j),
      restrictCoordinates hle' (y (x j)) = fibreCechCoordinates W' y' U' hUW' x' j') :
    restrictCoordinates hle (fibreCechCoordinates W y U hUW x j) =
      fibreCechCoordinates W' y' U' hUW' x' j' := by
  rw [fibreCechCoordinates, restrictCoordinates_restrictCoordinates]
  exact hvert _

/-- **The coordinate Frobenius lift of the vertex `j`** on the lifts of a Čech intersection. -/
noncomputable def fibreCechFrobenius (hW : ∀ i, IsAffineOpen (W i))
    (hy : ∀ i, (y i).toRingHom.FormallyEtale) (U : ι → X.Opens) (hUW : ∀ i, U i ≤ W i) {m : ℕ}
    (x : Fin m → ι) (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))] (j : Fin m) :
    WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x) →+*
      WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x) :=
  fibreWittFrobenius p κ h (fibreCechCoordinates W y U hUW x j)
    (fibreCechCoordinates_formallyEtale W y hW hy U hUW x hU j)

variable (hW : ∀ i, IsAffineOpen (W i)) (hy : ∀ i, (y i).toRingHom.FormallyEtale)
  (U : ι → X.Opens) (hUW : ∀ i, U i ≤ W i)

/-- The coordinate Frobenius lifts the `p`-th power map (`hF`). -/
theorem fibreCechπ_frobenius {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))] (j : Fin m)
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x)) :
    fibreCechπ p κ h H U x hU (fibreCechFrobenius p κ h W y hW hy U hUW x hU j z) =
      fibreCechπ p κ h H U x hU z ^ p := by
  change (Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom
      (fibreWittπ p κ h H hU (fibreWittFrobenius p κ h _ _ z)) =
    ((Y.presheaf.map (homOfLE (CohomologyAux.cechOpen_preimage g U x).le).op).hom
      (fibreWittπ p κ h H hU z)) ^ p
  rw [fibreWittπ_frobenius, map_pow]

/-- The Teichmüller lifts are fixed up to `p`-th powers (`hK`). -/
theorem fibreCechFrobenius_teichmuller {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))] (j : Fin m) (k : κ) :
    fibreCechFrobenius p κ h W y hW hy U hUW x hU j
        (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, TopCat.Presheaf.cechOpen U x))) =
      (wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, TopCat.Presheaf.cechOpen U x))) ^ p :=
  fibreWittFrobenius_teichmuller p κ h _ _ k

/-- The coordinates of the vertex are fixed up to `p`-th powers. -/
theorem fibreCechFrobenius_coordinate {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))] (j : Fin m) (t : Fin n) :
    fibreCechFrobenius p κ h W y hW hy U hUW x hU j
        ((1 : WittTwo p κ) ⊗ₜ[A] fibreCechCoordinates W y U hUW x j (MvPolynomial.X t)) =
      ((1 : WittTwo p κ) ⊗ₜ[A] fibreCechCoordinates W y U hUW x j (MvPolynomial.X t)) ^ p :=
  fibreWittFrobenius_coordinate p κ h _ _ t

/-- **The constants have lifts fixed by all the vertex Frobenius lifts** (`hK` of check 491). -/
theorem exists_fibreCech_teichmuller {m : ℕ} (x : Fin m → ι)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))] (k : κ) :
    ∃ k' : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x),
      fibreCechπ p κ h H U x hU k' =
        algebraMap κ Γ(Y, TopCat.Presheaf.cechOpen (fun i => g ⁻¹ᵁ U i) x) k ∧
      ∀ j, fibreCechFrobenius p κ h W y hW hy U hUW x hU j k' = k' ^ p :=
  ⟨wittTwoTeichmuller p κ k ⊗ₜ[A] (1 : Γ(X, TopCat.Presheaf.cechOpen U x)),
    fibreCechπ_teichmuller p κ h H U x hU k,
    fun j => fibreCechFrobenius_teichmuller p κ h W y hW hy U hUW x hU j k⟩

/-- **The vertex Frobenius lifts commute with restriction** (`hRF` of check 491). -/
theorem fibreCechFrobenius_restrict {m m' : ℕ} (x : Fin m → ι) (f : Fin m' → Fin m)
    (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (hU' : IsAffineOpen (TopCat.Presheaf.cechOpen U (x ∘ f)))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))]
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U (x ∘ f)))] (j : Fin m')
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U (x ∘ f))) :
    fibreWittRestrict p κ (TopCat.Presheaf.cechOpen_le_comp U x f)
        (fibreCechFrobenius p κ h W y hW hy U hUW (x ∘ f) hU' j z) =
      fibreCechFrobenius p κ h W y hW hy U hUW x hU (f j)
        (fibreWittRestrict p κ (TopCat.Presheaf.cechOpen_le_comp U x f) z) :=
  fibreWittFrobenius_restrict_of_eq p κ h _ _ _ _ _
    (restrictCoordinates_fibreCechCoordinates W y W y U U hUW hUW (x ∘ f) x j (f j) _
      fun _ => rfl) z

/-- **The vertex Frobenius lifts of a smaller family with the same coordinates are the
restrictions.** -/
theorem fibreCechFrobenius_mono (U' : ι → X.Opens) (hU'U : ∀ i, U' i ≤ U i) {m : ℕ}
    (x : Fin m → ι) (hU : IsAffineOpen (TopCat.Presheaf.cechOpen U x))
    (hU' : IsAffineOpen (TopCat.Presheaf.cechOpen U' x))
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x))]
    [Nontrivial (κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U' x))]
    (hle : TopCat.Presheaf.cechOpen U' x ≤ TopCat.Presheaf.cechOpen U x) (j : Fin m)
    (z : WittTwo p κ ⊗[A] Γ(X, TopCat.Presheaf.cechOpen U x)) :
    fibreWittRestrict p κ hle (fibreCechFrobenius p κ h W y hW hy U hUW x hU j z) =
      fibreCechFrobenius p κ h W y hW hy U' (fun i => (hU'U i).trans (hUW i)) x hU' j
        (fibreWittRestrict p κ hle z) :=
  fibreWittFrobenius_restrict_of_eq p κ h _ _ _ _ _
    (restrictCoordinates_fibreCechCoordinates W y W y U U' hUW _ x x j j hle
      fun _ => rfl) z

end CechFrobenius

end Cech

end MixedFujita
