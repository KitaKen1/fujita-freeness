/-
Copyright (c) 2026 Kenta Kitamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenta Kitamura
-/
module

public import MixedFujita.DeligneIllusieReindex
public import MixedFujita.FrobeniusLiftNaturality
public import MixedFujita.DeRhamExteriorDegree

/-!
The Deligne–Illusie map of a chart commutes with restriction (step 10).

Let `S → T` be a map of `K`-algebras with étale coordinates on both (for instance the
restriction from a Čech intersection to a smaller one), and `ρ : L → L'` a map of lifts modulo
`p²` compatible with `π`, `π'` and with families of Frobenius lifts, `ρ ∘ F_j = F'_j ∘ ρ`.
* The maps `Φ_F` and `h_{F₁F₂}` on `1`-forms commute with `Ω[S⁄K] → Ω[T⁄K]`
  (`frobeniusLiftOneFormAux_map`, `frobeniusLiftHomotopyAux_map`): both sides are additive and
  Frobenius-semilinear along `S → T`, and they agree on exact forms by check 412; such maps are
  determined by their values on exact forms (`eq_of_frobeniusSemilinear_D_ringHom`, the version of
  check 457 along a ring map).
* The induced map of exterior algebras commutes with the grade involutions
  (`kaehlerExteriorMap_involute`), hence with the products of total index cochains
  (`map_seqTotalMul`, `map_seqTotalProd`).
* So the degree-`1` Deligne–Illusie cocycle, its products and the Deligne–Illusie map on
  `b`-forms commute with restriction (`diSeqCocycle_map`, `diSeqProd_map`, `diSeqAlt_map`).
-/

@[expose] public section

namespace MixedFujita

universe u v v' w w'

section Uniqueness

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S]

/-- **An additive map on `Ω[S⁄K]` that is Frobenius-semilinear along a ring map `φ : S → R` is
determined by its values on exact forms.** -/
theorem eq_of_frobeniusSemilinear_D_ringHom (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]
    (φ : S →+* R) {M : Type*} [AddCommGroup M] [Module R M] (f g : Ω[S⁄K] → M)
    (hf : ∀ ω η, f (ω + η) = f ω + f η) (hg : ∀ ω η, g (ω + η) = g ω + g η)
    (hfs : ∀ (c : S) ω, f (c • ω) = φ c ^ p • f ω) (hgs : ∀ (c : S) ω, g (c • ω) = φ c ^ p • g ω)
    (hD : ∀ a, f (KaehlerDifferential.D K S a) = g (KaehlerDifferential.D K S a))
    (ω : Ω[S⁄K]) : f ω = g ω := by
  have hω : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D K S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    exact hD a
  | zero =>
    have h1 : f 0 = 0 := by simpa [zero_pow hp.out.ne_zero] using hfs 0 0
    have h2 : g 0 = 0 := by simpa [zero_pow hp.out.ne_zero] using hgs 0 0
    rw [h1, h2]
  | add x z _ _ hx hz => rw [hf, hg, hx, hz]
  | smul c x _ hx => rw [hfs, hgs, hx]

end Uniqueness

section Products

variable {J : Type*} {A : Type*} [Ring A] {B : Type*} [Ring B] (σ : A →+* A) (σ' : B →+* B)
  (ψ : A →+* B) (hψ : ∀ x, ψ (σ x) = σ' (ψ x))

/-- Applying a ring map to the values of a total index cochain. -/
def seqTotalMap (α : ℕ → (ℕ → J) → A) : ℕ → (ℕ → J) → B := fun c t => ψ (α c t)

/-- `seqTotalMap` as an additive map. -/
def seqTotalMapHom : (ℕ → (ℕ → J) → A) →+ (ℕ → (ℕ → J) → B) where
  toFun := seqTotalMap ψ
  map_zero' := funext fun _ => funext fun _ => map_zero ψ
  map_add' _ _ := funext fun _ => funext fun _ => map_add ψ _ _

theorem seqTotalMapHom_apply (α : ℕ → (ℕ → J) → A) :
    seqTotalMapHom (J := J) ψ α = seqTotalMap ψ α := rfl

include hψ in
theorem ringHom_pow_map (k : ℕ) (x : A) : ψ ((σ ^ k) x) = (σ' ^ k) (ψ x) := by
  rw [RingHom.coe_pow, RingHom.coe_pow]
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hψ]

include hψ in
/-- **Ring maps commuting with the involutions commute with the product of total cochains.** -/
theorem map_seqTotalMul (α β : ℕ → (ℕ → J) → A) :
    seqTotalMap ψ (seqTotalMul σ α β) = seqTotalMul σ' (seqTotalMap ψ α) (seqTotalMap ψ β) := by
  funext c t
  simp only [seqTotalMap, seqTotalMul, map_sum, map_mul, ringHom_pow_map σ σ' ψ hψ]

theorem map_seqTotalOne : seqTotalMap ψ (seqTotalOne (J := J) (A := A)) = seqTotalOne := by
  funext c t
  cases c with
  | zero => exact map_one ψ
  | succ c => exact map_zero ψ

include hψ in
theorem map_seqTotalProd (l : List (ℕ → (ℕ → J) → A)) :
    seqTotalMap ψ (seqTotalProd σ l) = seqTotalProd σ' (l.map (seqTotalMap ψ)) := by
  induction l with
  | nil => exact map_seqTotalOne ψ
  | cons α l ih =>
    rw [seqTotalProd_cons, map_seqTotalMul σ σ' ψ hψ, ih, List.map_cons, seqTotalProd_cons]

end Products

section Naturality

variable {K : Type u} [Field K] {S : Type v} [CommRing S] [Algebra K S] {T : Type v'} [CommRing T]
  [Algebra K T] [Algebra S T] [IsScalarTower K S T]

/-- **The map of exterior algebras commutes with the grade involutions.** -/
theorem kaehlerExteriorMap_involute (x : ExteriorAlgebra S Ω[S⁄K]) :
    kaehlerExteriorMap K S T (exteriorInvolute K S x) =
      exteriorInvolute K T (kaehlerExteriorMap K S T x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [exteriorInvolute_apply, AlgHom.commutes, AlgHom.commutes,
      IsScalarTower.algebraMap_apply S T (ExteriorAlgebra T Ω[T⁄K]), exteriorInvolute_apply,
      AlgHom.commutes]
  | ι v =>
    rw [exteriorInvolute_ι, map_neg, kaehlerExteriorMap_ι, exteriorInvolute_ι]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

theorem kaehlerExteriorMap_ιMulti (b : ℕ) (ω : Fin b → Ω[S⁄K]) :
    kaehlerExteriorMap K S T (ExteriorAlgebra.ιMulti S b ω) =
      ExteriorAlgebra.ιMulti T b fun i => KaehlerDifferential.map K K S T (ω i) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  exact kaehlerExteriorMap_ι (ω i)

/-- The restriction of an element of `⋀^b`, as an element of `⋀^b`. -/
noncomputable def kaehlerExteriorPowerMap (b : ℕ) (x : ⋀[S]^b Ω[S⁄K]) : ⋀[T]^b Ω[T⁄K] :=
  ⟨kaehlerExteriorMap K S T x, kaehlerExteriorMap_mem_exteriorPower x.2⟩

theorem kaehlerExteriorPowerMap_zero (b : ℕ) :
    kaehlerExteriorPowerMap (K := K) (T := T) b (0 : ⋀[S]^b Ω[S⁄K]) = 0 :=
  Subtype.ext (by simp only [kaehlerExteriorPowerMap, Submodule.coe_zero, map_zero])

theorem kaehlerExteriorPowerMap_add (b : ℕ) (x x' : ⋀[S]^b Ω[S⁄K]) :
    kaehlerExteriorPowerMap (T := T) b (x + x') =
      kaehlerExteriorPowerMap b x + kaehlerExteriorPowerMap b x' :=
  Subtype.ext (by simp only [kaehlerExteriorPowerMap, Submodule.coe_add, map_add])

theorem kaehlerExteriorPowerMap_smul (b : ℕ) (f : S) (x : ⋀[S]^b Ω[S⁄K]) :
    kaehlerExteriorPowerMap (T := T) b (f • x) = algebraMap S T f • kaehlerExteriorPowerMap b x :=
  Subtype.ext (by simp only [kaehlerExteriorPowerMap, Submodule.coe_smul, kaehlerExteriorMap_smul])

theorem kaehlerExteriorPowerMap_ιMulti (b : ℕ) (ω : Fin b → Ω[S⁄K]) :
    kaehlerExteriorPowerMap (T := T) b (exteriorPower.ιMulti S b ω) =
      exteriorPower.ιMulti T b fun i => KaehlerDifferential.map K K S T (ω i) :=
  Subtype.ext (kaehlerExteriorMap_ιMulti b ω)

variable {n m : ℕ} (y : MvPolynomial (Fin n) K →ₐ[K] S) (hy : y.toRingHom.FormallyEtale)
  (z : MvPolynomial (Fin m) K →ₐ[K] T) (hz : z.toRingHom.FormallyEtale)
  {L : Type w} [CommRing L] (π : L →+* S) (hπ : Function.Surjective π) (p : ℕ) [hp : Fact p.Prime]
  [CharP K p] (hker : ∀ x, π x = 0 → ∃ z, x = (p : L) * z) (hann : ∀ z, (p : L) * z = 0 → π z = 0)
  (hp2 : (p : L) * p = 0)
  {L' : Type w'} [CommRing L'] (π' : L' →+* T) (hπ' : Function.Surjective π')
  (hker' : ∀ x, π' x = 0 → ∃ z, x = (p : L') * z) (hann' : ∀ z, (p : L') * z = 0 → π' z = 0)
  (hp2' : (p : L') * p = 0)
  (ρ' : L →+* L') (hρ : ∀ x, π' (ρ' x) = algebraMap S T (π x))

include hann hp2 hann' hp2' hρ in
/-- **`Φ_F` on `1`-forms commutes with restriction.** -/
theorem frobeniusLiftOneFormAux_map [Algebra.FiniteType K S] [Algebra.FiniteType K T]
    (F : L →+* L) (hF : ∀ x, π (F x) = π x ^ p) (F' : L' →+* L') (hF' : ∀ x, π' (F' x) = π' x ^ p)
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F c' = c' ^ p)
    (hK' : ∀ c : K, ∃ c' : L', π' c' = algebraMap K T c ∧ F' c' = c' ^ p)
    (hρF : ∀ x, ρ' (F x) = F' (ρ' x)) (ω : Ω[S⁄K]) :
    frobeniusLiftOneFormAux z hz π' hπ' p F' hF' hker' (KaehlerDifferential.map K K S T ω) =
      KaehlerDifferential.map K K S T (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω) :=
  eq_of_frobeniusSemilinear_D_ringHom p (algebraMap S T)
    (fun ω => frobeniusLiftOneFormAux z hz π' hπ' p F' hF' hker' (KaehlerDifferential.map K K S T ω))
    (fun ω => KaehlerDifferential.map K K S T (frobeniusLiftOneFormAux y hy π hπ p F hF hker ω))
    (fun ω η => by rw [map_add, frobeniusLiftOneFormAux_add])
    (fun ω η => by rw [frobeniusLiftOneFormAux_add, map_add])
    (fun c ω => by
      rw [LinearMap.map_smul, ← algebraMap_smul T c, frobeniusLiftOneFormAux_smul])
    (fun c ω => by
      rw [frobeniusLiftOneFormAux_smul, LinearMap.map_smul, ← map_pow, algebraMap_smul])
    (fun a => by
      rw [KaehlerDifferential.map_D,
        frobeniusLiftOneFormAux_D z hz π' hπ' p F' hF' hker' hann' hp2' hK',
        frobeniusLiftOneFormAux_D y hy π hπ p F hF hker hann hp2 hK,
        frobeniusLiftOneForm_map π hπ p F hF hker hann hp2 π' hπ' F' hF' hker' hann' hp2' ρ' hρ
          hρF])
    ω

omit hp2 hp2' in
include hann hann' hρ in
/-- **The homotopy `h_{F₁F₂}` on `1`-forms commutes with restriction.** -/
theorem frobeniusLiftHomotopyAux_map [Algebra.FiniteType K S] [Algebra.FiniteType K T]
    (F₁ F₂ : L →+* L) (hF₁ : ∀ x, π (F₁ x) = π x ^ p) (hF₂ : ∀ x, π (F₂ x) = π x ^ p)
    (F₁' F₂' : L' →+* L') (hF₁' : ∀ x, π' (F₁' x) = π' x ^ p) (hF₂' : ∀ x, π' (F₂' x) = π' x ^ p)
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ F₁ c' = c' ^ p ∧ F₂ c' = c' ^ p)
    (hK' : ∀ c : K, ∃ c' : L', π' c' = algebraMap K T c ∧ F₁' c' = c' ^ p ∧ F₂' c' = c' ^ p)
    (hρF₁ : ∀ x, ρ' (F₁ x) = F₁' (ρ' x)) (hρF₂ : ∀ x, ρ' (F₂ x) = F₂' (ρ' x)) (ω : Ω[S⁄K]) :
    frobeniusLiftHomotopyAux z hz π' hπ' p F₁' F₂' hF₁' hF₂' hker'
        (KaehlerDifferential.map K K S T ω) =
      algebraMap S T (frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω) :=
  eq_of_frobeniusSemilinear_D_ringHom p (algebraMap S T) (M := T)
    (fun ω => frobeniusLiftHomotopyAux z hz π' hπ' p F₁' F₂' hF₁' hF₂' hker'
      (KaehlerDifferential.map K K S T ω))
    (fun ω => algebraMap S T (frobeniusLiftHomotopyAux y hy π hπ p F₁ F₂ hF₁ hF₂ hker ω))
    (fun ω η => by rw [map_add, frobeniusLiftHomotopyAux_add])
    (fun ω η => by rw [frobeniusLiftHomotopyAux_add, map_add])
    (fun c ω => by
      rw [LinearMap.map_smul, ← algebraMap_smul T c, frobeniusLiftHomotopyAux_smul, smul_eq_mul])
    (fun c ω => by rw [frobeniusLiftHomotopyAux_smul, map_mul, map_pow, smul_eq_mul])
    (fun a => by
      rw [KaehlerDifferential.map_D,
        frobeniusLiftHomotopyAux_D z hz π' hπ' p F₁' F₂' hF₁' hF₂' hker' hann' hK',
        frobeniusLiftHomotopyAux_D y hy π hπ p F₁ F₂ hF₁ hF₂ hker hann hK,
        frobeniusLiftHomotopy_map π hπ p F₁ F₂ hF₁ hF₂ hker hann π' hπ' F₁' F₂' hF₁' hF₂' hker' hann'
          ρ' hρ hρF₁ hρF₂])
    ω

variable {J : Type*} (F : J → (L →+* L)) (hF : ∀ j x, π (F j x) = π x ^ p)
  (F' : J → (L' →+* L')) (hF' : ∀ j x, π' (F' j x) = π' x ^ p)
  (hρF : ∀ j x, ρ' (F j x) = F' j (ρ' x))

include hann hp2 hann' hp2' hρ hρF in
/-- **The degree-`1` Deligne–Illusie cocycle commutes with restriction.** -/
theorem diSeqCocycle_map [Algebra.FiniteType K S] [Algebra.FiniteType K T]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p)
    (hK' : ∀ c : K, ∃ c' : L', π' c' = algebraMap K T c ∧ ∀ j, F' j c' = c' ^ p) (ω : Ω[S⁄K]) :
    seqTotalMap (kaehlerExteriorMap K S T).toRingHom (diSeqCocycle y hy π hπ p F hF hker ω) =
      diSeqCocycle z hz π' hπ' p F' hF' hker' (KaehlerDifferential.map K K S T ω) := by
  funext c s
  rcases c with _ | _ | c
  · simp only [seqTotalMap, diSeqCocycle, diCocycleP, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      kaehlerExteriorMap_ι]
    rw [frobeniusLiftOneFormAux_map y hy z hz π hπ p hker hann hp2 π' hπ' hker' hann' hp2' ρ' hρ
      (F (s 0)) (hF (s 0)) (F' (s 0)) (hF' (s 0))
      (fun c => (hK c).imp fun c' h => ⟨h.1, h.2 (s 0)⟩)
      (fun c => (hK' c).imp fun c' h => ⟨h.1, h.2 (s 0)⟩) (hρF (s 0))]
  · simp only [seqTotalMap, diSeqCocycle, diCocycleH, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, Fin.val_zero, Fin.val_one]
    rw [IsScalarTower.algebraMap_apply S T (ExteriorAlgebra T Ω[T⁄K]),
      frobeniusLiftHomotopyAux_map y hy z hz π hπ p hker hann π' hπ' hker' hann' ρ' hρ
      (F (s 0)) (F (s 1)) (hF (s 0)) (hF (s 1)) (F' (s 0)) (F' (s 1)) (hF' (s 0)) (hF' (s 1))
      (fun c => (hK c).imp fun c' h => ⟨h.1, h.2 (s 0), h.2 (s 1)⟩)
      (fun c => (hK' c).imp fun c' h => ⟨h.1, h.2 (s 0), h.2 (s 1)⟩) (hρF (s 0)) (hρF (s 1))]
  · exact map_zero _

include hann hp2 hann' hp2' hρ hρF in
/-- **The products of the Deligne–Illusie cocycles commute with restriction.** -/
theorem diSeqProd_map [Algebra.FiniteType K S] [Algebra.FiniteType K T]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p)
    (hK' : ∀ c : K, ∃ c' : L', π' c' = algebraMap K T c ∧ ∀ j, F' j c' = c' ^ p)
    (ωs : List Ω[S⁄K]) :
    seqTotalMap (kaehlerExteriorMap K S T).toRingHom (diSeqProd y hy π hπ p F hF hker ωs) =
      diSeqProd z hz π' hπ' p F' hF' hker' (ωs.map (KaehlerDifferential.map K K S T)) := by
  rw [diSeqProd, diSeqProd, map_seqTotalProd (exteriorInvolute K S) (exteriorInvolute K T)
    (kaehlerExteriorMap K S T).toRingHom (kaehlerExteriorMap_involute (K := K) (S := S) (T := T)),
    List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun ω _ => ?_
  exact diSeqCocycle_map y hy z hz π hπ p hker hann hp2 π' hπ' hker' hann' hp2' ρ' hρ F hF F' hF'
    hρF hK hK' ω

include hann hp2 hann' hp2' hρ hρF in
/-- **The Deligne–Illusie map on `b`-forms commutes with restriction.** -/
theorem diSeqAlt_map [Algebra.FiniteType K S] [Algebra.FiniteType K T]
    (hK : ∀ c : K, ∃ c' : L, π c' = algebraMap K S c ∧ ∀ j, F j c' = c' ^ p)
    (hK' : ∀ c : K, ∃ c' : L', π' c' = algebraMap K T c ∧ ∀ j, F' j c' = c' ^ p) (b : ℕ)
    (x : ⋀[S]^b Ω[S⁄K]) :
    seqTotalMap (kaehlerExteriorMap K S T).toRingHom
        (twistedPiHom K S p J (diSeqAlt y hy π hπ p F hF hker b x)) =
      twistedPiHom K T p J (diSeqAlt z hz π' hπ' p F' hF' hker' b (kaehlerExteriorPowerMap b x)) := by
  induction span_ιMulti_mem b x using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ω, rfl⟩ := hx
    rw [kaehlerExteriorPowerMap_ιMulti, diSeqAlt_ιMulti, diSeqAlt_ιMulti, ← seqTotalMapHom_apply]
    simp only [map_sum, Units.smul_def, map_zsmul, seqTotalMapHom_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    have h := diSeqProd_map y hy z hz π hπ p hker hann hp2 π' hπ' hker' hann' hp2' ρ' hρ F hF F'
      hF' hρF hK hK' (List.ofFn fun i => ω (σ i))
    rw [List.map_ofFn] at h
    exact h
  | zero =>
    rw [← seqTotalMapHom_apply]
    simp only [map_zero, kaehlerExteriorPowerMap_zero]
  | add x x' _ _ hx hx' =>
    rw [← seqTotalMapHom_apply]
    simp only [map_add, kaehlerExteriorPowerMap_add, seqTotalMapHom_apply, hx, hx']
  | smul f x _ hx =>
    rw [map_smul, twistedPiHom_smul, kaehlerExteriorPowerMap_smul, map_smul, twistedPiHom_smul, ← hx]
    funext a t
    simp only [seqTotalMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, kaehlerExteriorMap_smul,
      map_pow]

end Naturality

end MixedFujita
