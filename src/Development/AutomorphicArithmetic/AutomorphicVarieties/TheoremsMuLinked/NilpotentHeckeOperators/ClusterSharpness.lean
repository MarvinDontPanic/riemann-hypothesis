module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NilpotentHeckeOperators.FNil

/-!
# Exact universal nilpotence order for a cluster of equal residues

The upper bound comes from counting differences in the deviation ideal. For the converse
use independent nilpotent coordinates over ℚ. Their balanced monomial survives exactly
below the claimed threshold; translating the coordinates by one makes the shifted factors
units at `q = 2`.
-/

@[expose] public section

namespace UpperTheory.V.Th

noncomputable section

open Finset

universe u

/-- Product over the upper triangle, i.e. one orientation of each unordered pair. -/
private def upper {m : ℕ} {A : Type*} [CommMonoid A] (f : Fin m → Fin m → A) : A :=
  ∏ i, ∏ j, if i < j then f i j else 1

private lemma upper_mul {m : ℕ} {A : Type*} [CommMonoid A] (f g : Fin m → Fin m → A) :
    upper (fun i j => f i j * g i j) = upper f * upper g := by
  simp only [upper, ← Finset.prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h]

private lemma ordered_eq_upper {m : ℕ} {A : Type*} [CommMonoid A] (f : Fin m → Fin m → A) :
    (∏ i, ∏ j ∈ univ.erase i, f i j) = upper f * upper (fun i j => f j i) := by
  let t (i j : Fin m) := (if i < j then f i j else 1) * (if j < i then f i j else 1)
  calc
    _ = ∏ i, ∏ j, t i j := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_erase_mul _ (t i) (mem_univ i)]
      simp only [t, lt_irrefl, ite_false, mul_one]
      apply Finset.prod_congr rfl
      intro j hj
      rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h <;> simp [h, h.asymm]
    _ = _ := by
      simp only [t, upper, Finset.prod_mul_distrib]
      rw [Finset.prod_comm (f := fun i j : Fin m => if j < i then f i j else 1)]

private abbrev Laurent (m : ℕ) := AddMonoidAlgebra ℚ (Fin m → ℤ)

private def lx {m : ℕ} (i : Fin m) : Laurent m := AddMonoidAlgebra.single (Pi.single i 1) 1

private def rev (m : ℕ) : Laurent m ≃ₐ[ℚ] Laurent m :=
  AddMonoidAlgebra.domCongr ℚ ℚ (AddEquiv.neg _)

/-- The constant coefficient of a Laurent polynomial times its reversal is a sum of squares. -/
private lemma norm_coeff_pos {m : ℕ} {f : Laurent m} (hf : f ≠ 0) :
    0 < (f * rev m f).coeff 0 := by
  simp only [AddMonoidAlgebra.coeff_mul_apply_left, rev, AddMonoidAlgebra.coeff_domCongr,
    add_zero, AddEquiv.neg_symm, AddEquiv.neg_apply, neg_neg, Finsupp.sum]
  apply Finset.sum_pos
  · intro i hi
    exact mul_self_pos.mpr (Finsupp.mem_support_iff.mp hi)
  · exact Finsupp.support_nonempty_iff.mpr (fun h => hf (AddMonoidAlgebra.coeff_eq_zero.mp h))

private lemma lx_ne {m : ℕ} {i j : Fin m} (h : i ≠ j) : lx i ≠ lx j := by
  intro e
  have he := AddMonoidAlgebra.single_left_injective (R := ℚ) one_ne_zero e
  simpa [Pi.single_apply, h] using congrFun he i

private lemma diff_reverse {m : ℕ} (i j : Fin m) :
    lx j - lx i = (lx i * lx j) * rev m (lx i - lx j) := by
  simp only [rev, lx, map_sub, AddMonoidAlgebra.domCongr_single, AddEquiv.neg_apply, mul_sub,
    AddMonoidAlgebra.single_mul_single, mul_one]
  abel_nf

private lemma upper_rev {m : ℕ} (f : Fin m → Fin m → Laurent m) :
    upper (fun i j => rev m (f i j)) = rev m (upper f) := by
  simp only [upper, map_prod, apply_ite (rev m), map_one]

private lemma upper_diff_ne (m : ℕ) : upper (fun i j : Fin m => lx i - lx j) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split
  · exact sub_ne_zero.mpr (lx_ne (by assumption : i < j).ne)
  · exact one_ne_zero

private lemma singles_prod {α : Type*} {m : ℕ} (s : Finset α) (a : α → Fin m → ℤ) :
    (∏ i ∈ s, (AddMonoidAlgebra.single (a i) 1 : Laurent m)) =
    AddMonoidAlgebra.single (∑ i ∈ s, a i) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddMonoidAlgebra.one_def]
  | insert i s hi ih => simp [hi, ih, AddMonoidAlgebra.single_mul_single]

private lemma shift_eq {m : ℕ} (n : ℕ) :
    (∏ i : Fin m, lx i ^ n) = AddMonoidAlgebra.single (fun _ => (n : ℤ)) 1 := by
  simp only [lx, AddMonoidAlgebra.single_pow, one_pow, singles_prod]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- Reverse each factor of the Vandermonde and collect the common monomial shift. -/
private lemma discr_factor (m : ℕ) :
    (∏ i : Fin m, ∏ j ∈ univ.erase i, (lx i - lx j)) =
      AddMonoidAlgebra.single (fun _ => ((m - 1 : ℕ) : ℤ)) 1 *
      (upper (fun i j : Fin m => lx i - lx j) * rev m (upper (fun i j : Fin m => lx i - lx j))) := by
  have hshift : upper (fun i j : Fin m => lx i * lx j) =
      AddMonoidAlgebra.single (fun _ => ((m - 1 : ℕ) : ℤ)) 1 := by
    rw [upper_mul, ← ordered_eq_upper (fun i _ : Fin m => lx i)]
    simpa using (shift_eq (m := m) (m - 1))
  rw [ordered_eq_upper]
  conv_lhs =>
    enter [2, 1, i, j]
    rw [diff_reverse i j]
  rw [upper_mul, upper_rev, hshift]
  ac_rfl

private theorem laurent_balanced_pos (m k : ℕ) :
    0 < ((∏ i : Fin m, ∏ j ∈ univ.erase i, (lx i - lx j)) ^ k).coeff
      (fun _ => (((m - 1) * k : ℕ) : ℤ)) := by
  rw [discr_factor, mul_pow, mul_pow, AddMonoidAlgebra.single_pow, one_pow, ← map_pow,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  have hexp : (-(k • fun _ : Fin m => ((m - 1 : ℕ) : ℤ)) + fun _ => (((m - 1) * k : ℕ) : ℤ)) = 0 := by
    funext i
    simp [mul_comm]
  rw [hexp]
  exact norm_coeff_pos (pow_ne_zero k (upper_diff_ne m))

variable {m : ℕ}

private def exponentMap (m : ℕ) : (Fin m →₀ ℕ) →+ (Fin m → ℤ) where
  toFun d i := (d i : ℤ)
  map_zero' := rfl
  map_add' a b := by ext i; exact Nat.cast_add _ _

private def asLaurent (m : ℕ) : MvPolynomial (Fin m) ℚ →+* AddMonoidAlgebra ℚ (Fin m → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom ℚ (exponentMap m)

private theorem asLaurent_coeff (p : MvPolynomial (Fin m) ℚ) (d : Fin m →₀ ℕ) :
    (asLaurent m p).coeff (fun i => (d i : ℤ)) = p.coeff d := by
  apply Finsupp.mapDomain_apply_of_injective (f := exponentMap m)
  intro a b h
  ext i
  exact Nat.cast_injective (R := ℤ) (congrFun h i)

private theorem asLaurent_X (i : Fin m) :
    asLaurent m (MvPolynomial.X i) =
      lx i := by
  change AddMonoidAlgebra.mapDomain (exponentMap m) (AddMonoidAlgebra.single _ _) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  congr 1
  ext j
  by_cases h : i = j <;> simp [exponentMap, h, eq_comm]

/-- In the ordered product of all differences, the monomial with equal exponents
has positive coefficient in every power. -/
theorem orderedVandermonde_balanced_coeff_pos (m k : ℕ) :
    0 < ((∏ i : Fin m, ∏ j ∈ univ.erase i,
      (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial (Fin m) ℚ)) ^ k).coeff
      (Finsupp.equivFunOnFinite.symm (fun _ => (m - 1) * k)) := by
  rw [← asLaurent_coeff]
  simpa [map_prod, asLaurent_X] using laurent_balanced_pos m k

open MvPolynomial

/-- Impose precisely the relations that each coordinate has vanishing Nth power. -/
private def truncIdeal (m N : ℕ) : Ideal (MvPolynomial (Fin m) ℚ) :=
  Ideal.span ((fun d => monomial d (1 : ℚ)) '' Set.range (fun i : Fin m => Finsupp.single i N))

private abbrev Trunc (m N : ℕ) := (MvPolynomial (Fin m) ℚ) ⧸ truncIdeal m N

private def truncX (m N : ℕ) (i : Fin m) : Trunc m N := Ideal.Quotient.mk _ (X i)

private theorem trunc_mk_ne_zero_of_coeff {m N : ℕ} {p : MvPolynomial (Fin m) ℚ} {d : Fin m →₀ ℕ}
    (hc : p.coeff d ≠ 0) (hd : ∀ i, d i < N) : Ideal.Quotient.mk (truncIdeal m N) p ≠ 0 := by
  classical
  intro hz
  obtain ⟨_, ⟨i, rfl⟩, hle⟩ := mem_ideal_span_monomial_image.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    d (mem_support_iff.mpr hc)
  exact (Nat.not_le_of_lt (hd i)) (by simpa using hle i)

private theorem truncX_pow (m N : ℕ) (i : Fin m) : truncX m N i ^ N = 0 := by
  rw [truncX, ← map_pow, Ideal.Quotient.eq_zero_iff_mem, X_pow_eq_monomial]
  exact Ideal.subset_span ⟨_, ⟨i, rfl⟩, rfl⟩

private theorem isUnit_trunc_shift (m N : ℕ) (i j : Fin m) :
    IsUnit ((1 + truncX m N i) - 2 * (1 + truncX m N j)) := by
  rw [show (1 + truncX m N i) - 2 * (1 + truncX m N j) =
    (truncX m N i - 2 * truncX m N j) - 1 by ring]
  apply IsNilpotent.isUnit_sub_one
  apply Commute.isNilpotent_sub (.all _ _)
  · exact ⟨N, truncX_pow m N i⟩
  · exact ⟨N, by rw [mul_pow, truncX_pow, mul_zero]⟩

private theorem trunc_hecke_ne_zero {m N k : ℕ} (hlt : (m - 1) * k < N) :
    heckeDiscriminant 2 (fun i => 1 + truncX m N i) ^ k ≠ 0 := by
  classical
  let P : MvPolynomial (Fin m) ℚ := ∏ i, ∏ j ∈ Finset.univ.erase i, (X i - X j)
  let E := ∏ i, ∏ j ∈ Finset.univ.erase i, ((1 + truncX m N i) - 2 * (1 + truncX m N j))
  have hE : IsUnit E := IsUnit.prod_univ_iff.mpr fun i =>
    IsUnit.prod_iff.mpr fun j _ => isUnit_trunc_shift m N i j
  have h : heckeDiscriminant 2 (fun i => 1 + truncX m N i) =
      Ideal.Quotient.mk (truncIdeal m N) P * E := by
    simp only [heckeDiscriminant, add_sub_add_left_eq_sub, Finset.prod_mul_distrib,
      P, E, map_prod, map_sub, truncX]
  rw [h, mul_pow, ne_eq, (hE.pow k).mul_left_eq_zero, ← map_pow]
  exact trunc_mk_ne_zero_of_coeff (orderedVandermonde_balanced_coeff_pos m k).ne'
    (fun _ => by simpa using hlt)

/-- For a common positive nilpotence bound `N`, power `k` kills the ordered Hecke
discriminant in every commutative ring precisely when `N ≤ (m - 1) * k`. -/
theorem heckeDiscriminant_universal_pow_iff {m N k : ℕ} (hN : 0 < N) :
    (∀ (S : Type u) [CommRing S] (q a : S) (U : Fin m → S),
      (∀ i, (U i - a) ^ N = 0) → heckeDiscriminant q U ^ k = 0) ↔ N ≤ (m - 1) * k := by
  constructor
  · intro h
    by_contra! hlt
    let R := Trunc m N
    let V := fun i => 1 + truncX m N i
    have hV (i : Fin m) : (V i - 1) ^ N = 0 := by simpa [V] using truncX_pow m N i
    let e : R ≃+* ULift.{u} R := ULift.ringEquiv.symm
    have hv : ∀ i, (e (V i) - e 1) ^ N = 0 := fun i => by
      rw [← map_sub, ← map_pow, hV, map_zero]
    have hz := h (ULift.{u} R) (e 2) (e 1) (fun i => e (V i)) hv
    apply trunc_hecke_ne_zero hlt
    change heckeDiscriminant (2 : R) V ^ k = 0
    exact e.injective (by simpa [heckeDiscriminant, map_prod] using hz)
  · intro hk S _ q a U hU
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simpa using hN.trans_le hk)
    apply heckeDiscriminant_pow_of_cluster (e := Function.Embedding.refl _) (r := fun _ => N - 1)
      (a := a)
    · simpa [Nat.sub_add_cancel hN] using hU
    · simpa [mul_comm (N - 1), Nat.mul_assoc] using
        (Nat.mul_lt_mul_of_pos_left (show N - 1 < (m - 1) * k by omega) hm)

end

end UpperTheory.V.Th
