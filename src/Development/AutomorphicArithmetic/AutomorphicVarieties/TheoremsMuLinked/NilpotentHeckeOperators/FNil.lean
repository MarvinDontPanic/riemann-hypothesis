module

public import Mathlib

@[expose] public section

namespace UpperTheory.V.Th

/-- One-place factor of the discriminant used for the Hecke relations. -/
def heckeDiscriminant {S : Type*} [CommRing S] {n : ℕ} (q : S) (U : Fin n → S) : S :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, (U i - U j) * (U i - q * U j)

variable {S : Type*} [CommRing S] {n : ℕ} {q a : S} {U : Fin n → S} {i j : Fin n} {r s : ℕ}

private theorem sub_pow_zero {x y c a : S} (hx : (x - c * a) ^ r = 0)
    (hy : (y - a) ^ s = 0) : (x - c * y) ^ (r + s - 1) = 0 := by
  have hneg : (-c * (y - a)) ^ s = 0 := by rw [mul_pow, hy, mul_zero]
  rw [show x - c * y = (x - c * a) + (-c * (y - a)) by ring]
  exact (Commute.all _ _).add_pow_eq_zero_of_add_le_succ_of_pow_eq_zero hx hneg (by omega)

private theorem factor_dvd_row (hij : i ≠ j) :
    (U i - U j) * (U i - q * U j) ∣ ∏ k ∈ Finset.univ.erase i, (U i - U k) * (U i - q * U k) :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)

/-- A collision after multiplication by q requires nilpotence at just the two colliding roots. -/
theorem heckeDiscriminant_pow_of_shift (hij : i ≠ j) (hi : (U i - q * a) ^ r = 0)
    (hj : (U j - a) ^ s = 0) : heckeDiscriminant q U ^ (r + s - 1) = 0 := by
  have hd : U i - q * U j ∣ heckeDiscriminant q U :=
    ((dvd_mul_left _ _).trans (factor_dvd_row hij)).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact zero_dvd_iff.mp (sub_pow_zero hi hj ▸ pow_dvd_pow_of_dvd hd (r + s - 1))

/-- When the roots themselves coincide, the ordered product contains the difference twice. -/
theorem heckeDiscriminant_pow_of_eq (hij : i ≠ j) (hi : (U i - a) ^ r = 0)
    (hj : (U j - a) ^ s = 0) : heckeDiscriminant q U ^ ((r + s) / 2) = 0 := by
  let row := fun i => ∏ k ∈ Finset.univ.erase i, (U i - U k) * (U i - q * U k)
  have h1 : U i - U j ∣ row i := (dvd_mul_right _ _).trans (factor_dvd_row hij)
  have h2 : U i - U j ∣ row j := by
    rw [← neg_sub (U j) (U i), neg_dvd]
    exact (dvd_mul_right _ _).trans (factor_dvd_row hij.symm)
  have hd : (U i - U j) ^ 2 ∣ heckeDiscriminant q U := by
    refine (show (U i - U j) ^ 2 ∣ row i * row j by simpa [pow_two] using mul_dvd_mul h1 h2).trans ?_
    simpa [row, heckeDiscriminant, hij] using
      Finset.prod_dvd_prod_of_subset {i,j} Finset.univ row (Finset.subset_univ _)
  have hz : (U i - U j) ^ (r + s - 1) = 0 := by
    simpa using sub_pow_zero (c := 1) (a := a) (by simpa using hi) hj
  have hzero : ((U i - U j) ^ 2) ^ ((r + s) / 2) = 0 := by
    rw [← pow_mul]
    exact pow_eq_zero_of_le (by omega) hz
  exact zero_dvd_iff.mp (hzero ▸ pow_dvd_pow_of_dvd hd ((r + s) / 2))

-- Preserve the original uniform estimate used by the global patching argument.
theorem fNil :
    ∀ (K S : Type) [CommRing K] [IsDomain K] [CommRing S] (f : K →+* S) (n N q : ℕ) (α : Fin n → K) (U : Fin n → S), (∀ k, (U k - f (α k)) ^ N = 0) → ¬ (∀ i i', i ≠ i' → α i ≠ α i' ∧ α i ≠ (q : K) * α i') → (∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, (U i - U i') * (U i - (q : S) * U i')) ^ (2 * N) = 0 := by
  intro K S _ _ _ f n N q α U hU hne
  simp only [not_forall] at hne
  obtain ⟨i, j, hij, hα⟩ := hne
  change heckeDiscriminant (q : S) U ^ (2 * N) = 0
  by_cases h : α i = α j
  · have hi := hU i
    rw [h] at hi
    exact pow_eq_zero_of_le (by omega) (heckeDiscriminant_pow_of_eq hij hi (hU j))
  · have e : α i = (q : K) * α j := not_not.mp fun h' => hα ⟨h, h'⟩
    have hi := hU i
    rw [e, map_mul, map_natCast] at hi
    exact pow_eq_zero_of_le (by omega) (heckeDiscriminant_pow_of_shift hij hi (hU j))

end UpperTheory.V.Th
