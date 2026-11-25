module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory

theorem addMonoidHom_intCast_mul_real {A : Type} [CommRing A] (θ : A →+ ℝ) (k : ℤ) (z : A) :
    θ ((k : A) * z) = (k : ℝ) * θ z := by
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

/-- Agreement on `m+1` distinct diagonal powers on a pencil determines all of its
mixed powers, not just the term that is linear in the first direction. -/
theorem mixed_powers_of_pencil {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+ ℝ) (ψ : B →+ ℝ) (x y : A) (u v : B) (m : ℕ) (s : Fin (m + 1) ↪ ℤ)
    (h : ∀ i, φ (((s i : A) * x + y) ^ m) = ψ (((s i : B) * u + v) ^ m))
    (k : ℕ) (hk : k ≤ m) : φ (x ^ k * y ^ (m - k)) = ψ (u ^ k * v ^ (m - k)) := by
  let P {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R) : Polynomial ℝ :=
    ∑ i ∈ Finset.range (m + 1), Polynomial.C (f (a ^ i * b ^ (m - i)) * (m.choose i : ℝ)) * Polynomial.X ^ i
  have eval_P {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R) (t : ℤ) :
      (P f a b).eval (t : ℝ) = f (((t : R) * a + b) ^ m) := by
    rw [add_pow, map_sum]
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    apply Finset.sum_congr rfl
    intro i _
    have step : ((t : R) * a) ^ i * b ^ (m - i) * (m.choose i : R) =
        ((t ^ i * (m.choose i : ℤ) : ℤ) : R) * (a ^ i * b ^ (m - i)) := by push_cast; ring
    rw [step, addMonoidHom_intCast_mul_real]
    push_cast
    ring
  have degree_P {R : Type} [CommRing R] (f : R →+ ℝ) (a b : R) : (P f a b).natDegree ≤ m :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have eqP : P φ x y = P ψ u v := by
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Int.cast_injective.comp s.injective)
    · intro i
      simpa only [Function.comp_apply, eval_P] using h i
    · simpa using Nat.lt_succ_of_le (max_le (degree_P φ x y) (degree_P ψ u v))
  have c := congrArg (fun p : Polynomial ℝ => p.coeff k) eqP
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Finset.sum_ite_eq, Finset.mem_range, ite_eq_left (Nat.lt_succ_of_le hk)] at c
  exact mul_right_cancel₀ (by exact_mod_cast (Nat.choose_pos hk).ne') c

open Polynomial in
/-- Fewer than `m + 1` polynomial probes cannot determine the values of an arbitrary
additive measurement on all the first `m + 1` monomials. -/
theorem exists_measurement_vanishing_on_probes {m r : ℕ} (hr : r ≤ m)
    (p : Fin r → ℝ[X]) :
    ∃ φ : ℝ[X] →+ ℝ, (∀ j, φ (p j) = 0) ∧ ∃ i : Fin (m + 1), φ (Polynomial.X ^ (i : ℕ)) ≠ 0 := by
  let T : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin r → ℝ) :=
    LinearMap.pi fun j => ∑ i : Fin (m + 1), (p j).coeff i • LinearMap.proj i
  have hn : LinearMap.ker T ≠ ⊥ := by
    intro he
    have hd := T.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp he)
    simp at hd
    omega
  obtain ⟨a, ha, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let L : ℝ[X] →ₗ[ℝ] ℝ := ∑ i : Fin (m + 1), a i • Polynomial.lcoeff ℝ i
  refine ⟨L.toAddMonoidHom, ?_, ?_⟩
  · intro j
    simpa [L, T, mul_comm] using congrFun (LinearMap.mem_ker.mp ha) j
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨i, ?_⟩
    simpa [L, Polynomial.coeff_X_pow, ← Fin.ext_iff] using hi

/-- For a fixed bundle combination, the nonnegative parameters `0,…,m`
recover every mixed coefficient of the degree-`m` pencil. -/
theorem polarisation_mixed_terms_on_pencil (A : Type) [CommRing A] (θ : A →+ ℝ)
    (ι : Type) [Fintype ι] (x : Option ι → A) (m : ℕ)
    (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ) (n : ι → ℤ)
    (h : ∀ i : Fin (m + 1), let r : Option ι → ℤ := fun o => o.elim i.val n
      Φ (lin (fun o => (r o : ℝ)) ^ m) = θ ((∑ o, r o • x o) ^ m))
    (k : ℕ) (hk : k ≤ m) :
    Φ (MvPolynomial.X none ^ k * rename some (lin fun i => (n i : ℝ)) ^ (m - k)) =
      θ (x none ^ k * (∑ i, n i • x (some i)) ^ (m - k)) := by
  let L := rename some (lin fun i => (n i : ℝ))
  let y := ∑ i, n i • x (some i)
  let s : Fin (m + 1) ↪ ℤ := ⟨fun i => i.val, fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  have test (i : Fin (m + 1)) :
      Φ (((s i : MvPolynomial (Option ι) ℝ) * MvPolynomial.X none + L) ^ m) =
        θ (((s i : A) * x none + y) ^ m) := by
    change Φ ((((i.val : ℤ) : MvPolynomial (Option ι) ℝ) * MvPolynomial.X none + L) ^ m) =
      θ ((((i.val : ℤ) : A) * x none + y) ^ m)
    simpa [L, y, lin, Fintype.sum_option, zsmul_eq_mul, map_sum] using
      h i
  exact mixed_powers_of_pencil Φ.toAddMonoidHom θ (MvPolynomial.X none) L (x none) y m s test k hk

theorem polarisation_mixed_term_of_powers : ∀ (A : Type) [CommRing A] (θ : A →+ ℝ) (ι : Type) [Fintype ι] (x : Option ι → A) (D : ℕ) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), (∀ n : Option ι → ℤ, Φ (lin (fun o => (n o : ℝ)) ^ (D + 1)) = θ ((∑ o, n o • x o) ^ (D + 1))) → ∀ n : ι → ℤ, Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = θ ((∑ i, n i • x (some i)) ^ D * x none) := by
  intro A _ θ ι _ x D Φ h n
  simpa [mul_comm] using polarisation_mixed_terms_on_pencil A θ ι x (D + 1) Φ n
    (fun i => h (fun o => o.elim i.val n)) 1 (Nat.succ_pos D)

end GlobalTheory
