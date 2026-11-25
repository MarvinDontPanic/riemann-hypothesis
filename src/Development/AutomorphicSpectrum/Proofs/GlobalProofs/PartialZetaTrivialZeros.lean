module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaFunctionalEquation

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace GroundTheory.Global GroundTheory.Global.IdeleGroup
open GlobalTheory.CompanionTheory.PartialZeta GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open Complex Filter Topology
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Hypotheses₂

variable {F : Type} [Field F] [NumberField F]

/-- Two continuations of the same class Dirichlet series agree away from the pole. -/
theorem isPartialZeta_eqOn {C : ClassGroup (𝓞 F)} {Z W : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (hW : IsPartialZeta C W) : Set.EqOn Z W {1}ᶜ := by
  have ho : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  refine (hZ.1.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (hW.1.analyticOnNhd ho)
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (z₀ := 2) (by norm_num) ?_
  have hh : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hh.mem_nhds (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by simp)] with s hs
  exact (hZ.2 s hs).unique (hW.2 s hs)

/-- An ordinary partial zeta is strictly positive real on the real half-ray x > 1. -/
theorem isPartialZeta_pos_right {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ} (hZ : IsPartialZeta C Z)
    (x : ℝ) (hx : 1 < x) : 0 < Z (x : ℂ) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C
  have h := hZ.2 (x : ℂ) (by simpa using hx)
  have hp (I : {I : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 I = C}) :
      0 < ((Ideal.absNorm (I.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-(x : ℂ)) := by
    rw [Complex.cpow_neg]
    exact Complex.inv_natCast_cpow_ofReal_pos (Ideal.absNorm_pos_of_nonZeroDivisors I.1).ne' x
  rw [← h.tsum_eq]
  exact h.summable.tsum_pos (fun I => (hp I).le) ⟨J, hJ⟩ (hp ⟨J, hJ⟩)

private theorem order_inv_Gamma_neg_nat (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gamma z)⁻¹) (-(n : ℂ)) = 1 := by
  let γ := fun z : ℂ => (Gamma z)⁻¹
  let t := fun z : ℂ => z + 1
  change analyticOrderAt γ _ = 1
  have ht (x : ℂ) : HasDerivAt t 1 x := by simpa [t] using (hasDerivAt_id x).add_const 1
  have recur (x : ℂ) : analyticOrderAt γ x = analyticOrderAt id x + analyticOrderAt γ (x + 1) := by
    have eq : γ = (id : ℂ → ℂ) * (γ ∘ t) := funext one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
    calc
      _ = analyticOrderAt ((id : ℂ → ℂ) * (γ ∘ t)) x := congrArg (analyticOrderAt · x) eq
      _ = _ := by
        rw [analyticOrderAt_mul analyticAt_id ((differentiable_one_div_Gamma.analyticAt _).comp
          (show AnalyticAt ℂ t x by dsimp [t]; fun_prop)),
          analyticOrderAt_comp_of_deriv_ne_zero (by dsimp [t]; fun_prop) (by rw [(ht x).deriv]; norm_num)]
  induction n with
  | zero =>
      rw [Nat.cast_zero, neg_zero, recur, zero_add]
      have ho : analyticOrderAt (id : ℂ → ℂ) 0 = 1 := by
        simp
      rw [ho, analyticOrderAt_eq_zero.mpr (.inr (by simp [γ, Gamma_one])), add_zero]
  | succ n ih =>
      have hn : (id : ℂ → ℂ) (-(n.succ : ℂ)) ≠ 0 :=
        neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
      rw [recur, analyticOrderAt_eq_zero.mpr (.inr hn), zero_add,
        show -(n.succ : ℂ) + 1 = -(n : ℂ) by push_cast; ring]
      exact ih

private theorem order_inv_GammaC_neg_nat (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gammaℂ z)⁻¹) (-(n : ℂ)) = 1 := by
  let U := fun s : ℂ => (2 * (2 * (Real.pi : ℂ)) ^ (-s))⁻¹
  have hU : AnalyticAt ℂ U (-(n : ℂ)) :=
    (Differentiable.inv ((differentiable_neg.const_cpow (by simp)).const_mul 2) (by simp)).analyticAt _
  have eq : (fun z : ℂ => (Gammaℂ z)⁻¹) = (fun z : ℂ => (Gamma z)⁻¹) * U :=
    funext fun s => by simp [Gammaℂ_def, U, Pi.mul_apply]
  rw [eq, analyticOrderAt_mul (differentiable_one_div_Gamma.analyticAt _) hU, order_inv_Gamma_neg_nat,
    hU.analyticOrderAt_eq_zero.mpr (by simp [U]), add_zero]

private theorem order_inv_GammaR_neg_even (n : ℕ) :
    analyticOrderAt (fun z : ℂ => (Gammaℝ z)⁻¹) (-(2 * (n : ℂ))) = 1 := by
  let U := fun s : ℂ => ((Real.pi : ℂ) ^ (-s / 2))⁻¹
  let t := fun s : ℂ => s / 2
  have hU : AnalyticAt ℂ U (-(2 * (n : ℂ))) :=
    (Differentiable.inv ((differentiable_neg.div_const (2 : ℂ)).const_cpow (by simp)) (by simp)).analyticAt _
  have ht : AnalyticAt ℂ t (-(2 * (n : ℂ))) := by dsimp [t]; fun_prop
  have eq : (fun z : ℂ => (Gammaℝ z)⁻¹) = ((fun z : ℂ => (Gamma z)⁻¹) ∘ t) * U :=
    funext fun s => by simp [Gammaℝ_def, U, t, Pi.mul_apply]
  rw [eq, analyticOrderAt_mul ((differentiable_one_div_Gamma.analyticAt _).comp ht) hU,
    analyticOrderAt_comp_of_deriv_ne_zero ht (by dsimp [t]; simp),
    hU.analyticOrderAt_eq_zero.mpr (by simp [U]), add_zero,
    show t (-(2 * (n : ℂ))) = -(n : ℂ) by dsimp [t]; ring, order_inv_Gamma_neg_nat]

/-- An analytic numerator nonzero at the target does not cancel any archimedean zero. -/
private theorem orderAt_signature_quotient_eq (r c n : ℕ) (G Z : ℂ → ℂ) (hG : AnalyticAt ℂ G (-(n : ℂ)))
    (hnz : G (-(n : ℂ)) ≠ 0) (hz : Z =ᶠ[𝓝 (-(n : ℂ))] fun z =>
      (Gammaℝ z ^ r * Gammaℂ z ^ c)⁻¹ * G z) :
    analyticOrderAt Z (-(n : ℂ)) = (if Even n then (r : ℕ∞) else 0) + c := by
  let R := fun s : ℂ => (Gammaℝ s)⁻¹
  let C := fun s : ℂ => (Gammaℂ s)⁻¹
  have hR : AnalyticAt ℂ R (-(n : ℂ)) := differentiable_Gammaℝ_inv.analyticAt _
  have hC : AnalyticAt ℂ C (-(n : ℂ)) := differentiable_Gammaℂ_inv.analyticAt _
  have eq : Z =ᶠ[𝓝 (-(n : ℂ))] (R ^ r * C ^ c) * G :=
    hz.trans <| .of_forall fun s => by simp [R, C, Pi.mul_apply, Pi.pow_apply, mul_comm]
  rw [analyticOrderAt_congr eq, analyticOrderAt_mul ((hR.pow r).mul (hC.pow c)) hG,
    hG.analyticOrderAt_eq_zero.mpr hnz, add_zero, analyticOrderAt_mul (hR.pow r) (hC.pow c),
    analyticOrderAt_pow hR, analyticOrderAt_pow hC, order_inv_GammaC_neg_nat, nsmul_one]
  split_ifs with hn
  · obtain ⟨j, rfl⟩ := hn
    rw [show (↑(j + j) : ℂ) = 2 * (j : ℂ) by push_cast; ring, order_inv_GammaR_neg_even, nsmul_one]
  · have hr : R (-(n : ℂ)) ≠ 0 := by
      apply inv_ne_zero
      intro h
      obtain ⟨j, hj⟩ := Gammaℝ_eq_zero_iff.mp h
      apply hn
      refine ⟨j, ?_⟩
      have hj' := neg_inj.mp hj
      rw [two_mul] at hj'
      exact_mod_cast hj'
    rw [hR.analyticOrderAt_eq_zero.mpr hr, nsmul_zero]

private theorem classDiscriminant_ne_zero (F : Type) [Field F] [NumberField F] : (dF F : ℂ) ≠ 0 := by
  exact Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))

private theorem classGamma_ne_of_re_pos {s : ℂ} (hs : 0 < s.re) : classGamma F s ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (Gammaℝ_ne_zero_of_re_pos hs)) (pow_ne_zero _ ?_)
  rw [Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl
    (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))) (Gamma_ne_zero_of_re_pos hs)

/-- On the open left half-plane, normalization is valid even at a pole of the
archimedean Gamma factor. -/
theorem zetaOfClass_eq_normalized_of_re_neg (C : ClassGroup (𝓞 F)) {s : ℂ} (hs : s.re < 0) :
    zetaOfClass C s = (classGamma F s)⁻¹ * ((dF F : ℂ) ^ (-(s / 2)) * completedZetaOfClass C s) := by
  classical
  rw [zetaOfClass, completedZetaOfClass, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  have hU := standardOpenSubgroup_le_ker ψ
  have hL : (classHecke ψ).continuedLFunction s = (classHecke ψ).normalizedLFunction s := by
    by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F, ((classHecke ψ).toIdele x : ℂ) =
        ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * I)
    · obtain ⟨τ, hτ⟩ := h
      apply HeckeCharacter.continuedLFunction_of_ne hτ
      intro e
      rw [e] at hs
      simp at hs
    · rw [HeckeCharacter.continuedLFunction_of_not _ h]
  rw [hL, HeckeCharacter.normalizedLFunction, classGamma_eq _ hU, discrNormConductor_eq_dF_of_unramified F _ hU]
  ring

private theorem completedZetaOfClass_ne_of_real_neg (C : ClassGroup (𝓞 F)) (x : ℝ) (hx : x < 0) :
    completedZetaOfClass C (x : ℂ) ≠ 0 := by
  let D : (Ideal (𝓞 F))⁰ := ⟨differentIdeal ℤ (𝓞 F), mem_nonZeroDivisors_of_ne_zero _root_.differentIdeal_ne_bot⟩
  let C' := C⁻¹ * ClassGroup.mk0 D
  have h0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne
  have h1 : (x : ℂ) ≠ 1 := by norm_cast; linarith
  have hr : 1 < 1 - x := by linarith
  have heq : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by simp
  have hp : 0 < (1 - (x : ℂ)).re := by simp; linarith
  rw [completedZetaOfClass_functionalEquation C C' D rfl (by simp [C']) _ h0 h1,
    completedZetaOfClass_eq C' (classGamma_ne_of_re_pos hp)]
  refine mul_ne_zero (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (classDiscriminant_ne_zero F))) (classGamma_ne_of_re_pos hp)) ?_
  rw [heq]
  exact (isPartialZeta_pos_right (isPartialZeta_zetaOfClass C') (1 - x) hr).ne'

/-- At every negative real argument the only zeros of a partial zeta function are the
zeros of the totalized archimedean factor. -/
theorem isPartialZeta_eq_zero_iff_of_real_neg {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (x : ℝ) (hx : x < 0) : Z (x : ℂ) = 0 ↔ classGamma F x = 0 := by
  have h1 : (x : ℂ) ≠ 1 := by norm_cast; linarith
  rw [isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C) h1, zetaOfClass_eq_normalized_of_re_neg C hx]
  simp [completedZetaOfClass_ne_of_real_neg C x hx, Complex.cpow_ne_zero_iff.mpr (Or.inl (classDiscriminant_ne_zero F))]

/-- The exact multiplicity of an ordinary partial zeta zero at a strictly negative integer
is one per complex place, and one per real place precisely when the integer is even. -/
theorem isPartialZeta_order_neg_nat {C : ClassGroup (𝓞 F)} {Z : ℂ → ℂ}
    (hZ : IsPartialZeta C Z) (n : ℕ) (hn : 0 < n) :
    analyticOrderAt Z (-(n : ℂ)) = (if Even n then (nrRealPlaces F : ℕ∞) else 0) + nrComplexPlaces F := by
  let g := fun t : ℂ => (dF F : ℂ) ^ (-(t / 2)) * completedZetaOfClass C t
  have hr : -(n : ℝ) < 0 := by exact neg_lt_zero.mpr (by exact_mod_cast hn)
  have hs : (-(n : ℂ)).re < 0 := by simpa using hr
  have h0 : -(n : ℂ) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')
  have h1 : -(n : ℂ) ≠ 1 := by intro e; rw [e] at hs; norm_num at hs
  have hD : Differentiable ℂ (fun t : ℂ => (dF F : ℂ) ^ (-(t / 2))) :=
    fun _ => DifferentiableAt.const_cpow (by fun_prop) (Or.inl (classDiscriminant_ne_zero F))
  apply orderAt_signature_quotient_eq _ _ n g Z
  · exact (hD.analyticAt _).mul (analyticAt_completedZetaOfClass C h0 h1)
  · apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl (classDiscriminant_ne_zero F)))
    simpa using completedZetaOfClass_ne_of_real_neg C _ hr
  · apply Filter.EventuallyEq.trans (Filter.mem_of_superset (isOpen_compl_singleton.mem_nhds h1)
      (isPartialZeta_eqOn hZ (isPartialZeta_zetaOfClass C)))
    have ho : IsOpen {t : ℂ | t.re < 0} := isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [ho.mem_nhds hs] with t ht
    exact zetaOfClass_eq_normalized_of_re_neg C ht

end GlobalTheory.CompanionTheory.Hypotheses₂
