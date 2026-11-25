module

public import Development.AutomorphicArithmetic.CharacterBoxes.PairGood

@[expose] public section

open Formalism.HC Filter Set
open scoped Topology

namespace UpperTheory.Top

/-- The left boundary of the cell on which the interior has unique page number `n + 1`. -/
noncomputable def pageStart (eps : ℝ) (n : ℕ) : ℝ := ((2 : ℝ) ^ n) ^ (2 + 8 * eps)⁻¹

/-- Exactly the finite index set for the dyadic tests in a half-open window. -/
theorem pageStart_mem_iff {eps Y Z : ℝ} (he : 0 < eps) (hY : 0 < Y) (hZ : 0 < Z) (n : ℕ) :
    (Y ≤ pageStart eps n ∧ pageStart eps n < Z) ↔
      n ∈ Finset.Ico ⌈(2 + 8 * eps) * Real.log Y / Real.log 2⌉₊ ⌈(2 + 8 * eps) * Real.log Z / Real.log 2⌉₊ := by
  let a := 2 + 8 * eps
  have ha : 0 < a := by dsimp [a]; positivity
  unfold pageStart
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : 0 < ((2 : ℝ) ^ n) ^ a⁻¹ := by positivity
  have hlog : Real.log (((2 : ℝ) ^ n) ^ a⁻¹) = (n : ℝ) * Real.log 2 / a := by
    rw [Real.log_rpow (by positivity), Real.log_pow]
    ring
  rw [← Real.log_le_log_iff hY hpt, ← Real.log_lt_log_iff hpt hZ, hlog, Finset.mem_Ico,
    Nat.ceil_le, Nat.lt_ceil, le_div_iff₀ ha, div_lt_iff₀ ha, div_le_iff₀ h2, lt_div_iff₀ h2]
  simp only [a, mul_comm]

/-- Test one point per dyadic cell, not every real point of the window. -/
def DyadicWindowAtWidth (ψ : PChar) (eps w b : ℝ) : Prop :=
  ∃ J : ℝ, 1 ≤ J ∧ ∀ A : ℝ, ∃ X ≥ A, ∃ q d : ℕ, PairGood ψ.N eps (X ^ (1 / J)) X q d ∧
    ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ w ≤ X ∧ ∀ n : ℕ, Y ≤ pageStart eps n →
      pageStart eps n < Y ^ w → VAt ψ eps b q d (n + 1) (pageStart eps n)

def DyadicVWinBelowWidth (ψ : PChar) (δ w b : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → eps < δ → DyadicWindowAtWidth ψ eps w b

private theorem pageStart_cover (eps x : ℝ) (he : 0 < eps) (hx : 1 ≤ x) :
    ∃ n : ℕ, PageN eps x (n + 1) ∧ pageStart eps n ≤ x ∧ x ≤ 2 * pageStart eps n := by
  let a := 2 + 8 * eps
  have ha : 0 < a := by dsimp [a]; positivity
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  obtain ⟨n, hlo, hup⟩ := exists_nat_pow_near (Real.one_le_rpow hx ha.le) (by norm_num : (1 : ℝ) < 2)
  have ht : 0 ≤ pageStart eps n := Real.rpow_nonneg (by positivity) _
  have heq : pageStart eps n ^ a = (2 : ℝ) ^ n := Real.rpow_inv_rpow (by positivity) ha.ne'
  refine ⟨n, ⟨hup.le, ?_⟩, (Real.rpow_le_rpow_iff ht hx₀ ha).mp (heq.trans_le hlo), ?_⟩
  · rw [pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_left hlo (by norm_num)
  · apply (Real.rpow_le_rpow_iff hx₀ (by positivity) ha).mp
    rw [Real.mul_rpow (by norm_num) ht, heq]
    have h2 : (2 : ℝ) ≤ 2 ^ a := calc
      2 = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by dsimp [a]; linarith)
    rw [pow_succ, mul_comm] at hup
    exact hup.le.trans (mul_le_mul_of_nonneg_right h2 (by positivity))

private theorem eventually_scaled_lt {a b : ℝ} (hab : a < b) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x ≥ M, (2 * x) ^ a < x ^ b := by
  have hab' := sub_pos.mpr hab
  let C := (2 : ℝ) ^ a + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨max 1 (C ^ (b - a)⁻¹), le_max_left _ _, fun x hx => ?_⟩
  have hx₀ := zero_lt_one.trans_le ((le_max_left _ _).trans hx)
  have h := Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) ((le_max_right _ _).trans hx) hab'.le
  rw [Real.rpow_inv_rpow hC.le hab'.ne'] at h
  rw [Real.mul_rpow (by norm_num) hx₀.le, show b = (b - a) + a by ring, Real.rpow_add hx₀]
  exact mul_lt_mul_of_pos_right ((lt_add_one _).trans_le h) (Real.rpow_pos_of_pos hx₀ _)

private theorem DyadicWindowAtWidth.toJoint_of_le {ψ : PChar} {eps w v b : ℝ}
    {depth : ℝ → ℝ} {B : ℝ} (hdepth : ∀ x ≥ B, depth x ≤ (x / 2) ^ b)
    (he : 0 < eps) (hvw : v < w) (hb : 0 ≤ b) (h : DyadicWindowAtWidth ψ eps w b) :
    JointWindowAtWidth ψ eps v depth := by
  obtain ⟨J, hJ, hX⟩ := h
  obtain ⟨M₀, hM₀, hs⟩ := eventually_scaled_lt hvw
  let M := max M₀ B
  have hM : 1 ≤ M := hM₀.trans (le_max_left _ _)
  have hMn := zero_le_one.trans hM
  have hJ₀ := zero_lt_one.trans_le hJ
  refine ⟨J, hJ, fun A => ?_⟩
  obtain ⟨X, hXA, q, d, hpair, Y, hbase, hupper, hsample⟩ := hX (max A (M ^ J))
  have hMX := (le_max_right _ _).trans hXA
  have hMY : M ≤ Y := calc
    M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hMn hJ₀.ne']
    _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hMn _) hMX (by positivity)
    _ ≤ Y := hbase
  have hY₀ := hMn.trans hMY
  have hY2 : Y ≤ 2 * Y := by linarith
  have hend := hs Y ((le_max_left _ _).trans hMY)
  refine ⟨X, (le_max_left _ _).trans hXA, q, d, hpair, 2 * Y, hbase.trans hY2, hend.le.trans hupper, fun x hlo hup => ?_⟩
  obtain ⟨n, hpage, htx, hxt⟩ := pageStart_cover eps x he ((hM.trans hMY).trans (hY2.trans hlo))
  have ht : 0 ≤ pageStart eps n := Real.rpow_nonneg (by positivity) _
  have hV := hsample n (by linarith) (htx.trans_lt (hup.trans_lt hend))
  refine ⟨n + 1, hpage, fun E _ _ hE => (hV E hE).mono (Nat.floor_mono ?_) ?_⟩
  · have hx₀ : 0 ≤ x := by linarith
    calc depth x ≤ (x / 2) ^ b := hdepth x ((le_max_right _ _).trans (hMY.trans (hY2.trans hlo)))
      _ ≤ _ := Real.rpow_le_rpow (by linarith) (by linarith) hb
  · exact Real.sqrt_le_sqrt (Real.exp_le_exp.mpr (Real.rpow_le_rpow ht htx he.le))

/-- Inside a slightly narrower window, each point lies above a sampled anchor at least half
its size. The cutoff loses only a fixed multiplier, not its exponent. -/
theorem DyadicWindowAtWidth.toJoint {ψ : PChar} {eps w v b : ℝ}
    (he : 0 < eps) (hvw : v < w) (hb : 0 ≤ b) (h : DyadicWindowAtWidth ψ eps w b) :
    JointWindowAtWidth ψ eps v (fun x => (1 / 2 ^ b) * x ^ b) := by
  apply h.toJoint_of_le (B := 0) _ he hvw hb
  intro x hx
  rw [Real.div_rpow hx (by norm_num)]
  exact le_of_eq (by ring)

theorem DyadicVWinBelowWidth.toJoint {ψ : PChar} {δ w v b : ℝ}
    (hvw : v < w) (hb : 0 ≤ b) (h : DyadicVWinBelowWidth ψ δ w b) :
    JointVWinBelowWidth ψ δ v (fun _ x => (1 / 2 ^ b) * x ^ b) :=
  fun eps he he' hδ => (h eps he he' hδ).toJoint he hvw hb

/-- An arbitrarily small power gap absorbs the constant lost between neighboring samples. -/
theorem DyadicVWinBelowWidth.toJointPower {ψ : PChar} {δ w v b a : ℝ}
    (hvw : v < w) (hab : a < b) (hb : 0 ≤ b) (h : DyadicVWinBelowWidth ψ δ w b) :
    JointVWinBelowWidth ψ δ v (fun _ x => x ^ a) := by
  obtain ⟨M, _, hs⟩ := eventually_scaled_lt hab
  intro eps he he' hδ
  apply (h eps he he' hδ).toJoint_of_le (B := 2 * M) _ he hvw hb
  intro x hx
  have hp := (hs (x / 2) (by linarith)).le
  rwa [show (2 : ℝ) * (x / 2) = x by ring] at hp

/-- At a dyadic boundary both pages are legal. Immediately to its right only the
upper page is legal, and its arithmetic upper bound is closed under that limit. -/
theorem vAt_succ_of_window {ψ : Formalism.HC.PChar} {eps b x Y Z : ℝ} {q d n : ℕ}
    (he : 0 < eps) (hb : 0 ≤ b) (hx : 0 < x) (hpow : x ^ (2 + 8 * eps) = (2 : ℝ) ^ n)
    (hY : Y ≤ x) (hZ : x < Z)
    (h : ∀ y : ℝ, Y ≤ y → y ≤ Z → ∃ e : ℕ, PageN eps y e ∧ VAt ψ eps b q d e y) :
    VAt ψ eps b q d (n + 1) x := by
  have htop : x ^ (2 + 8 * eps) < (2 : ℝ) ^ (n + 1) := by
    rw [hpow, pow_succ]
    linarith [show (0 : ℝ) < 2 ^ n by positivity]
  have hcont : ContinuousAt (fun y : ℝ => y ^ (2 + 8 * eps)) x := by fun_prop (disch := positivity)
  have hel : ∀ᶠ y in 𝓝[>] x, VAt ψ eps b q d (n + 1) y := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hZ),
      nhdsWithin_le_nhds (hcont (Iio_mem_nhds htop))] with y hxy hyZ hup
    change x < y at hxy
    obtain ⟨e, hp, hv⟩ := h y (hY.trans hxy.le) hyZ.le
    have hlo : (2 : ℝ) ^ n < y ^ (2 + 8 * eps) := by
      rw [← hpow]
      exact Real.rpow_lt_rpow hx.le hxy (by positivity)
    have hn : n < e := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp (hlo.trans_le hp.1)
    have hs : e < n + 2 := by
      apply (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp
      calc (2 : ℝ) ^ e ≤ 2 * y ^ (2 + 8 * eps) := hp.2
        _ < 2 * (2 : ℝ) ^ (n + 1) := mul_lt_mul_of_pos_left hup (by norm_num : (0 : ℝ) < 2)
        _ = 2 ^ (n + 2) := by rw [pow_succ (2 : ℝ) (n + 1), mul_comm]
    simpa only [show e = n + 1 by omega] using hv
  intro E _ _ hE
  have hev : ∀ᶠ y in 𝓝[>] x, VVle E ⌊x ^ b⌋₊ (Real.sqrt (Real.exp (y ^ eps))) := by
    filter_upwards [hel, self_mem_nhdsWithin] with y hy hxy
    exact (hy E hE).mono (Nat.floor_mono (Real.rpow_le_rpow hx.le hxy.le hb)) le_rfl
  intro Ω _ _ _ ld
  obtain ⟨_, hu⟩ := hev.exists
  refine ⟨(hu Ω ld).1, fun S => ?_⟩
  have hlim : ContinuousAt (fun y : ℝ => Real.sqrt (Real.exp (y ^ eps))) x := by fun_prop (disch := positivity)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim.continuousWithinAt
    (hev.mono fun y hy => (hy Ω ld).2 S)

/-- The pointwise window already implies the sampled one at its original width and power. -/
theorem JointWindowAtWidth.toDyadic {ψ : PChar} {eps w b : ℝ} (he : 0 < eps) (hb : 0 ≤ b)
    (h : JointWindowAtWidth ψ eps w (fun x => x ^ b)) : DyadicWindowAtWidth ψ eps w b := by
  obtain ⟨J, hJ, hw⟩ := h
  refine ⟨J, hJ, fun A => ?_⟩
  obtain ⟨X, hX, q, d, hp, Y, hlo, hup, hgood⟩ := hw A
  refine ⟨X, hX, q, d, hp, Y, hlo, hup, fun n hY hZ => ?_⟩
  apply vAt_succ_of_window he hb (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_inv_rpow (by positivity) (by positivity)) hY hZ hgood

/-- Allowing any powers above the analytic cutoffs, a finite dyadic checklist per window
is equivalent to testing every real point in a window. -/
theorem has_dyadic_power_window_iff (ψ : PChar) :
    (∃ b > (797 / 2 : ℝ), ∃ w > (1 : ℝ), ∃ δ > 0, DyadicVWinBelowWidth ψ δ w b) ↔
    ∃ b > (797 / 2 : ℝ), ∃ w > (1 : ℝ), ∃ δ > 0, JointVWinBelowWidth ψ δ w (fun _ x => x ^ b) := by
  constructor
  · rintro ⟨b, hb, w, hw, δ, hδ, h⟩
    obtain ⟨a, ha, hab⟩ := exists_between hb
    obtain ⟨v, hv, hvw⟩ := exists_between hw
    exact ⟨a, ha, v, hv, δ, hδ, h.toJointPower hvw hab (by linarith)⟩
  · rintro ⟨b, hb, w, hw, δ, hδ, h⟩
    exact ⟨b, hb, w, hw, δ, hδ, fun eps he he' ht => (h eps he he' ht).toDyadic he (by linarith)⟩

end UpperTheory.Top
