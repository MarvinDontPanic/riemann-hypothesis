import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

/-
Core 12. The starting point for the evaluation lemmas, cyclotomic derivative
argument, single-branch divisibility and coefficient-projection idea was the
publicly visible prefix of Andrew Pullin’s entry #101654. Entry #100599
(dugbt607) also exhibits the last projection argument. The public #99275
solution (LewyM) and Alpöge’s original give reference proofs of the remaining
clauses. This file adapts public work; it is not an independent rediscovery
of the entire proof.

The refinements here include reading the n-th coefficient directly after
division and moving unit cancellation inside the shifted-coefficient map.
The single-branch and split completeness proofs use the same canonical
Weierstrass remainder and the same induction, with X regular in either
coefficient ring. One chain of divisibilities of iterates yields both
ideal-membership conclusions.
-/

set_option autoImplicit true

open PowerSeries hiding coe_mul map_comp
open IsLocalRing LevelStatements.Lv Ideal
open Polynomial hiding C X constantCoeff coeff algebraMap_eq X_ne_zero

variable [CommRing O] [CommRing S] [Algebra O S]

@[local simp] theorem mapPoly
    (ρ : PowerSeries O →ₐ[O] S) (r : Polynomial O) :
    ρ r = aeval (ρ X) r := by
  rw [← eval₂_C_X_eq_coe, aeval_algHom_apply]
  rfl

@[local simp] theorem ccEval
    (r : Polynomial O) :
    constantCoeff (aeval (x : PowerSeries S) r) = aeval (constantCoeff x) r := hom_eval₂ ..

theorem cycloDist : CycloDistStatement := by
  intro
  intros
  expose_names
  have w := (@cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt l ⟨h⟩ s).isWeaklyEisensteinAt.map (algebraMap ℤ O)
  simp_all [map_comp, map_span]
  exact ⟨⟨(span_le.2 (by simpa) <| w.mem ·)⟩, (cyclotomic.monic ..).comp_X_add_C 1⟩

theorem cycloSimple : CycloSimpleStatement := by
  intro
  intros
  expose_names
  have hg := sub_const_eq_shift_mul_X (aeval (C ζ * E) (cyclotomic m LL))
  generalize mk _ = g at hg
  simp_all
  refine ⟨(isUnit_iff_constantCoeff.2 ?_).unit, rfl⟩
  cases' cyclotomic.dvd_X_pow_sub_one m LL with Q hQ
  have := congrArg (aeval ζ) hQ
  apply_fun constantCoeff ∘ derivative ∘ aeval (C ζ * E) at hQ
  have := (Nat.cast_ne_zero.2 h.ne').isUnit.map (algebraMap LL S)
  simp_all [sub_eq_zero, pow_sub_one_mul h.ne']

/-- The one-branch and all-primitive-branches divisibility tests obey the same
Weierstrass descent. The polynomial remainder is detected differently in each branch; the induction
then cancels the same regular element X in either coefficient ring. -/
theorem weierstrassCompleteness : RhoComplStatement ∧ SplitComplStatement := by
  constructor <;> intro <;> intros <;> expose_names
  case' left => obtain ⟨w,unit⟩ := h_1
  case' right =>
    simp_rw [← eq_sub_iff_add_eq'] at h_3
    have hn := pow_pos h.pos s.succ
    have h := cycloDist O l s h h_1
    set P := (cyclotomic _ O).comp _
    choose w hw using fun z hp => cycloSimple LL LL _ hn z _ (IsPrimitiveRoot.isRoot_cyclotomic hn hp) constantCoeff_exp (derivative_exp LL)
    have unit z hp : ρ z P = (w z hp).val * X := by
      simp [P, aeval_comp, h_3 z hp]
      rw [← aeval_map_algebraMap LL, map_cyclotomic, hw z hp]
  all_goals
    induction' k with k ih generalizing a
    · simp
    let divisor := h.isWeierstrassDivisorAt'
    rw [(divisor.isWeierstrassDivisionAt_div_mod a).2] at *
    generalize divisor.mod a = r at *
    -- On the split branch, the distinct primitive roots detect every linear factor.
    obtain ⟨b,rfl⟩ : P ∣ r := by
      apply (map_dvd_map _ (IsFractionRing.injective O LL) h.monic).1
      first
      | apply h_2; simpa [*] using X_pow_dvd_iff.1 h_3 0 k.succ_pos
      | simp [P, map_comp]
        rw [← Polynomial.C_1, ← dvd_comp_X_sub_C_iff, cyclotomic_eq_prod_X_sub_primitiveRoots h_2.choose_spec]
        refine Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C Function.injective_id).set_pairwise _) fun z mem => ?_
        have hp := (mem_primitiveRoots hn).1 mem
        simpa [dvd_iff_isRoot, IsRoot, eval_map_algebraMap, *] using X_pow_dvd_iff.1 (h_4 z hp) 0 k.succ_pos
    rw [coe_mul, ← mul_add, pow_succ' _ k] at *
    gcongr; apply ih
    try intro z hp; specialize h_4 z hp
    simp_all [mul_assoc, IsLeftRegular.dvd_cancel_left, IsLeftRegular, X_mul_injective]

theorem AlpogeRHCore12.cyclotomicPowerSeriesRigidity :
    RhoUniqueStatement ∧ RhoComplStatement ∧ CycloDistStatement ∧ CycloSimpleStatement ∧
    ExpRescaleStatement ∧ DescendDvdStatement ∧ SplitComplStatement ∧ PsCoprimeStatement :=
  ⟨by
    intro
    intros
    expose_names
    -- After division by P^(n+1), the two polynomial remainders agree.
    -- The other term contains X^(n+1), so its n-th coefficient is zero.
    obtain ⟨u, hu⟩ := X_dvd_iff.2 h_2
    ext a n
    obtain ⟨q,r,-,rfl⟩ := exists_isWeierstrassDivision (g := (P : PowerSeries O) ^ n.succ) a (by simp [← polynomial_map_coe, (h.monic.map _).ne_zero])
    simp [← h_1, hu, mul_pow, mul_assoc, PowerSeries.coeff_X_pow_mul'],
  weierstrassCompleteness.1,
  cycloDist,
  cycloSimple,
  by
    intro S
    intros
    have := IsAddTorsionFree.of_module_rat S
    grind [exp_unique_of_derivative_eq_self, exp_pow_eq_rescale_exp],
  by
    unfold DescendDvdStatement
    intros
    expose_names
    cases' h_1 with w hι
    -- Remove the unit before dropping the first m coefficients. Iterating this
    -- operator gives a projection that turns multiplication by ι f into multiplication by f.
    let s : Module.End O (PowerSeries O) := .pi fun d => coeff (d () + m) ∘ₗ .mulLeft O w.inv
    let π Q := mk fun k => constantCoeff ((s ^ k) Q)
    have hπm f Q : π (ι f * Q) = f * π Q := by
      ext n
      induction' n with n ih generalizing f <;> rw [eq_X_mul_shift_add_const f] <;>
        simp_all [π, h.ne', pow_succ, add_mul, mul_assoc, ← algebraMap_eq, ← Algebra.smul_def]
      convert! ih _ using 3
      ext j
      change coeff _ (w.inv * _) = _; simp
    have hu : IsUnit (π 1) := isUnit_iff_constantCoeff.2 isUnit_one
    refine' ⟨fun _ _ h => hu.mul_left_inj.1 _, fun _ _ ⟨Q, h⟩ => hu.dvd_mul_right.1 ⟨π Q, _⟩⟩ <;> simp_all [← hπm],
  weierstrassCompleteness.2,
  by
    intro O _ l φ h
    -- Each iterate carries the original product divisibility to the next link.
    -- Both ideal inclusions follow from transitivity of that one chain.
    have edge n := map_dvd (φ ^ n) h
    simp only [← AlgHom.coe_pow, map_mul, map_add, map_natCast] at *
    have chain := Nat.rel_of_forall_rel_succ_of_le (· ∣ ·) fun n => dvd_of_mul_right_dvd (edge n)
    constructor <;> intros
    case' left s =>
      cases' chain (Nat.zero_le s) with q e
      simp_all
    case' right s t h =>
      rcases lt_or_gt_of_ne h with h|h <;> cases' (dvd_of_mul_left_dvd (edge _)).trans (chain h) with q e <;> simp_all
    all_goals apply subset_span; simp⟩
