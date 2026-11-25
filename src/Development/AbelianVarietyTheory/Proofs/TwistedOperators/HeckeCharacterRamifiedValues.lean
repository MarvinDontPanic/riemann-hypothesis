module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeValueInterpolation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterFiniteOrderValuesInField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterFiniteIdeleValueMemField

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.GridField
variable {E : Type} [Field E] [NumberField E]

/-- A single positive rational integer clears the denominator and every finite level. -/
theorem exists_ray_sample_step (b : E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (m : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 E)), v ∈ S →
      v.valuation E ((t : E) * M * b) ≤ WithZero.exp (-((m v : ℤ) + 1)) := by
  classical
  have hb : IsAlgebraic ℤ b := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ b)
  obtain ⟨d, a, hd, ha⟩ := hb.exists_nsmul_eq (𝓞 E)
  rw [nsmul_eq_mul, ← RingOfIntegers.coe_eq_algebraMap] at ha
  let J := ∏ v ∈ S, v.asIdeal ^ (m v + 1)
  have hJ : J ≠ ⊥ := Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  refine ⟨d * J.absNorm, Nat.mul_pos (Nat.pos_of_ne_zero hd)
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)), ?_⟩
  intro t v hv
  have hle : J ≤ v.asIdeal ^ (m v + 1) := Ideal.prod_le_inf.trans (Finset.inf_le hv)
  have hmem := (v.asIdeal ^ (m v + 1)).mul_mem_left ((t : 𝓞 E) * a) (hle J.absNorm_mem)
  have heq : (t : E) * (d * J.absNorm : ℕ) * b =
      algebraMap (𝓞 E) E ((t * a) * (J.absNorm : 𝓞 E)) := by
    calc
      _ = (t : E) * (d * b) * J.absNorm := by push_cast; ring
      _ = _ := by rw [ha]; push_cast; rfl
  rw [heq, v.valuation_of_algebraMap]
  simpa using (v.intValuation_le_pow_iff_mem _ _).mpr hmem

/-- At most one integral sample is excluded when turning these elements into units. -/
theorem ray_samples_nonzero {b : E} (M : ℕ) :
    {t : ℕ | 1 + (t : E) * M * b = 0}.Subsingleton := by
  by_cases h : (M : E) * b = 0
  · simp [mul_assoc, h]
  · intro t _ s _
    rename_i ht hs
    change 1 + (t : E) * M * b = 0 at ht
    change 1 + (s : E) * M * b = 0 at hs
    rw [mul_assoc] at ht hs
    exact_mod_cast mul_right_cancel₀ h (add_left_cancel (ht.trans hs.symm))

open Formalism.L2.Host
open HeckeCharacterValueBounds.GlobalTheory.CompanionTheory.CharValues

/-- For a character whose ordinary unramified values lie in the field, the
infinity part of every nonzero rational ray sample also lies in the field. -/
theorem exists_ray_samples_inf_mem (χ : HChar E) {C : Type} [Field C] (e : C →+* ℂ)
    (hval : χ.ValuesIn 0 e) (k : E) :
    ∃ M : ℕ, 0 < M ∧ ∀ (t : ℕ) (hu : 1 + (t : E) * M * (k - 1) ≠ 0),
      (χ.inf (Units.mk0 _ hu) : ℂ) ∈ e.fieldRange := by
  classical
  let S := (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset
  have hunr (v) (hv : v ∉ S) : χ.UnrAt v := by simpa [S] using hv
  choose m hm using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  obtain ⟨M, hM, hstep⟩ := exists_ray_sample_step (k-1) S m
  refine ⟨M, hM, fun t hu => ?_⟩
  let u := Units.mk0 _ hu
  have hloc (v) (hv : v ∈ S) : χ.locK v u = 1 := by
    have h := hstep t v hv
    have heq := locK_eq_of_level χ (hm v) 1 u
    apply (heq ?_).trans (map_one _)
    simpa [u] using h
  let H := GlobalTheory.TameVal.unitsIn e.fieldRange
  have hval' (v) (hv : v ∉ S) : χ.val v ∈ H := by
    obtain ⟨y, hy⟩ := hval v (hunr v hv)
    exact RingHom.mem_fieldRange.mpr ⟨y, by simpa [HChar.valTw] using hy⟩
  have hprod : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v u) ∈ H :=
    finprod_induction (· ∈ H) H.one_mem (fun _ _ => H.mul_mem) fun v =>
      finprod_induction (· ∈ H) H.one_mem (fun _ _ => H.mul_mem) fun hv =>
        H.zpow_mem (hval' v hv) _
  have hpr := GlobalTheory.TypeValues.productRule χ S hunr u
  rw [Finset.prod_eq_one hloc, mul_one] at hpr
  exact (H.mul_mem_cancel_right hprod).mp (hpr ▸ H.one_mem)

end GlobalTheory.GridField

open Formalism.L2.Host

namespace GlobalTheory.RelativeGrid

theorem hasInfQ_rational_line {L : Type} [Field L] [NumberField L] {I : Type} [Fintype I]
    {χ : HChar L} (φ : I → L →+* ℂ) (b : I → ℤ)
    (hinf : χ.HasInfQ φ (fun i => (b i : ℚ))) (k : Lˣ) {M : ℕ} (hM : M ≠ 0) :
    RationalArchLine (fun u => (χ.inf u : ℂ)) k M (∑ i, (b i).natAbs) := by
  obtain ⟨n, hn, hphase⟩ := hinf
  have h : n = (fun i => 2*b i) := funext fun i => by
    have hi : (n i : ℚ) = 2*(b i : ℚ) := hn i
    exact_mod_cast hi
  subst n
  exact rationalArchLine_of_even_phase φ b _ hphase k hM

end GlobalTheory.RelativeGrid

open GlobalTheory.RelativeGrid GlobalTheory.GridField Polynomial

namespace GridInterpolation

private theorem line_values_mem (F : IntermediateField ℚ ℂ) (P Q : ℂ[X]) (s : Set ℕ)
    (hs : s.Infinite) (h : ∀ n ∈ s, Q.eval (n : ℂ) ≠ 0 ∧ P.eval (n : ℂ) / Q.eval (n : ℂ) ∈ F)
    (x : ℚ) (hx : Q.eval (x : ℂ) ≠ 0) : P.eval (x : ℂ) / Q.eval (x : ℂ) ∈ F := by
  let pts := (fun n : ℕ => (n : F)) '' s
  have hinf : pts.Infinite := hs.image Nat.cast_injective.injOn
  have hh (a : F) (ha : a ∈ pts) :
      ∃ c : F, P.eval (algebraMap F ℂ a) = c • Q.eval (algebraMap F ℂ a) := by
    obtain ⟨n, hn, rfl⟩ := ha
    obtain ⟨hq, hf⟩ := h n hn
    refine ⟨⟨_,hf⟩, ?_⟩
    rw [Algebra.smul_def]
    change P.eval ((n : F) : ℂ) = (P.eval (n : ℂ) / Q.eval (n : ℂ)) * Q.eval ((n : F) : ℂ)
    simpa using (div_mul_cancel₀ (P.eval (n : ℂ)) hq).symm
  obtain ⟨c, hc⟩ := value_descends P Q pts hinf hh (x : F) (by simpa using hx)
  have he : P.eval (x : ℂ) / Q.eval (x : ℂ) = (c : ℂ) := by simpa using hc
  exact he ▸ c.property

/-- For even phase weights, the infinity character on principal elements of the number
field takes values in the prescribed field of its unramified uniformizer values. -/
theorem infinity_mem_of_values {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (hval : χ.ValuesIn 0 F.val.toRingHom)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (k : Eˣ) : (χ.inf k : ℂ) ∈ F := by
  obtain ⟨M, hM, hm⟩ := exists_ray_samples_inf_mem χ F.val.toRingHom hval (k:E)
  obtain ⟨P,Q,_,_,hline,_,hQ,hk⟩ := hasInfQ_rational_line φ b hi k hM.ne'
  let S := {t : ℕ | 1 + (t : E) * M * ((k : E) - 1) ≠ 0}
  have hS : S.Infinite :=
    (ray_samples_nonzero (b := (k:E)-1) M).finite.infinite_compl
  dsimp only at hk
  rw [hk]
  have ht (n : ℕ) (hn : n ∈ S) : Q.eval (n : ℂ) ≠ 0 ∧ P.eval (n : ℂ) / Q.eval (n : ℂ) ∈ F := by
    let u := Units.mk0 _ hn
    obtain ⟨_, hq, he⟩ := hline (n : ℚ) u (by simp [u,mul_assoc])
    have hu : (χ.inf u : ℂ) ∈ F := by
      obtain ⟨y,hy⟩ := RingHom.mem_fieldRange.mp (hm n hn)
      exact hy ▸ y.property
    simp only [Rat.cast_natCast] at hq he
    exact ⟨hq, he ▸ hu⟩
  simpa using line_values_mem F P Q S hS ht (M:ℚ)⁻¹ (by simpa using hQ)

/-- All finite local values, including those at ramified places, lie in the prescribed field. -/
theorem local_mem_of_values {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (hval : χ.ValuesIn 0 F.val.toRingHom)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (v : HeightOneSpectrum (𝓞 E)) (y : (v.adicCompletion E)ˣ) : (χ.loc v y : ℂ) ∈ F :=
  GlobalTheory.HeckeValField.loc_mem χ (GlobalTheory.Mem.Fld.valueField_le_iff.mpr hval)
    (infinity_mem_of_values χ F hval φ b hi) v y

/-- The same field contains each idèle value with trivial archimedean component. -/
theorem finite_idele_mem_of_values {E : Type} [Field E] [NumberField E] (χ : HChar E)
    (F : IntermediateField ℚ ℂ) (hval : χ.ValuesIn 0 F.val.toRingHom)
    {I : Type} [Fintype I] (φ : I → E →+* ℂ) (b : I → ℤ) (hi : χ.HasInfQ φ (fun i => (b i : ℚ)))
    (x : (AdeleRing (𝓞 E) E)ˣ) (hx : ∀ w : InfinitePlace E, x.val.1 w = 1) :
    ((χ.1 x : ℂˣ) : ℂ) ∈ F :=
  GlobalTheory.HeckeValField.mem_of_inf_eq_one E χ F (GlobalTheory.Mem.Fld.valueField_le_iff.mpr hval)
    (infinity_mem_of_values χ F hval φ b hi) x hx

end GridInterpolation
