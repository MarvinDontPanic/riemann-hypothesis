import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition

-- Original theorem and formalization: Levent Alpöge. Adapted from Fortytwo /
-- Vladyslav Larin’s Core 36 proof at vlarin/riemann-hypothesis@a77fbba030230e2c8a7edb1429ccbafcf47f7b17,
-- which credits Vincent Liu and Mikko Nyman. The signed-root argument, span
-- inclusions and cancellation steps come from that proof. This version uses
-- closure under natural multiples (nsmul_mem) directly in all three goals.


open NumberField GlobalTheory CompanionTheory.Ar.Fl Submodule Set Sum PureType SetLike Function

local notation "𝒮" f:80 => span (𝓞 ‹Type›) $ range f

theorem AlpogeRHCore36.pureFamilyDecomposition
    E [Field E] [NumberField E] [IsCMField E]
    H D g ty P hP p q x (n : ℕ) :
    @IsPure E _ _ _ H D g ty P hP p q x → (∀ y, n • y ∈ 𝒮 x) →

    (∀ y, ∃ a ∈ lat hP $ sgnRt H true, ∃ b ∈ lat hP $ sgnRt H false, n • y = a + b) ∧
    (∀ y ∈ lat hP $ sgnRt H true, n • y ∈ 𝒮 x ∘ inl) ∧
    ∀ y ∈ lat hP $ sgnRt H false, n • y ∈ 𝒮 x ∘ inr := by

  rintro ⟨hp, hm⟩ hn
  have := disjoint_lat hP (show H.rt0 ≠ -H.rt0 by grind [H.sqrt_neg_disc_sq, H.d_mod, Nat.cast_eq_zero])

  simp [← mem_coe, ← range_subset_iff, ← span_le] at hp hm
  simp_all [disjoint_def, range_eq, mem_sup, SetLike.le_def, comp_def]

  and_intros <;> intro y <;> grind [hn y, sgnRt, nsmul_mem, add_mem_cancel_left, add_mem_cancel_right]
