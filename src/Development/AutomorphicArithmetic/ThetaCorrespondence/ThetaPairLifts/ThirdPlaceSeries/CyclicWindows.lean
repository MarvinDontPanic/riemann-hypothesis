module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug

@[expose] public section

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

namespace UpperTheory.Top

local notation "SideHyps" => Nonempty (_root_.GlobalTheory.Fc.HypsAlt
  (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)

theorem cyclicLevel_of_green_power_window (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b : ℝ) (hb : 797 / 2 < b) (ψ : PChar)
    (hV : ∃ δ > 0, JointVWinBelow ψ δ (fun _ x => x ^ b)) : (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨δ, hδ, hV⟩ := hV
  have hwindow : JointVWinBelow ψ δ (fun _ x => 1 * x ^ b) := by simpa only [one_mul] using hV
  obtain ⟨η, hη, hr⟩ := RankWindowsAt.of_limiting_power (C := fun _ => 1) hδ hb hwindow (by intros; norm_num)
  exact h.elim fun side => cyclicLevel_zeroFree_of_topG_at (la := 3 / 2) ψ (by norm_num)
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green_at hG)
      trivial trivial side) hη (supplyChi_of_rank_windows_at ψ hr)

/-- A window need not be supplied for each character separately: it suffices
that the cyclic levels of the tested characters cover their primitive parts. -/
theorem every_character_of_green_window_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b : ℝ) (hb : 797 / 2 < b) (tested : Set PChar)
    (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ δ > 0, JointVWinBelow ρ δ (fun _ x => x ^ b)) :
    UpperTheory.EveryCharacter := by
  apply imprimitive
  intro ψ _
  obtain ⟨ρ, hρ, hψ⟩ := cover ψ
  exact cyclicLevel_of_green_power_window hG h b hb ρ (win ρ hρ) ψ hψ

/-- For a modulus with cyclic unit group, a single character window suffices.
Its primitive part may have smaller conductor than the modulus. -/
theorem one_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, ∀ (b : ℝ), 797 / 2 < b →
      (∃ δ > 0, JointVWinBelow (PChar.of ξ) δ (fun _ x => x ^ b)) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := Level.exists_cyc_keeps_all_of_isCyclic_units (n := N)
  refine ⟨ξ, fun b hb hv hG h χ => ?_⟩
  apply imprimitive_of_primitive χ
  exact cyclicLevel_of_green_power_window hG h b hb _ hv (PChar.of χ) (hξ χ)

end UpperTheory.Top
