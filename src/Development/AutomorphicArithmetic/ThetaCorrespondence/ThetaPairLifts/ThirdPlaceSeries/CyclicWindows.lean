module

public import Development.AutomorphicArithmetic.CharacterBoxes.DyadicWindows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopPlug

@[expose] public section

open Formalism.HC Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc

namespace UpperTheory.Top

local notation "SideHyps" => Nonempty (_root_.GlobalTheory.Fc.HypsAlt
  (fun 𝒞 => Closed 𝒞 fun Fm _ => LinkN Fm) _root_.GlobalTheory.Fc.DefiniteSideCondition)

/-- Any fixed arithmetic power window of width greater than one suffices for the cyclic level. -/
theorem cyclicLevel_of_green_narrow_window (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b w : ℝ) (hb : 797 / 2 < b) (hw : 1 < w) (ψ : PChar)
    (hV : ∃ δ > 0, JointVWinBelowWidth ψ δ w (fun _ x => x ^ b)) : (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨δ, hδ, hV⟩ := hV
  have hwindow : JointVWinBelowWidth ψ δ w (fun _ x => 1 * x ^ b) := by simpa only [one_mul] using hV
  obtain ⟨η, hη, hr⟩ := RankWindowsAtWidth.of_limiting_power (C := fun _ => 1) hδ hb hwindow (by intros; norm_num)
  obtain ⟨la, hla, hlw⟩ := exists_between hw
  exact h.elim fun side => cyclicLevel_zeroFree_of_topG_at ψ hla
    (_root_.GlobalTheory.Fc.forall_goal_of_shape_of_hyps _ _ _ _ (shape_closed_link_n_of_green_at hG)
      trivial trivial side) hη (supplyChi_of_rank_windows_at_width hla hlw ψ hr)

theorem cyclicLevel_of_green_power_window (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b : ℝ) (hb : 797 / 2 < b) (ψ : PChar)
    (hV : ∃ δ > 0, JointVWinBelow ψ δ (fun _ x => x ^ b)) : (Level.cyc ψ).ZeroFreeLevel :=
  cyclicLevel_of_green_narrow_window hG h b 2 hb (by norm_num) ψ hV

/-- A window need not be supplied for each character separately: it suffices
that the cyclic levels of the tested characters cover their primitive parts. -/
theorem every_character_of_green_narrow_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (tested : Set PChar)
    (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0,
      JointVWinBelowWidth ρ δ w (fun _ x => x ^ b)) :
    UpperTheory.EveryCharacter := by
  apply imprimitive
  intro ψ _
  obtain ⟨ρ, hρ, hψ⟩ := cover ψ
  obtain ⟨b, hb, w, hw, δ, hδ, hV⟩ := win ρ hρ
  exact cyclicLevel_of_green_narrow_window hG h b w hb hw ρ ⟨δ, hδ, hV⟩ ψ hψ

theorem every_character_of_green_window_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (b : ℝ) (hb : 797 / 2 < b) (tested : Set PChar)
    (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ δ > 0, JointVWinBelow ρ δ (fun _ x => x ^ b)) :
    UpperTheory.EveryCharacter :=
  every_character_of_green_narrow_cover hG h tested cover fun ρ hρ =>
    ⟨b, hb, 2, by norm_num, win ρ hρ⟩

/-- For a modulus with cyclic unit group, a single character window suffices.
Its primitive part may have smaller conductor than the modulus. -/
theorem one_narrow_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, ∀ (b w : ℝ), 797 / 2 < b → 1 < w →
      (∃ δ > 0, JointVWinBelowWidth (PChar.of ξ) δ w (fun _ x => x ^ b)) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := Level.exists_cyc_keeps_all_of_isCyclic_units (n := N)
  refine ⟨ξ, fun b w hb hw hv hG h χ => ?_⟩
  apply imprimitive_of_primitive χ
  exact cyclicLevel_of_green_narrow_window hG h b w hb hw _ hv (PChar.of χ) (hξ χ)

theorem one_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N, ∀ (b : ℝ), 797 / 2 < b →
      (∃ δ > 0, JointVWinBelow (PChar.of ξ) δ (fun _ x => x ^ b)) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := one_narrow_window_at_cyclic_modulus N
  exact ⟨ξ, fun b hb => hξ b 2 hb (by norm_num)⟩

/-- It suffices to test the finite list of dyadic page boundaries in each retained window. -/
theorem cyclicLevel_of_green_dyadic_window (hG : GlobalTheory.GLq.Green) (h : SideHyps) (ψ : PChar)
    (win : ∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0, DyadicVWinBelowWidth ψ δ w b) :
    (Level.cyc ψ).ZeroFreeLevel := by
  obtain ⟨b, hb, w, hw, δ, hδ, hV⟩ := (has_dyadic_power_window_iff ψ).mp win
  exact cyclicLevel_of_green_narrow_window hG h b w hb hw ψ ⟨δ, hδ, hV⟩

theorem every_character_of_green_dyadic_cover (hG : GlobalTheory.GLq.Green) (h : SideHyps)
    (tested : Set PChar) (cover : ∀ ψ : PChar, ∃ ρ ∈ tested, ψ ∈ (Level.cyc ρ).KEPT)
    (win : ∀ ρ ∈ tested, ∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0, DyadicVWinBelowWidth ρ δ w b) :
    UpperTheory.EveryCharacter :=
  every_character_of_green_narrow_cover hG h tested cover fun ρ hρ =>
    (has_dyadic_power_window_iff ρ).mp (win ρ hρ)

theorem one_dyadic_window_at_cyclic_modulus (N : ℕ) [NeZero N] [IsCyclic (ZMod N)ˣ] :
    ∃ ξ : DirichletCharacter ℂ N,
      (∃ b > (797 / 2 : ℝ), ∃ w > 1, ∃ δ > 0, DyadicVWinBelowWidth (PChar.of ξ) δ w b) →
      GlobalTheory.GLq.Green → SideHyps →
      ∀ (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := one_narrow_window_at_cyclic_modulus N
  refine ⟨ξ, fun win => ?_⟩
  obtain ⟨b, hb, w, hw, δ, hδ, hv⟩ := (has_dyadic_power_window_iff _).mp win
  exact hξ b w hb hw ⟨δ, hδ, hv⟩

end UpperTheory.Top
