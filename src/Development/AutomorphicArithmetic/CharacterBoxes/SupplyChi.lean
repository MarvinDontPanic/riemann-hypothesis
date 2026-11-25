module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.Imports
public import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
public import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

theorem UpperTheory.Top.supplyChi_of_rank_windows_at_width {δ w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    ∀ ψ : PChar, RankWindowsAtWidth ψ δ w → HostExW la ((GChi ψ).below δ).req := by
  intro ψ hψ
  refine UpperTheory.T3.supplyOfAdmOfRankWindowsAtWidth hla hlw hostOfField ψ hψ ?_
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi

theorem UpperTheory.Top.supplyChi_of_rank_windows_at {δ : ℝ} :
    ∀ ψ : PChar, RankWindowsAt ψ δ → HostExW (3 / 2) ((GChi ψ).below δ).req :=
  supplyChi_of_rank_windows_at_width (w := 2) (la := 3 / 2) (by norm_num) (by norm_num)

theorem UpperTheory.Top.supplyChi_of_cofinal :
    ∀ ψ : PChar, CofinalVWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
  intro ψ hV
  have h : (GChi ψ).below (1 / 52) = GChi ψ := by
    funext s φ H TT t
    exact propext ⟨fun hg => hg s.eps_lt, fun hg _ => hg⟩
  simpa only [h] using supplyChi_of_rank_windows_at ψ hV.rankWindows

theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req :=
  fun ψ hψ => supplyChi_of_cofinal ψ hψ.cofinal
