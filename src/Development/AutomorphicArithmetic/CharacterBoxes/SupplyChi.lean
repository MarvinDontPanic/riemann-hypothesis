module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.DyadicWindows
public import Development.AutomorphicArithmetic.CharacterBoxes.Imports
public import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
public import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

theorem UpperTheory.Top.supplyChi_of_rank_windows_on {P : ℝ → Prop} {w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    ∀ ψ : PChar, RankWindowsOn ψ P w → HostExW la ((GChi ψ).whenEps P).req := by
  intro ψ hψ
  refine UpperTheory.T3.supplyOfAdmOfRankWindowsOn hla hlw hostOfField ψ hψ ?_
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi

theorem UpperTheory.Top.supplyChi_of_rank_windows_at_width {δ w la : ℝ} (hla : 1 < la) (hlw : la < w) :
    ∀ ψ : PChar, RankWindowsAtWidth ψ δ w → HostExW la ((GChi ψ).below δ).req :=
  supplyChi_of_rank_windows_on (P := (· < δ)) hla hlw

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


/-- Windows at arbitrarily small good ε suffice to construct gated hosts on that same set.
Outside it the unconditional prime-pair windows supply the underlying hosts. -/
theorem UpperTheory.Top.exists_coinitial_host_of_dyadic {la w : ℝ} (ψ : PChar)
    (hla : 1 < la) (hlw : la < w)
    (h : ∀ η : ℝ, 0 < η → ∃ eps : ℝ, 0 < eps ∧ eps < η ∧
      ∃ b : ℝ, rankExponent eps < b ∧ DyadicWindowAtWidth ψ eps w b) :
    ∃ P : ℝ → Prop, (∀ η : ℝ, 0 < η → ∃ eps : ℝ, 0 < eps ∧ eps < η ∧ P eps) ∧
      HostExW la ((GChi ψ).whenEps P).req := by
  let P := fun eps => ∃ b : ℝ, rankExponent eps < b ∧ DyadicWindowAtWidth ψ eps w b
  obtain ⟨v, hlv, hvw⟩ := exists_between hlw
  refine ⟨P, h, supplyChi_of_rank_windows_on hla hlv ψ ?_⟩
  let b := fun eps => Classical.epsilon (fun z : ℝ => rankExponent eps < z ∧ DyadicWindowAtWidth ψ eps w z)
  have good (eps : ℝ) (hp : P eps) : rankExponent eps < b eps ∧ DyadicWindowAtWidth ψ eps w (b eps) :=
    Classical.epsilon_spec hp
  apply RankWindowsOn.of_power (C := fun eps => 1 / 2 ^ b eps) (b := b)
  · intro eps he _ hp
    obtain ⟨hgap, hwin⟩ := good eps hp
    exact hwin.toJoint he hvw ((show 0 ≤ rankExponent eps by unfold rankExponent; positivity).trans hgap.le)
  · exact fun eps _ _ hp => ⟨by positivity, (good eps hp).1⟩
