module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.Imports
public import Development.AutomorphicArithmetic.CharacterBoxes.HostOfField
public import Development.AutomorphicArithmetic.CoprimeRanks.AdmChi

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX UpperTheory.Top

theorem UpperTheory.Top.supplyChi_of_cofinal :
    ∀ ψ : PChar, CofinalVWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req := by
  intro ψ hψ
  refine UpperTheory.T3.supplyOfAdmOfCofinal hostOfField ψ hψ ?_
  intro eps he0 he1
  obtain ⟨x0, hx0⟩ := admissibleClassesTwistedChar eps he0 he1
  refine ⟨x0, fun s φ H0 hs hx hlo hhi _ _ => ?_⟩
  subst hs
  exact hx0 s φ H0 rfl hx hlo hhi

theorem UpperTheory.Top.supplyChi :
    ∀ ψ : PChar, VWinAt ψ 401 → HostExW (3 / 2) (GChi ψ).req :=
  fun ψ hψ => supplyChi_of_cofinal ψ hψ.cofinal
