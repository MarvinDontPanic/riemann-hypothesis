module

public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AutomorphicArithmetic.CharacterBoxes.DivinNOfHypV
public import Development.AutomorphicArithmetic.PrimitiveCosets.LevelGmLeOnFamilyScales
public import Development.AutomorphicArithmetic.PrimitiveCosets.Imports

@[expose] public section

noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.HC GlobalTheory.EX

def TopG : Prop :=
  ∀ (la : ℝ) (G : FReq), 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), G.cls la Fm → HypV Fm.toFamCore) → FamilyClassConnected (G.cls la)

/-- In the zero-free argument the arithmetic bound is used only for sufficiently small ε. -/
def TopGAt : Prop :=
  ∀ (δ la : ℝ) (G : FReq), 0 < δ → 1 < la → HostExW la G.req →
    (∀ {eps : ℝ} (Fm : FamP eps), eps < δ → G.cls la Fm → HypV Fm.toFamCore) →
      FamilyClassConnected (G.cls la)

theorem TopGAt.toTopG (h : TopGAt) : TopG :=
  fun la G hla hH hV => h 1 la G zero_lt_one hla hH (fun Fm _ => hV Fm)

theorem FReq.cls_of_below {G : FReq} {δ eps la : ℝ} {Fm : FamP eps} (he : eps < δ)
    (h : (G.below δ).cls la Fm) : G.cls la Fm := by
  refine ⟨h.1, fun x hx i => h.2 x hx i ?_⟩
  rwa [Fm.L_eps x i]

theorem hypV_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) : HypV Fm.toFamCore :=
  ⟨Fm.x1 + 1, fun x hx i => (h.2 x (by linarith) i).2⟩

theorem eFamC_of_cls (ψ : PChar) (la : ℝ) {eps : ℝ} (Fm : FamP eps) (h : (GChi ψ).cls la Fm) :
    EFamC (Level.cyc ψ) Fm.toFamCore := by
  refine ⟨4, Fm.x1 + 1, fun x hx i => ?_⟩
  have h1 := (h.2 x (by linarith) i).1
  rw [Fm.L_x x i (by linarith), Fm.L_eps x i] at h1
  exact h1

theorem zeroFreeAll_of_topG {la : ℝ} (hla : 1 < la) (h : TopG) (hS : ∀ ψ : PChar, HostExW la (GChi ψ).req) : ZeroFreeAll := by
  have key : ZeroFreeOn fun _ => True :=
    zeroFreeOn_of_tiedWin_cyc (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm) hla
      (fun ψ _ => UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (fun ψ _ => UpperTheory.Comparison₂.formB _) fun ψ _ => by
        obtain ⟨eD, eL, ε₁, h1, h2⟩ := h la (GChi ψ) hla (hS ψ) (hypV_of_cls ψ la)
        refine ⟨eD, eL, ε₁, h1, fun eps a b => ?_⟩
        obtain ⟨Fm, c, d⟩ := h2 eps a b
        exact ⟨Fm, eFamC_of_cls ψ la Fm c, c.1, d⟩
  exact key

theorem cyclicLevel_zeroFree_of_topG_at {la δ : ℝ} (ψ : PChar) (hla : 1 < la) (h : TopGAt)
    (hδ : 0 < δ) (hH : HostExW la ((GChi ψ).below δ).req) : (Level.cyc ψ).ZeroFreeLevel := by
  apply level_of_tiedWin (Fam := FamP) (core := fun Fm => Fm.toFamCore) (Tied := fun Fm => ChainTied Fm)
    (UpperTheory.Comparison₂.level_gm_le_on_family_scales _) (UpperTheory.Comparison₂.formB _ la hla)
  obtain ⟨eD, eL, ε₁, h₁, hF⟩ := h δ la ((GChi ψ).below δ) hδ hla hH
    fun Fm he hFm => hypV_of_cls ψ la Fm (FReq.cls_of_below he hFm)
  refine ⟨eD, eL, min δ ε₁, lt_min hδ h₁, fun eps hp hlt => ?_⟩
  obtain ⟨hle, hlt'⟩ := lt_min_iff.mp hlt
  obtain ⟨Fm, c, d⟩ := hF eps hp hlt'
  exact ⟨Fm, eFamC_of_cls ψ la Fm (FReq.cls_of_below hle c), c.1, d⟩

theorem zeroFreeAll_of_topG_at {la : ℝ} (hla : 1 < la) (h : TopGAt)
    (hS : ∀ ψ : PChar, ∃ δ > 0, HostExW la ((GChi ψ).below δ).req) : ZeroFreeAll := by
  intro ψ _
  obtain ⟨δ, hδ, hH⟩ := hS ψ
  exact cyclicLevel_zeroFree_of_topG_at ψ hla h hδ hH ψ (Level.mem_cyc ψ)

end UpperTheory.Top

end
