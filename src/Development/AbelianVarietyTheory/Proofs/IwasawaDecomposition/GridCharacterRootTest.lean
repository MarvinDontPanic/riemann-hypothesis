module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridValuesFromOneReference

@[expose] public section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GridInterpolation

/-- A family of bounded roots of unity imposes exactly the field-containment test
for one primitive root, of order dividing the bound. -/
private theorem primitiveRoot_mem_iff_subset {R : ℕ} (hR : R ≠ 0) (S : Set ℂ)
    (hS : ∀ z ∈ S, z ^ R = 1) :
    ∃ e : ℕ, e ∣ R ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      ∀ M : IntermediateField ℚ ℂ, (ζ ∈ M ↔ S ⊆ M) := by
  let : NeZero R := ⟨hR⟩
  let A : Set (rootsOfUnity R ℂ) := {x | ((x : ℂˣ) : ℂ) ∈ S}
  let H := Subgroup.closure A
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  let ζ : ℂ := ((g.val : ℂˣ) : ℂ)
  have hz : ζ ^ R = 1 := (mem_rootsOfUnity' R _).mp g.val.property
  refine ⟨orderOf ζ, orderOf_dvd_of_pow_eq_one hz, ζ, IsPrimitiveRoot.orderOf _, ?_⟩
  intro M
  constructor
  · intro hζ z hzS
    let x := rootsOfUnity.mkOfPowEq z (hS z hzS)
    have hx : x ∈ A := hzS
    let y : H := ⟨x, Subgroup.subset_closure hx⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
    have heq := congrArg (fun t : H => ((t.val : ℂˣ) : ℂ)) hk
    have e : ζ ^ k = z := by
      simpa only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, ζ, y, x,
        rootsOfUnity.coe_mkOfPowEq] using heq
    exact e ▸ M.toSubfield.zpow_mem hζ k
  · intro h
    have Hmem (x : rootsOfUnity R ℂ) (hx : x ∈ H) : ((x : ℂˣ) : ℂ) ∈ M := by
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact h hx
      | one => exact M.one_mem
      | mul x y _ _ hx hy => exact M.mul_mem hx hy
      | inv x _ hx => simpa only [Subgroup.coe_inv, Units.val_inv_eq_inv_val] using M.inv_mem hx
    exact Hmem g.val g.property


private abbrev GridValues {X : Stages} {T : Type} {L : LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) (F : IntermediateField ℚ ℂ) :=
  ∀ i, 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 F.val.toRingHom

private theorem all_place_mem {X : Stages} {T : Type} {L : LevCh X.toD7 T} {sc : Consts}
    (G : GridData L sc) (F : IntermediateField ℚ ℂ) (h : GridValues G F)
    (a : Fin X.toD7.R.m) (p) : ((G.ch.chiH (a.val+1)).val p : ℂ) ∈ F :=
  local_mem_of_values ((lamOf G).chi a) F (h _ (by omega) a.isLt)
    (embPsi _) ((lamOf G).c a) (lamOf_hasInfQ G a) p (atFin p (unif p))

/-- For a pair of grids the missing generators are the pointwise ratios, taken at
the same weights and finite places after identifying their base data. -/
private theorem exists_ratio_set {X Y : Stages} {T U : Type} {L : LevCh X.toD7 T} {L₀ : LevCh Y.toD7 U}
    {sc : Consts} (G : GridData L sc) (G₀ : GridData L₀ sc) (hP : X.B.toPre = Y.B.toPre) :
    ∃ S : Set ℂ, (∀ z ∈ S, z ^ movingRayExponent Y.toD7 = 1) ∧
      ∀ F : IntermediateField ℚ ℂ, GridValues G₀ F → (S ⊆ F ↔ GridValues G F) := by
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at hP
  subst Q
  let x (a : Fin P.R.m) (p) : ℂ := (G.ch.chiH (a.val + 1)).val p
  let y (a : Fin P.R.m) (p) : ℂ := (G₀.ch.chiH (a.val + 1)).val p
  let S := {z : ℂ | ∃ a p, x a p / y a p = z}
  refine ⟨S, ?_, fun F href => ⟨?_, ?_⟩⟩
  · rintro _ ⟨a, p, rfl⟩
    exact moving_ratio_pow G.pl.basePlace_over_qZero G₀.pl.basePlace_over_qZero
      (actual_specs G a) (actual_specs G₀ a) p
  · intro h i hi hm p _
    change i ≤ P.R.m at hm
    obtain ⟨a, rfl⟩ : ∃ a : Fin P.R.m, i = a.val + 1 := ⟨⟨i-1,by omega⟩,by simp; omega⟩
    have hr := h (show x a p / y a p ∈ S from ⟨a,p,rfl⟩)
    have hx : x a p ∈ F := by simpa [x,y] using F.mul_mem hr (all_place_mem G₀ F href a p)
    refine ⟨⟨_, hx⟩, ?_⟩
    simp [HChar.valTw, x]
  · rintro h _ ⟨a,p,rfl⟩
    exact F.div_mem (all_place_mem G F h a p) (all_place_mem G₀ F href a p)

private theorem movingRayExponent_eq_of_same_pre {X Y : Stages} (h : X.B.toPre = Y.B.toPre) :
    movingRayExponent X.toD7 = movingRayExponent Y.toD7 := by
  obtain ⟨⟨P⟩, _, _, _, _, _, _⟩ := X
  obtain ⟨⟨Q⟩, _, _, _, _, _, _⟩ := Y
  change P = Q at h
  subst Q
  rfl

/-- A single root of unity tests all original grids at these base data and parameters.
The root is chosen before the reference grid and the prescribed field. For a field already containing
the reference's unramified values, membership of the root is equivalent to containing
every grid's unramified values. Its order divides the common ray
exponent; this need not be the least possible conductor. -/
theorem exists_root_iff_all_grid_values_uniform (Y : Stages) (sc : Consts) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      ∀ (Z : Stages), Z.B.toPre = Y.B.toPre → ∀ (V : Type) (H : LevCh Z.toD7 V)
        (G₀ : GridData H sc) (F : IntermediateField ℚ ℂ),
        (∀ i, 1 ≤ i → i ≤ Z.toD7.R.m → (G₀.ch.chiH i).ValuesIn 0 F.val.toRingHom) →
        (ζ ∈ F ↔ ∀ (X : Stages), X.B.toPre = Y.B.toPre → ∀ (T : Type) (L : LevCh X.toD7 T)
          (G : GridData L sc) (i : ℕ), 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 F.val.toRingHom) := by
  choose S horder htest using fun (X : Stages) (hX : X.B.toPre = Y.B.toPre) (T : Type)
      (L : LevCh X.toD7 T) (G : GridData L sc) (Z : Stages) (hZ : Z.B.toPre = Y.B.toPre) (V : Type)
      (H : LevCh Z.toD7 V) (J : GridData H sc) => exists_ratio_set G J (hX.trans hZ.symm)
  let A := {z : ℂ | ∃ (X : Stages) (hX : X.B.toPre = Y.B.toPre) (T : Type) (L : LevCh X.toD7 T)
    (G : GridData L sc) (Z : Stages) (hZ : Z.B.toPre = Y.B.toPre) (V : Type) (H : LevCh Z.toD7 V)
    (J : GridData H sc), z ∈ S X hX T L G Z hZ V H J}
  have hA : ∀ z ∈ A, z ^ movingRayExponent Y.toD7 = 1 := by
    rintro z ⟨X, hX, T, L, G, Z, hZ, V, H, J, hz⟩
    rw [← movingRayExponent_eq_of_same_pre hZ]
    exact horder X hX T L G Z hZ V H J z hz
  obtain ⟨e, he, ζ, hζ, hf⟩ := primitiveRoot_mem_iff_subset (NeZero.ne _) A hA
  refine ⟨e, he, ζ, hζ, fun Z hZ V H J F href => (hf F).trans ⟨?_, ?_⟩⟩
  · intro h X hX T L G
    exact (htest X hX T L G Z hZ V H J F href).mp fun _ hz => h ⟨X, hX, T, L, G, Z, hZ, V, H, J, hz⟩
  · rintro h _ ⟨X, hX, T, L, G, W, hW, A, N, I, hz⟩
    exact (htest X hX T L G W hW A N I F (h W hW A N I)).mpr (h X hX T L G) hz

/-- Specialize the uniform test to a given original reference grid. -/
theorem exists_root_iff_all_grid_values {Y : Stages} {U : Type} {L₀ : LevCh Y.toD7 U} {sc : Consts}
    (G₀ : GridData L₀ sc) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      ∀ F : IntermediateField ℚ ℂ,
        (∀ i, 1 ≤ i → i ≤ Y.toD7.R.m → (G₀.ch.chiH i).ValuesIn 0 F.val.toRingHom) →
        (ζ ∈ F ↔ ∀ (X : Stages), X.B.toPre = Y.B.toPre → ∀ (T : Type) (L : LevCh X.toD7 T)
          (G : GridData L sc) (i : ℕ), 1 ≤ i → i ≤ X.toD7.R.m → (G.ch.chiH i).ValuesIn 0 F.val.toRingHom) := by
  obtain ⟨e, he, ζ, hζ, h⟩ := exists_root_iff_all_grid_values_uniform Y sc
  exact ⟨e, he, ζ, hζ, h Y rfl U L₀ G₀⟩

end GridInterpolation
