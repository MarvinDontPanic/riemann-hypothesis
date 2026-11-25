module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridPrimeTestDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridRootField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridCoefficientField

@[expose] public section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem GridInterpolation
open GlobalTheory.Mem.LiteralAutomorphy.KeyFiniteness
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

/-- A prescribed-field test identifies generators over the original reference's
own field: the roots-of-unity part is already present in every reference. -/
private theorem eq_adjoin_of_value_test {P : Pre} {sc : Consts} (J : GridOver P sc)
    (A : Set ℂ) (htest : ∀ F : IntermediateField ℚ ℂ, J.ValuesIn F →
      (A ⊆ F ↔ ∀ G : GridOver P sc, G.ValuesIn F)) :
    uniformGridField P sc = gridCoefficientField J.grid ⊔ IntermediateField.adjoin ℚ A := by
  let U := uniformGridField P sc
  let F := gridCoefficientField J.grid ⊔ IntermediateField.adjoin ℚ A
  have allU (G : GridOver P sc) : FieldHas G.grid U.val.toRingHom :=
    (uniformGridField_le_iff P sc U).mp le_rfl G.stage G.base_eq G.indexType G.level G.grid
  have refF : FieldHas J.grid F.val.toRingHom := (gridCoefficientField_le_iff J.grid F).mp le_sup_left
  apply le_antisymm
  · have inF : A ⊆ F := Set.Subset.trans (IntermediateField.subset_adjoin ℚ A)
      (show IntermediateField.adjoin ℚ A ≤ F from le_sup_right)
    have vals := (htest F refF.values).mp inF
    apply (uniformGridField_le_iff P sc F).mpr
    intro X hX T L G
    refine (FieldHas.rootField_le_iff F).mpr ⟨vals ⟨X, hX, T, L, G⟩, ?_⟩
    rw [← uniformRootField_eq_of_grid G, hX, ← J.base_eq, uniformRootField_eq_of_grid J.grid]
    exact ((FieldHas.rootField_le_iff F).mp refF).2
  · refine sup_le ((gridCoefficientField_le_iff J.grid U).mpr (allU J)) (IntermediateField.adjoin_le_iff.mpr ?_)
    exact (htest U (allU J).values).mpr fun G => (allU G).values

/-- One fixed list of original ratio columns generates the full uniform coefficient
field over *every* original reference. All columns are read at the same prime.
Every good prime of the chosen ray class works; degree-one representatives exist
outside each prescribed finite set. -/
theorem exists_single_prime_grid_field (Y : Stages) (sc : Consts) :
    ∃ q : Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7,
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧
    (∀ m : ℕ, e ∣ m ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ^ m = 1) ∧
    ∃ menu : Finset (GridRatioColumn Y.B.toPre sc), menu.card ≤ e.primeFactors.card ∧
      (∀ bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E)),
        ∃ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ bad ∧ p ∉ allBad Y.toD7 ∧
          p.asIdeal.inertiaDeg ℤ = 1 ∧
          movingPrimeClass Y.toD7 p = q) ∧
      ∀ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), p ∉ allBad Y.toD7 →
        movingPrimeClass Y.toD7 p = q →
        (∀ (G : GridOver Y.B.toPre sc) (a : Fin Y.B.toPre.R.m), (G.character a).UnrAt p) ∧
        menu.lcm (fun c => orderOf (c.read p)) = e ∧
        ∀ J : GridOver Y.B.toPre sc, uniformGridField Y.B.toPre sc =
          gridCoefficientField J.grid ⊔ IntermediateField.adjoin ℚ ((fun c : GridRatioColumn Y.B.toPre sc => c.read p) '' ↑menu) := by
  obtain ⟨q, e, he, hleast, menu, hc, hprimes, htest⟩ := exists_single_prime_grid_tests_exact Y sc
  refine ⟨q, e, he, hleast, menu, hc, hprimes, fun p hp hq => ?_⟩
  obtain ⟨hu, horder, test⟩ := htest p hp hq
  refine ⟨hu, horder, fun J => eq_adjoin_of_value_test J _ fun F href => ?_⟩
  exact Set.image_subset_iff.trans (test J F href)

#print axioms exists_single_prime_grid_field

/-- A fixed list of original columns generates the full uniform coefficient field
over every reference at every prime of one fixed packet. The displayed density is
that of this packet, not that of all primes at which some test could succeed. -/
theorem exists_totient_density_single_prime_grid_field (Y : Stages) (sc : Consts) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧
      (∀ m : ℕ, e ∣ m ↔ ∀ s : GridRatioSample Y.B.toPre sc, s.value ^ m = 1) ∧
    ∃ menu : Finset (GridRatioColumn Y.B.toPre sc), menu.card ≤ e.primeFactors.card ∧
    ∃ C : Finset (Ideles Y.toD7.host.E ⧸ movingRayGroup Y.toD7),
      (e.totient : ℝ) / e ≤ (C.card : ℝ) / (movingRayGroup Y.toD7).index ∧
      (∀ p : HeightOneSpectrum (𝓞 Y.toD7.host.E), movingPrimeClass Y.toD7 p ∈ C ↔
        menu.lcm (fun c => orderOf (c.read p)) = e) ∧
      ∀ bad : Finset (HeightOneSpectrum (𝓞 Y.toD7.host.E)),
        let P := {p : HeightOneSpectrum (𝓞 Y.toD7.host.E) | movingPrimeClass Y.toD7 p ∈ C ∧
          p ∉ bad ∧ p ∉ allBad Y.toD7 ∧ p.asIdeal.inertiaDeg ℤ = 1}
        P.HasDirichletDensity (C.card / (movingRayGroup Y.toD7).index) ∧
        ∀ p ∈ P, (∀ (G : GridOver Y.B.toPre sc) (a : Fin Y.B.toPre.R.m),
          (G.character a).UnrAt p) ∧ menu.lcm (fun c => orderOf (c.read p)) = e ∧
          ∀ J : GridOver Y.B.toPre sc, uniformGridField Y.B.toPre sc =
            gridCoefficientField J.grid ⊔ IntermediateField.adjoin ℚ
              ((fun c : GridRatioColumn Y.B.toPre sc => c.read p) '' ↑menu) := by
  obtain ⟨e, he, hleast, menu, hc, C, hbound, hpacket, htest⟩ := exists_totient_density_single_prime_grid_tests Y sc
  refine ⟨e, he, hleast, menu, hc, C, hbound, hpacket, fun bad => ⟨(htest bad).1, fun p hp => ?_⟩⟩
  obtain ⟨hu, horder, test⟩ := (htest bad).2 p hp
  refine ⟨hu, horder, fun J => eq_adjoin_of_value_test J _ fun F href => ?_⟩
  exact Set.image_subset_iff.trans (test J F href)

#print axioms exists_totient_density_single_prime_grid_field

end GlobalTheory.GridField
end
