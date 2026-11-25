module
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridRootField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridCoefficientField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridTestFamily
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharacterRamifiedValues

@[expose] public section
namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A finite compositum can be tested with actual members of an arbitrary set of scalars,
one per remaining prime factor (with multiplicity) of its degree. -/
theorem exists_scalar_samples_of_degree (B : IntermediateField F L) (S : Set L)
    [FiniteDimensional F ↥(B ⊔ adjoin F S)] :
    ∃ t : Finset L, ↑t ⊆ S ∧ B ⊔ adjoin F (t : Set L) = B ⊔ adjoin F S ∧
      t.card + (Module.finrank F B).primeFactorsList.length ≤
        (Module.finrank F ↥(B ⊔ adjoin F S)).primeFactorsList.length := by
  classical
  let A := adjoin F S
  have hle : A ≤ B ⊔ A := le_sup_right
  have hA : FiniteDimensional F A := FiniteDimensional.of_injective
    (inclusion hle).toLinearMap (inclusion hle).injective
  have hcompact : IsCompactElement A := by
    obtain ⟨s, hs⟩ := A.fg_of_fg_toSubalgebra
      (Subalgebra.fg_of_fg_toSubmodule (Module.Finite.iff_fg.mp hA))
    exact hs ▸ adjoin_finset_isCompactElement s
  let simple (x : S) := adjoin F ({(x : L)} : Set L)
  have hAeq : (⨆ x : S, simple x) = A := by
    dsimp only [A, simple]
    rw [← biSup_adjoin_simple, ← iSup_subtype'']
  obtain ⟨c, hc⟩ := hcompact.exists_finset_of_le_iSup simple hAeq.ge
  let fields := c.image simple
  have hsup : fields.sup id = A := by
    rw [show fields.sup id = c.sup simple by simp [fields, Finset.sup_image]]
    rw [Finset.sup_eq_iSup]
    exact le_antisymm (iSup_le fun x => iSup_le fun _ => hAeq ▸ le_iSup simple x) hc
  obtain ⟨u, hu, heu, hcount⟩ := exists_subfamily_sup_of_degree B fields
    (by rw [hsup]; infer_instance)
  have hreps (C : u) : ∃ x : S, simple x = C.val := by
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (hu C.property)
    exact ⟨x, hx⟩
  choose rep hrep using hreps
  let t := u.attach.image (fun C => (rep C : L))
  have ht : (t : Set L) ⊆ S := by
    rintro _ hx
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hx
    exact (rep C).property
  have heq : adjoin F (t : Set L) = u.sup id := by
    apply le_antisymm
    · apply adjoin_le_iff.mpr
      rintro _ hx
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hx
      apply (Finset.le_sup (f := id) C.property)
      change (rep C : L) ∈ C.val
      rw [← hrep C]
      exact mem_adjoin_simple_self F _
    · apply Finset.sup_le
      intro C hC
      change C ≤ _
      have hr : simple (rep ⟨C, hC⟩) = C := hrep _
      rw [← hr]
      apply adjoin_simple_le_iff.mpr
      exact subset_adjoin F _ (Finset.mem_image_of_mem _ (Finset.mem_attach _ _))
  refine ⟨t, ht, by rw [heq, heu, hsup], ?_⟩
  have hcard : t.card ≤ u.card := Finset.card_image_le.trans_eq Finset.card_attach
  rw [hsup] at hcount
  exact (Nat.add_le_add_right hcard _).trans hcount

end IntermediateField

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem GridInterpolation
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

/-- Values of actual original-grid characters at unramified primes, outside
a finite set assigned to each stage. No reference grid has to be chosen. -/
def goodGridReadings (P : Pre) (sc : Consts)
    (avoid : (X : Stages) → Finset (HeightOneSpectrum (𝓞 X.toD7.host.E))) : Set ℂ :=
  {z | ∃ (X : Stages), X.B.toPre = P ∧ ∃ (T : Type) (L : LevCh X.toD7 T)
    (G : GridData L sc) (a : Fin X.toD7.R.m) (p : HeightOneSpectrum (𝓞 X.toD7.host.E)),
    p ∉ avoid X ∧ ((lamOf G).chi a).UnrAt p ∧ (((lamOf G).chi a).val p : ℂ) = z}

/-- The roots required by the grids and the remaining genuine prime readings
generate exactly the full uniform field. This includes the empty family. -/
theorem uniform_eq_root_sup_good_readings (P : Pre) (sc : Consts)
    (avoid : (X : Stages) → Finset (HeightOneSpectrum (𝓞 X.toD7.host.E))) :
    uniformGridField P sc = uniformRootField P sc ⊔ IntermediateField.adjoin ℚ (goodGridReadings P sc avoid) := by
  let U := uniformGridField P sc
  let M := uniformRootField P sc ⊔ IntermediateField.adjoin ℚ (goodGridReadings P sc avoid)
  have allU := (uniformGridField_le_iff P sc U).mp le_rfl
  apply le_antisymm
  · apply (uniformGridField_le_iff P sc M).mpr
    intro X hX T L G
    apply (FieldHas.rootField_le_iff M).mpr
    constructor
    · intro i h1 hm
      obtain ⟨a, rfl⟩ : ∃ a : Fin X.toD7.R.m, i = a.val + 1 := ⟨⟨i-1,by omega⟩,by simp; omega⟩
      apply (valuesIn_iff_good_off ((lamOf G).chi a) M (embPsi _) ((lamOf G).c a)
        (lamOf_hasInfQ G a) (avoid X)).mpr
      intro p hp hu
      have h : (((lamOf G).chi a).val p : ℂ) ∈ goodGridReadings P sc avoid :=
        ⟨X, hX, T, L, G, a, p, hp, hu, rfl⟩
      exact (show IntermediateField.adjoin ℚ (goodGridReadings P sc avoid) ≤ M from le_sup_right)
        (IntermediateField.subset_adjoin ℚ _ h)
    · rw [← uniformRootField_eq_of_grid G, hX]
      exact le_sup_left
  · apply sup_le
    · exact (uniformRootField_le_iff P sc U).mpr fun X hX T L G => (allU X hX T L G).roots
    · apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨X, hX, T, L, G, a, p, _, hu, rfl⟩
      have v := (allU X hX T L G).values (a.val+1) (by omega) a.isLt
      exact GlobalTheory.HeckeValField.val_mem ((lamOf G).chi a) (GlobalTheory.Mem.Fld.valueField_le_iff.mpr v) hu

/-- A bounded finite sample of *actual unramified readings*, together with the
required roots, suffices to recover the uniform field, with no reference field
assumed known. The prime-factor count is with multiplicity. -/
theorem exists_good_grid_readings (P : Pre) (sc : Consts)
    (avoid : (X : Stages) → Finset (HeightOneSpectrum (𝓞 X.toD7.host.E))) :
    ∃ t : Finset ℂ, (t : Set ℂ) ⊆ goodGridReadings P sc avoid ∧
      uniformGridField P sc = uniformRootField P sc ⊔ IntermediateField.adjoin ℚ (t : Set ℂ) ∧
      t.card + (Module.finrank ℚ (uniformRootField P sc)).primeFactorsList.length ≤
        (Module.finrank ℚ (uniformGridField P sc)).primeFactorsList.length := by
  have eqn := uniform_eq_root_sup_good_readings P sc avoid
  have : FiniteDimensional ℚ ↥(uniformRootField P sc ⊔
      IntermediateField.adjoin ℚ (goodGridReadings P sc avoid)) := eqn ▸ inferInstance
  obtain ⟨t, ht, he, hn⟩ := IntermediateField.exists_scalar_samples_of_degree
    (uniformRootField P sc) (goodGridReadings P sc avoid)
  exact ⟨t, ht, eqn.trans he.symm, eqn.symm ▸ hn⟩

/-- In prime relative degree, one original good-prime reading generates the
entire uniform field over the required roots, outside any finite exclusions. -/
theorem exists_good_reading_of_prime_relative_degree (P : Pre) (sc : Consts)
    (avoid : (X : Stages) → Finset (HeightOneSpectrum (𝓞 X.toD7.host.E)))
    {q : ℕ} (hq : q.Prime)
    (hdeg : Module.finrank ℚ (uniformGridField P sc) =
      Module.finrank ℚ (uniformRootField P sc) * q) :
    ∃ z ∈ goodGridReadings P sc avoid,
      uniformGridField P sc = uniformRootField P sc ⊔ IntermediateField.adjoin ℚ {z} := by
  obtain ⟨t, ht, he, hn⟩ := exists_good_grid_readings P sc avoid
  have hU : Module.finrank ℚ (uniformGridField P sc) ≠ 0 := Module.finrank_pos.ne'
  have hB : Module.finrank ℚ (uniformRootField P sc) ≠ 0 := by
    intro h
    exact hU (by simp [hdeg, h])
  have hbound : t.card ≤ 1 := by
    rw [hdeg, (Nat.perm_primeFactorsList_mul hB hq.ne_zero).length_eq,
      Nat.primeFactorsList_prime hq, List.length_append] at hn
    simpa using (show t.card ≤ [q].length by omega)
  have hpos : 0 < t.card := by
    by_contra! h
    have hem : t = ∅ := Finset.card_eq_zero.mp (by omega)
    have e : uniformGridField P sc = uniformRootField P sc := by simpa [hem] using he
    have hlt : Module.finrank ℚ (uniformRootField P sc) * 1 <
        Module.finrank ℚ (uniformRootField P sc) * q :=
      Nat.mul_lt_mul_of_pos_left hq.one_lt (Nat.pos_of_ne_zero hB)
    rw [e] at hdeg
    omega
  obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp (show t.card = 1 by omega)
  exact ⟨z, ht (by simp), by simpa using he⟩

end GlobalTheory.GridField
