module
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridCharacterRootTest
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridRootField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformGridCoefficientField

@[expose] public section
open Formalism.BasicNotions Formalism.IndefR.Links Formalism.L2.Host
open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun GlobalTheory.Mem GridInterpolation
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridField

/-- One primitive root works over every original reference grid at this base and
scale, and its order divides the exponent (hence the order) of the finite ray quotient. -/
theorem every_grid_field (Y : Stages) (sc : Consts) :
    ∃ e : ℕ, e ∣ movingRayExponent Y.toD7 ∧ ∃ ζ : ℂ, IsPrimitiveRoot ζ e ∧
      ∀ (Z : Stages), Z.B.toPre = Y.B.toPre → ∀ (T : Type) (L : LevCh Z.toD7 T) (J : GridData L sc),
        uniformGridField Y.B.toPre sc = gridCoefficientField J ⊔ IntermediateField.adjoin ℚ {ζ} := by
  obtain ⟨e, he, ζ, hζ, test⟩ := exists_root_iff_all_grid_values_uniform Y sc
  refine ⟨e, he, ζ, hζ, fun Z hZ T L J => ?_⟩
  let U := uniformGridField Y.B.toPre sc
  let F := gridCoefficientField J ⊔ IntermediateField.adjoin ℚ {ζ}
  have allU := (uniformGridField_le_iff Y.B.toPre sc U).mp le_rfl
  have refF : FieldHas J F.val.toRingHom := (gridCoefficientField_le_iff J F).mp le_sup_left
  have inc : gridCoefficientField J ≤ U := (gridCoefficientField_le_iff J U).mpr (allU Z hZ T L J)
  apply le_antisymm
  · have hζF : ζ ∈ F := (show IntermediateField.adjoin ℚ {ζ} ≤ F from le_sup_right)
      (IntermediateField.subset_adjoin ℚ {ζ} (Set.mem_singleton ζ))
    have vals := (test Z hZ T L J F refF.values).mp hζF
    apply (uniformGridField_le_iff _ _ F).mpr
    intro X hX T' L' G
    refine (FieldHas.rootField_le_iff F).mpr ⟨vals X hX T' L' G, ?_⟩
    rw [← uniformRootField_eq_of_grid G, hX, ← hZ, uniformRootField_eq_of_grid J]
    exact ((FieldHas.rootField_le_iff F).mp refF).2
  · refine sup_le inc (IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ?_))
    exact (test Z hZ T L J U (allU Z hZ T L J).values).mpr
      (fun X hX T' L' G => (allU X hX T' L' G).values)

/-- The uniform field is abelian Galois over every original grid's own coefficient
field; no claim that this reference field is Galois over ℚ is needed. -/
theorem every_grid_field_isAbelianGalois {Y : Stages} {T : Type} {L : LevCh Y.toD7 T} {sc : Consts}
    (G : GridData L sc) :
    IsAbelianGalois (gridCoefficientField G)
      (IntermediateField.extendScalars ((gridCoefficientField_le_iff G _).mpr (uniformGridField_has G))) := by
  obtain ⟨e, he, ζ, hζ, hall⟩ := every_grid_field Y sc
  have : NeZero e := ⟨fun h => (NeZero.ne (movingRayExponent Y.toD7)) (by simpa [h] using he)⟩
  let K := gridCoefficientField G
  have := hζ.intermediateField_adjoin_isCyclotomicExtension K
  have := IsCyclotomicExtension.isAbelianGalois ({e} : Set ℕ) K (IntermediateField.adjoin K {ζ})
  have hKU := (gridCoefficientField_le_iff G _).mpr (uniformGridField_has G)
  have hin : IntermediateField.extendScalars hKU ≤ IntermediateField.adjoin K {ζ} := by
    apply (IntermediateField.extendScalars_le_iff hKU _).mpr
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, hall Y rfl T L G]
  exact IsAbelianGalois.of_algHom (IntermediateField.inclusion hin)

#print axioms every_grid_field
#print axioms every_grid_field_isAbelianGalois
end GlobalTheory.GridField
