module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridValuesFromOneReference
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory

/-- Outside any finite set, each open idelic ray class has a degree-one prime uniformizer. -/
theorem exists_degree_one_uniformizer_in_class {K : Type} [Field K] [NumberField K]
    (U : Subgroup (Ideles K)) (ho : IsOpen (U : Set (Ideles K)))
    (hk : (diagUnits K).range ⊔ infConn K ≤ U)
    (x : Ideles K) (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ π : (v.adicCompletion K)ˣ, IsUnifAt v π ∧ localIdele K v π * x⁻¹ ∈ U := by
  let Ω := AlgebraicClosure K
  obtain ⟨art, ha⟩ := globalArtinReciprocity_holds K Ω
  have hker : art.ker ≤ U := ha.ker ▸ Subgroup.topologicalClosure_minimal _ hk (U.isClosed_of_isOpen ho)
  let V := {y : Ideles K | y * x⁻¹ ∈ U}
  have hV : IsOpen V := ho.preimage (continuous_mul_const _)
  let f := fun σ : G K Ω => toAb K Ω σ⁻¹
  have hf : Continuous f := QuotientGroup.continuous_mk.comp continuous_inv
  have ht : IsOpen (f ⁻¹' (art '' V)) := (ha.quot.isOpenMap _ hV).preimage hf
  obtain ⟨τ, hτ⟩ := toAb_surjective (art x)
  have hne : (f ⁻¹' (art '' V)).Nonempty := ⟨τ⁻¹, x, by simp [V], by simpa [f] using hτ.symm⟩
  obtain ⟨σ, ⟨y, hy, hArt⟩, v, hv, hd, A, hA, hσ⟩ :=
    (dense_iff_inter_open.mp (Published.chebotarevDegreeOne'.dense (Ω := Ω) hS)) _ ht hne
  obtain ⟨π, hπ, he⟩ := (ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩
  have e : localIdele K v π * y⁻¹ ∈ art.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    exact he.trans hArt.symm
  exact ⟨v, hv, hd, π, hπ, by simpa [mul_assoc] using U.mul_mem (hker e) hy⟩

end GlobalTheory

open Formalism.BasicNotions GlobalTheory.Mem.LocTriv GlobalTheory.LevelChars

namespace GridInterpolation

private theorem isOpen_levSub {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) (N : ℕ) :
    IsOpen (levSub K S N : Set (Ideles K)) := by
  classical
  convert (GlobalTheory.Mem.UnitOpen.unit_open_and_congr_open K).2 hS.toFinset N using 1
  ext a
  refine ⟨fun h => ⟨fun v => (h v).1, fun v hv => (h v).2 (hS.mem_toFinset.1 hv)⟩, ?_⟩
  exact fun h v => ⟨h.1 v, fun hv => h.2 v (hS.mem_toFinset.2 hv)⟩

private theorem local_unit_mem_levSub {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (N : ℕ) {x : (v.adicCompletion K)ˣ} (hu : IsUnitAt v x) :
    localIdele K v x ∈ levSub K S N := by
  intro w
  change Valued.v (ev w (localIdele K v x : AdeleRing (𝓞 K) K)) = 1 ∧
    (w ∈ S → Valued.v (ev w (localIdele K v x : AdeleRing (𝓞 K) K) - 1) ≤ _)
  by_cases h : w = v
  · subst w
    exact ⟨by rw [ev_local_self]; exact hu, fun h => (hv h).elim⟩
  · rw [ev_local_ne h]
    simp

/-- Every moving ray class is attained at a degree-one prime, with the grid's actual
uniformizer and outside both the moving level and any extra finite set. -/
theorem exists_good_prime_in_moving_class (D : D7) (x : Ideles D.host.E)
    (S : Set (HeightOneSpectrum (𝓞 D.host.E))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.E), v ∉ S ∧ v ∉ allBad D ∧
      v.asIdeal.inertiaDeg ℤ = 1 ∧
      localIdele D.host.E v (atFin v (unif v)) * x⁻¹ ∈ movingRayGroup D := by
  have hp := allBad_finite D
  have ho : IsOpen (movingRayGroup D : Set (Ideles D.host.E)) :=
    Subgroup.isOpen_mono le_sup_right (isOpen_levSub hp 2)
  have hk : (diagUnits D.host.E).range ⊔ infConn D.host.E ≤ movingRayGroup D := by
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    rintro _ ⟨y, _, rfl⟩ w
    change Valued.v (1 : w.adicCompletion D.host.E) = 1 ∧
      (w ∈ allBad D → Valued.v ((1 : w.adicCompletion D.host.E) - 1) ≤ _)
    simp
  obtain ⟨v, hv, hd, π, hπ, hrep⟩ :=
    GlobalTheory.exists_degree_one_uniformizer_in_class _ ho hk x _ (hS.union hp)
  have hvb : v ∉ allBad D := fun h => hv (Or.inr h)
  have hu : IsUnitAt v (atFin v (unif v) * π⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, show Valued.v (atFin v (unif v) : v.adicCompletion D.host.E) = _ from unif_spec v,
      show Valued.v (π : v.adicCompletion D.host.E) = _ from hπ, mul_inv_cancel₀ WithZero.exp_ne_zero]
  refine ⟨v, fun h => hv (Or.inl h), hvb, hd, ?_⟩
  have hl := (show levSub D.host.E (allBad D) 2 ≤ movingRayGroup D from le_sup_right)
    (local_unit_mem_levSub hvb 2 hu)
  rw [map_mul, map_inv] at hl
  simpa [mul_assoc] using (movingRayGroup D).mul_mem hl hrep

end GridInterpolation
