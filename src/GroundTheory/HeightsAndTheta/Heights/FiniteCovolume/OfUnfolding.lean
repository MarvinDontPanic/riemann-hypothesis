module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Assembly
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PReducedBasisBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordEmbedBasis
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFormCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTraceHermNondegenerate
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDualLatticeMultiple
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoordLatticeFullRank
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantTransport
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineNormalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldAlongSubgroup
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHaarParabolicCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerCovolume
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticePointsBelowFinite
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchimedeanUnitaryEquiv
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicLatticeDictionary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDoubleCosetCovolume

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

theorem ReducedBasisBound.full : ReducedBasisBound.Statement := ReducedBasisBound.proof

/-- In coordinates, the trace dual enlarges the Hermitian dual by an index bounded by
the clearing integer for the inverse different to the power of the rational dimension. -/
theorem traceHerm_relIndex_factor {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] {W : Type*} [AddCommGroup W] [Module E W]
    {ι : Type*} [Fintype ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hT : (traceHerm h v).Nondegenerate) (hfull : CoordLatticeFullRank.Statement v)
    (δ : ℤ)
    (hdiff : ∀ z : E, (∀ a : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((a : E) * z) = n) →
      IsIntegral ℤ ((δ : E) * z))
    {D : ℕ} (La : AddSubgroup W) (hLa : IsDIntegral h D La) :
    let L := La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
    let B := (traceHerm h v).dualSubmodule L.toIntSubmodule
    L.toIntSubmodule ≤ B ∧ ∃ a : ℕ, a ∣ δ.natAbs ^ finrank ℚ (ι → E) ∧
      L.relIndex B.toAddSubgroup = La.relIndex (dualLattice h La) * a := by
  classical
  let φ := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  let L := La.map φ
  let H := (dualLattice h La).map φ
  let B := (traceHerm h v).dualSubmodule L.toIntSubmodule
  have hφ : ∀ x, v.equivFun.symm (φ x) = x := v.equivFun.symm_apply_apply
  have hLH : L ≤ H := AddSubgroup.map_mono (fun y hy x hx => hLa.integral y hy x hx)
  have hHB : H ≤ B.toAddSubgroup := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩
    change traceHerm h v (φ y) (φ x) ∈ (1 : Submodule ℤ ℚ)
    rw [traceHerm_apply, hφ, hφ, Submodule.mem_one]
    exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace
      ((mem_integralClosure_iff ℤ E).mp (hy x hx)))
  have hδB : ∀ y ∈ B, δ • y ∈ H := by
    intro y hy
    refine ⟨δ • v.equivFun.symm y, ?_, ?_⟩
    · intro x hx
      rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
      refine (mem_integralClosure_iff ℤ E).mpr (hdiff _ fun a => ?_)
      obtain ⟨n, hn⟩ := Submodule.mem_one.mp
        (hy (φ ((a : E) • x)) (AddSubgroup.mem_map_of_mem φ (hLa.isLattice.smul_mem a x hx)))
      change algebraMap ℤ ℚ n = traceHerm h v y (φ ((a : E) • x)) at hn
      rw [traceHerm_apply, hφ, LinearMap.map_smul, smul_eq_mul] at hn
      exact ⟨n, hn.symm⟩
    · rw [map_zsmul]; exact congrArg (δ • ·) (v.equivFun.apply_symm_apply y)
  obtain ⟨hfg, hspan⟩ := hfull La hLa.isLattice
  refine ⟨hLH.trans hHB, H.relIndex B.toAddSubgroup,
    (traceHerm h v).relIndex_dual_dvd_pow_of_zsmul_mem hT L H hfg hspan δ hδB, ?_⟩
  rw [← AddSubgroup.relIndex_mul_relIndex L H B.toAddSubgroup hLH hHB,
    AddSubgroup.relIndex_map_map_of_injective La (dualLattice h La) v.equivFun.injective]

section Closed

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

section OneSpace

variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)


omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
/-- With fixed coordinates and measure, the Hermitian dual index determines the squared
covolume up to a divisor of a fixed power of the absolute field discriminant. -/
theorem ArchCovolumeBound.index_factors :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) (La : AddSubgroup W), IsDIntegral h D La →
      ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
        ∃ a : ℕ, a ∣ (NumberField.discr E).natAbs ^ finrank ℚ (ι → E) ∧
          ZLattice.covolume (archLattice v La) ^ 2 =
          C * (La.relIndex (dualLattice h La) : ℝ) * a := by
  let e := Pi.basis fun _ : ι => integralBasis E
  have hc := CoordEmbedBasis.proof E ι
  have ht := TraceHermNondegenerate.proof h v
  have hf := CoordLatticeFullRank.proof v
  obtain ⟨C, hC, hformula⟩ := IntegralFormCovolume.index_formula _ _ _ (coordEmbed E ι) e
    (traceHerm h v) volume (Measure.pi.isAddHaarMeasure _) ht hc.1
    (by rw [hc.2, finrank_eq_card_basis e])
  refine ⟨C, hC, ?_⟩
  intro D La hLa
  let φ := (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom
  have harch : archLattice v La = AddSubgroup.toIntSubmodule ((La.map φ).map (coordEmbed E ι)) := by
    rw [archLattice, AddSubgroup.map_map]
    rfl
  obtain ⟨hfg, hspan⟩ := hf La hLa.isLattice
  obtain ⟨hint, a, ha, hidx⟩ := traceHerm_relIndex_factor h v ht hf (NumberField.discr E)
    (isIntegral_discr_mul_of_integral_traces E) La hLa
  obtain ⟨hd, hZ, hcov⟩ := hformula (La.map φ) hfg hspan hint
  rw [harch]
  refine ⟨hd, hZ, a, ha, ?_⟩
  rw [hcov, hidx, Nat.cast_mul, mul_assoc]

omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
/-- The two constants work for every cutoff and every full integral lattice. -/
theorem ArchCovolumeBound.index_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (D : ℕ) (La : AddSubgroup W), IsDIntegral h D La →
      ∃ _ : DiscreteTopology (archLattice v La), IsZLattice ℝ (archLattice v La) ∧
        c * (La.relIndex (dualLattice h La) : ℝ) ≤ ZLattice.covolume (archLattice v La) ^ 2 ∧
        ZLattice.covolume (archLattice v La) ^ 2 ≤ C * (La.relIndex (dualLattice h La) : ℝ) := by
  obtain ⟨c, hc, hfactor⟩ := ArchCovolumeBound.index_factors h v
  let N := (NumberField.discr E).natAbs ^ finrank ℚ (ι → E)
  have hN : 0 < N := pow_pos (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)) _
  refine ⟨c, c * N, hc, mul_pos hc (by exact_mod_cast hN), fun D La hLa => ?_⟩
  obtain ⟨hd, hZ, a, ha, hv⟩ := hfactor D La hLa
  have hpos : (1 : ℝ) ≤ a := by exact_mod_cast Nat.pos_of_dvd_of_pos ha hN
  have hle : (a : ℝ) ≤ N := by exact_mod_cast Nat.le_of_dvd hN ha
  have hn : 0 ≤ c * (La.relIndex (dualLattice h La) : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg _)
  refine ⟨hd, hZ, ?_, ?_⟩
  · rw [hv]
    exact le_mul_of_one_le_right hn hpos
  · rw [hv, mul_right_comm c (N : ℝ)]
    exact mul_le_mul_of_nonneg_left hle hn

omit [NumberField F] [IsTotallyReal F] [DecidableEq ι] in
theorem ArchCovolumeBound.full : ArchCovolumeBound.Statement h v := by
  obtain ⟨_, C, _, hC, hbound⟩ := ArchCovolumeBound.index_bounds h v
  intro D
  refine ⟨Real.sqrt (C * D), fun La hLa => ?_⟩
  obtain ⟨hd, hZ, _, hcov⟩ := hbound D La hLa
  refine ⟨hd, hZ, (le_abs_self _).trans (Real.abs_le_sqrt (hcov.trans ?_))⟩
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hLa.index_le) hC.le

omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.full : MajorantTransport.Statement h v := MajorantTransport.proof h v


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementExtension.full : ComplementExtension.Statement h := ComplementExtension.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LineNormalForm.full : LineNormalForm.Statement h := LineNormalForm.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem ComplementLattice.full [FiniteDimensional E W] : ComplementLattice.Statement h :=
  ComplementLattice.proof h


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.full : LatticePointsBelowFinite.Statement h v :=
  LatticePointsBelowFinite.proof h v

theorem ArchimedeanUnitaryEquiv.full : ArchimedeanUnitaryEquiv.Statement h v :=
  ArchimedeanUnitaryEquiv.proof h v

theorem AdelicLatticeDictionary.full : AdelicLatticeDictionary.Statement h v :=
  AdelicLatticeDictionary.proof h v

end OneSpace

theorem LatticeOrbitsFiniteBelow.full (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N :=
  LatticeOrbitsFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) N

section Dimension

variable {W : Type u} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
variable (h : HermitianForm F E W)

theorem LatticeOrbitsFinite.full : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.step_of h (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h _) (MajorantTransport.full h _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem LinePairOrbitsFinite.full : LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.full_of h (LatticeOrbitsFiniteBelow.full _) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h)

theorem ScalingLaw.of_unfolding {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Basis ι E W)
    (hU : UnfoldingIntegral.Statement h v) : ScalingLaw.Statement h v :=
  ScalingLaw.full_of h v (LinePairOrbitsFinite.full h) hU

end Dimension

end Closed

section Adelic

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AdelicCovolumeFinite.of_covolume (h : HermitianForm F E W) (v : Basis ι E W)
    (hC : ArithmeticCovolumeFinite.Statement h v) : AdelicCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  AdelicCovolumeFinite.full_of h v (LatticeOrbitsFinite.full h) hC (ArchimedeanUnitaryEquiv.full h v)
    (AdelicLatticeDictionary.full h v) (DoubleCosetCovolume.proof _ _ _)

theorem HaarParabolicCoordinates.of_open (h : HermitianForm F E W) (v : Basis ι E W)
    (hAU : ArchUnimodular.Statement h v) (hMS : MajorantStabCompact.Statement h v)
    (hLS : LineStabHaar.Statement h v) : HaarParabolicCoordinates.Statement h v :=
  HaarParabolicCoordinates.proof h v (ParabolicDecomposition.full h v) hAU hMS hLS

end Adelic

section Open

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

variable
    (hAU : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchUnimodular.Statement h v)
    (hMS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantStabCompact.Statement h v)
    (hLS : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineStabHaar.Statement h v)
    (hSD : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (x₀ w₀ : W)
      (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), StabilizerLevi.Statement h v)
    (hUM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentModulus.Statement h v)
    (hUC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCocompact.Statement h v)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), CongruenceLift.Statement h)

include hAU hMS hLS hSD hSL hUM hUC hCL

theorem CovolumeFiniteBelow.of_open (N : ℕ) : CovolumeFiniteBelow.{u} F E N :=
  CovolumeFiniteBelow.of_steps ReducedBasisBound.full
    (fun _ _ _ _ h _ v => ArchCovolumeBound.full h v) (fun _ _ _ _ h _ v => MajorantTransport.full h v)
    (fun _ _ _ _ h => ComplementExtension.full h) (fun _ _ _ _ h => LineNormalForm.full h)
    (fun _ _ _ _ h => ComplementLattice.full h) (fun _ _ _ _ _ _ _ _ => UnfoldAlongSubgroup.proof _ _)
    (fun W _ _ _ h n v => HaarParabolicCoordinates.of_open h v (hAU W h n v) (hMS W h n v)
      (hLS W h n v))
    (fun W _ _ _ h n v hB => StabilizerCovolumeFinite.proof h v hB (hSD W h n v) (hSL W h n v)
      (hUM W h n v) (hUC W h n v) (hCL W h))
    (fun _ _ _ _ h _ v => LatticePointsBelowFinite.full h v) N

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

variable (hSD' : ∀ (x₀ w₀ : W) (h' : HermitianForm F E (hypComplement h x₀ w₀)) (m : ℕ)
      (v' : Basis (Fin m) E (hypComplement h x₀ w₀)),
      SemidirectCovering.Statement (vecFixGroup h v x₀) (archUnitary h' v') (unipRadical h v x₀))
    (hSL' : StabilizerLevi.Statement h v) (hUM' : UnipotentModulus.Statement h v)
    (hUC' : UnipotentCocompact.Statement h v)

include hSD' hSL' hUM' hUC'

theorem StabilizerCovolumeFinite.of_open : StabilizerCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  StabilizerCovolumeFinite.proof h v
    (CovolumeFiniteBelow.of_open hAU hMS hLS hSD hSL hUM hUC hCL _) hSD' hSL' hUM' hUC' (hCL W h)

variable (hAU' : ArchUnimodular.Statement h v) (hMS' : MajorantStabCompact.Statement h v)
    (hLS' : LineStabHaar.Statement h v)

include hAU' hMS' hLS'

theorem UnfoldingIntegral.of_open : UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.full_of h v (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')

theorem ScalingLaw.of_open : ScalingLaw.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ScalingLaw.of_unfolding h v
    (UnfoldingIntegral.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS' hLS')

theorem ArithmeticCovolumeFinite.of_open : ArithmeticCovolumeFinite.Statement h v :=
  haveI : FiniteDimensional E W := Module.Finite.of_basis v
  ArithmeticCovolumeFinite.step_of h v (LatticeOrbitsFiniteBelow.full _) ReducedBasisBound.full
    (ArchCovolumeBound.full h v) (MajorantTransport.full h v) (ComplementExtension.full h)
    (LineNormalForm.full h) (ComplementLattice.full h) (fun _ => UnfoldAlongSubgroup.proof _ _)
    (HaarParabolicCoordinates.of_open h v hAU' hMS' hLS')
    (StabilizerCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC')
    (LatticePointsBelowFinite.full h v)

theorem AdelicCovolumeFinite.of_open : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_covolume h v
    (ArithmeticCovolumeFinite.of_open hAU hMS hLS hSD hSL hUM hUC hCL h v hSD' hSL' hUM' hUC' hAU' hMS'
      hLS')

end Open

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
