import Proof.OperatorMultiplierKernelHigherJets
import Proof.CommonSupportMultiplierForcingTaylorHigherJets
import Proof.CommonSupportWeakPoissonTaylorHigherJets
import Proof.CommonSupportWeakFirstPoissonHigherJets
import Proof.CommonSupportStrongPoissonTaylorHigherJets
import Proof.CommonSupportMultiplierForcingRegularity
import Proof.CommonSupportWeakFamilyIdentities
import Proof.NativeWeakCoefficientCongruence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  nativeCoefficientWeakFunctionalInverse commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

def nativeMultiplierKernelTaylorJetBudget (N : ℕ) (F0 : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3)
    (CI C0 CW CW0 qA P1 QR B : ℝ) : ℝ :=
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let CA1 := 2*SB*P1
  let CG := 270*nativeMultiplierForcingGradientBudget*B
  let CQI := |strongInverseTaylorJetBudget N CI C0 qA P1 QR|
  multiplierKernelTaylorJetBudget N (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
    (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
    (inverseFamilyJetBudget N CI (2*SB*qA)) C0 CA1 (CG*qA) (C0*C0*CA1+CQI) CQI
    (CG*QR) (CG*P1) |weakPoissonTaylorJetBudget N CW CW0 qA P1 QR|
    (CW0*(weakFullDerivativeBudget*P1)*‖fixedHarmonicH1LiftL‖)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The same genuine native strong inverse, forcing and weak Poisson factors
    give all finite mixed quadratic jets of the actual multiplier kernel. -/
theorem commonSupport_native_multiplier_kernel_taylor_higher_jets
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (F0 : SmoothCoefficientMatrix 2) (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (N : ℕ) (Q : SmoothCoefficientJets 3) (CI C0 CW CW0 qA P1 QR B : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCW : 0 ≤ CW) (hCW0 : 0 ≤ CW0) (hB : 0 ≤ B)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hqA : 0 ≤ qA) (hP1 : 0 ≤ P1) (hQR : 0 ≤ QR)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).inverse‖ ≤ CI)
    (hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C0)
    (hWeak : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hWeak0 : (nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).IsInvertible)
    (hNW : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ CW)
    (hNW0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ CW0)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B)
    (hAJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ qA)
    (hFirstJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a1 (t,z) i j) x) p‖ ≤ P1)
    (hRemainderJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ QR*r^2) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n (fun t => operatorMultiplierTaylorKernel
      (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
      (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 (F1 t))
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q)
      (commonSupportWeakHalfLift a ha t) fixedHarmonicH1LiftL
      (weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) r) p‖ ≤
        nativeMultiplierKernelTaylorJetBudget N F0 Q CI C0 CW CW0 qA P1 QR B*r^2 := by
  intro F F1
  let A := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)
  let A1 := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t)
  let I := fun t => (A t).inverse
  let I0 := (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
  let I1 := fun t => -(I0.comp ((A1 t).comp I0))
  let K := fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q
  let K0 := nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q
  let K1 := fun t => nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q
  let W := commonSupportWeakHalfLift a ha
  let W1 := fun t => weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let CA1 := 2*SB*P1
  let CG := 270*nativeMultiplierForcingGradientBudget*B
  let CIJ := inverseFamilyJetBudget N CI (2*SB*qA)
  let CQI := |strongInverseTaylorJetBudget N CI C0 qA P1 QR|
  let CQP := |weakPoissonTaylorJetBudget N CW CW0 qA P1 QR|
  have hSB : 0 ≤ SB := strongC1OperatorBudget_nonneg _
  have hCG : 0 ≤ CG := by
    have hG := nativeMultiplierForcingGradientBudget_nonneg
    dsimp only [CG]
    positivity
  have hCA1 : 0 ≤ CA1 := by dsimp only [CA1];positivity
  have hCIJ : 0 ≤ CIJ := inverseFamilyJetBudget_nonneg N CI (2*SB*qA) hCI (by positivity)
  have hCQI : 0 ≤ CQI := abs_nonneg _
  have hCQP : 0 ≤ CQP := abs_nonneg _
  have hA : ContDiffAt ℝ ∞ A p :=
    (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha S hS hz).contDiffAt
  have hA1 : ContDiffAt ℝ ∞ A1 p :=
    (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a1 ha1 S1 hS1 hz1).contDiffAt
  have hInvA : (A p).IsInvertible := hInv
  have hInvMap : ContDiffAt ℝ ∞
      (fun L : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => L.inverse) (A p) := hInvA.contDiffAt_map_inverse
  have hI : ContDiffAt ℝ ∞ I p := hInvMap.comp p hA
  have hI1 : ContDiffAt ℝ ∞ I1 p := (contDiffAt_const.clm_comp (hA1.clm_comp contDiffAt_const)).neg
  have hK : ContDiffAt ℝ ∞ K p := (contDiff_commonSupport_bulkMultiplierForcing a ha S hS hz Q).contDiffAt
  have hK1 : ContDiffAt ℝ ∞ K1 p := (contDiff_commonSupport_bulkMultiplierForcing a1 ha1 S1 hS1 hz1 Q).contDiffAt
  have hW : ContDiffAt ℝ ∞ W p := by
    dsimp only [W]
    rw [commonSupportWeakHalfLift_eq_affineInverseCorrection]
    exact contDiffAt_affineInverseCorrectionFamily (P:=P) (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      (U:=BallH1) (Z:=SphereSobolev (1/2:ℝ)) _ _ _ _ p hWeak
      (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).contDiffAt
      (contDiff_commonSupportWeakEnergy a ha S hS hz).contDiffAt
  have hW1 : ContDiffAt ℝ ∞ W1 p := (contDiff_commonSupport_weakFirstPoisson a1 ha1 S1 hS1 hz1 1).contDiffAt
  have hAJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l A p‖ ≤ 2*SB*qA :=
    norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus a ha S hS hz p l qA hqA (hAJets l hl)
  have hA1J (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l A1 p‖ ≤ CA1 :=
    norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hIJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l I p‖ ≤ CIJ :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible (P:=P) (E:=StrongDirichletSpace 0) (F:=BallSobolev 0)
      A p hInv hA N CI (2*SB*qA) hCI (by positivity) hNI (fun j _ hj => hAJ j hj) l hl
  have hStrong := commonSupport_strong_poisson_taylor_higher_jets a a1 aD ha ha1 haD S S1 SD hS hS1 hSD
    hz hz1 hzD r hField F0 hFlat p N CI C0 qA P1 QR hr hr1 hCI hC0 hqA hP1 hQR
    hInv hInv0 hNI hNI0 hAJets hFirstJets hRemainderJets
  have hIRem (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => I t-I0-r • I1 t) p‖ ≤ CQI*r^2 := by
    have hh := (hStrong l hl).2.2
    have hStep := hh.trans (mul_le_mul_of_nonneg_right
      (le_abs_self (strongInverseTaylorJetBudget N CI C0 qA P1 QR)) (sq_nonneg r))
    simpa only [I1,smul_neg,sub_neg_eq_add] using hStep
  have hI1J (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l I1 p‖ ≤ C0*C0*CA1 := by
    rw [norm_iteratedFDeriv_neg_at _ p (contDiffAt_const.clm_comp (hA1.clm_comp contDiffAt_const)) l]
    exact (norm_iteratedFDeriv_operator_sandwich_le I0 I0 A1 p hA1 l).trans
      (mul_le_mul (mul_le_mul hNI0 hNI0 (norm_nonneg _) hC0) (hA1J l hl) (norm_nonneg _) (by positivity))
  have hIDiff (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => I t-I0) p‖ ≤ (C0*C0*CA1+CQI)*r :=
    norm_iteratedFDeriv_difference_of_affine_remainder_le I I1 I0 p hI hI1 l r (C0*C0*CA1) CQI
      hr hr1 (by positivity) hCQI (hI1J l hl) (hIRem l hl)
  have hKJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l K p‖ ≤ CG*qA :=
    norm_iteratedFDeriv_commonSupport_nativeBulkMultiplierForcing_le a ha S hS hz p Q l qA B hqA hB
      (hAJets l hl) hQ1 hQ2
  have hK1J (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l K1 p‖ ≤ CG*P1 :=
    norm_iteratedFDeriv_commonSupport_nativeBulkMultiplierForcing_le a1 ha1 S1 hS1 hz1 p Q l P1 B hP1 hB
      (hFirstJets l hl) hQ1 hQ2
  have hKRem (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => K t-K0-r • K1 t) p‖ ≤ (CG*QR)*r^2 :=
    (norm_iteratedFDeriv_commonSupport_nativeBulkMultiplierForcing_affine_remainder_le
      a a1 aD ha ha1 S S1 hS hS1 hz hz1 r hField F0 hFlat p Q l (QR*r^2) B
      (by positivity) hB (hRemainderJets l hl) hQ1 hQ2).trans_eq (by dsimp only [CG];ring)
  have hV (l : ℕ) (hl : l ≤ N) (i j : ShrinkingSpheres.I) (x : X) (hx : x ∈ (ballOpens:Set X)) :=
    hAJets l hl i j ⟨0,by omega⟩ x hx
  have hV1 (l : ℕ) (hl : l ≤ N) (i j : ShrinkingSpheres.I) (x : X) (hx : x ∈ (ballOpens:Set X)) :=
    hFirstJets l hl i j ⟨0,by omega⟩ x hx
  have hVR (l : ℕ) (hl : l ≤ N) (i j : ShrinkingSpheres.I) (x : X) (hx : x ∈ (ballOpens:Set X)) :=
    hRemainderJets l hl i j ⟨0,by omega⟩ x hx
  have hWeakRem := commonSupport_weak_poisson_taylor_higher_jets a a1 aD ha ha1 haD S S1 SD hS hS1 hSD
    hz hz1 hzD r hField p N CW CW0 qA P1 QR hr hr1 hCW hCW0 hqA hP1 hQR
    hWeak hWeak0 hNW hNW0 hV hV1 hVR
  have hWRem (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => W t-fixedHarmonicH1LiftL-r • W1 t) p‖ ≤ CQP*r^2 :=
    (hWeakRem l hl).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))
  have hNIWeak0 : ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat)) 0 0
      (flatCoefficientBound 1)‖ ≤ CW0 := by
    have he := nativeZeroCoefficientEnergy_inverse_eq (a:=fun _ : X => (1:ℝ) • (1:Mat)) (flatCoefficientBound 1)
    exact (congrArg norm he.symm).le.trans hNW0
  have hW1J (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l W1 p‖ ≤ CW0*(weakFullDerivativeBudget*P1)*‖fixedHarmonicH1LiftL‖ :=
    norm_iteratedFDeriv_commonSupport_weakFirstPoisson_le a1 ha1 S1 hS1 hz1 1 p l CW0 P1 hCW0 hP1
      hNIWeak0 (hV1 l hl)
  have hWB := weakFullDerivativeBudget_nonneg
  intro n hn
  exact norm_iteratedFDeriv_operatorMultiplierTaylorKernel_le
    (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL I I0 A1 K K1 K0 W W1 p
    hI hA1 hK hK1 hW hW1 N r CIJ C0 CA1 (CG*qA) (C0*C0*CA1+CQI) CQI (CG*QR) (CG*P1) CQP
      (CW0*(weakFullDerivativeBudget*P1)*‖fixedHarmonicH1LiftL‖) hr hr1 hCIJ hC0 hCA1 (by positivity)
      (by positivity) hCQI (by positivity) (by positivity) hCQP (by positivity) hNI0
      hIJ hA1J hKJ hK1J hIDiff hIRem hKRem hWRem hW1J n hn

/-- The same actual radial multiplier commutator family is precisely the
    kernel estimated above, with its original integrability witnesses. -/
theorem commonSupport_radialTaylorMultiplierCommutator_eq_kernel
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hMem : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hMem1 : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hMem0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens)) (Q : SmoothCoefficientJets 3) (r : ℝ) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    (fun t => radialTaylorMultiplierCommutatorL (F t) F0 (F1 t) (hMem t) hMem0 (hMem1 t) Q r) =
    (fun t => operatorMultiplierTaylorKernel
      (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
      (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 (F1 t))
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q)
      (commonSupportWeakHalfLift a ha t) fixedHarmonicH1LiftL
      (weakFirstPoissonVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)) r) := by
  intro F F1
  have hP0 : nativeWeakHalfLift (coefficientMatrixField 2 F0) 0 0 hMem0 sphereFischerInner = fixedHarmonicH1LiftL :=
    (nativeWeakHalfLift_congr_unitBall hMem0 (flatCoefficientBound 1)
      (by intro z hzB;simpa only [one_smul] using hFlat z hzB)).trans
        (nativeWeakHalfLift_flat_eq 1 (flatCoefficientBound 1))
  have hW := commonSupport_native_weak_lift_family_eq a ha S hS hz hMem
  have hW1 := commonSupport_native_weak_first_family_eq a1 ha1 S1 hS1 hz1 hMem1
  funext t
  have hk := radialTaylorMultiplierCommutator_kernel (F t) F0 (F1 t) (hMem t) hMem0 (hMem1 t) Q r
  rw [hP0] at hk
  have he := congrArg₂ (fun U U1 : SphereSobolev (1/2:ℝ) →L[ℝ] BallH1 =>
    operatorMultiplierTaylorKernel (fixedHalfOutwardTraceL.comp fixedStrongH2InclusionL) fixedHarmonicH1LiftL
      (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse
      (strongDirichletOperator fixedSobolevCalculus 0 (F1 t))
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q)
      (nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q)
      U fixedHarmonicH1LiftL U1 r) (congrFun hW t) (congrFun hW1 t)
  exact hk.trans he

end ShrinkingSpheres
