import Proof.RadialTaylorHigherJets
import Proof.CommonSupportFirstRadialHigherJets
import Proof.BoundaryMatrixFlatIdentities
import Proof.CommonSupportWeakConormalTaylorHigherJets
import Proof.CommonSupportRadialTaylorIdentity
import Proof.CommonSupportPoissonHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.NativeBoundaryCoefficientFamilies
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

def lowRadialTaylorJetBudget (N : ℕ) (CNI CI C0 qA P1 QR : ℝ) : ℝ :=
  let CB := 1404*boundaryHalfMultiplierBudget
  let CR := radialTaylorRhsJetBudget N fixedLowRadialL fixedSphereTangentialL
    |weakConormalTaylorJetBudget N CI C0 qA P1 QR| (CB*QR) (CB*QR) (CB*P1+CB*QR) (firstLowRadialJetConstant*P1)
  2^N*inverseFamilyJetBudget N CNI (CB*qA)*CR

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The exact supplied radial left identity and the same actual inverse,
    conormal and boundary maps give every finite quadratic Taylor jet. -/
theorem commonSupport_low_radial_taylor_higher_jets
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (F0 : SmoothCoefficientMatrix 2)
    (hFlat2 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (p : P) (N : ℕ) (CNI CI C0 qA P1 QR : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCNI : 0 ≤ CNI) (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hqA : 0 ≤ qA) (hP1 : 0 ≤ P1) (hQR : 0 ≤ QR)
    (hInv : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hInv0 : (nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).IsInvertible)
    (hNI : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ CI)
    (hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ C0)
    (hNormal : (negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)).IsInvertible)
    (hNN : ‖(negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz p)).inverse‖ ≤ CNI)
    (hFirstTan : ∀ j : I,(fun t => boundaryMatrixMultiplier (some j)
      (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t)) =ᶠ[𝓝 p] (fun _ => 0))
    (hAJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ qA)
    (hFirstJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a1 (t,z) i j) x) p‖ ≤ P1)
    (hRemainderJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ QR*r^2) :
    ∀ n : ℕ,n ≤ N →
    ‖iteratedFDeriv ℝ n (fun t => commonSupportLowRadialErrorL a ha S hS hz t-
      r • commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1 t) p‖ ≤
        lowRadialTaylorJetBudget N CNI CI C0 qA P1 QR*r^2 := by
  let F := commonSupportMatrixFamily 2 a ha S hS hz
  let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
  let M := fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a ha S hS hz t)
  let M1 := fun t => negativeBoundaryCoefficientMulL (normalCoefficientJetsFamily a1 ha1 S1 hS1 hz1 t)
  let Nop := commonSupportWeakConormalEndpoint a ha
  let N1 := fun t => weakFirstConormalVariationL 1 (fun z => a1 (t,z)) (commonSupportEnergyMemLp a1 ha1 t)
  let B := commonSupportLowFirstRadialL a1 ha1 S1 hS1 hz1 1
  let T := fun j t => negativeBoundaryCoefficientMulL (tangentCoefficientJetsFamily a ha S hS hz j t)
  let NQ := fun t => Nop t-fixedLowRadialL-r • N1 t
  let MQ := fun t => M t-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • M1 t
  let J := fun t => commonSupportLowRadialErrorL a ha S hS hz t-r • B t
  let RHS := fun t => NQ t-(MQ t).comp fixedLowRadialL-
    ∑ j : I,(T j t).comp (fixedSphereTangentialL j)-
      r • (M t-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))).comp (B t)
  let CB := 1404*boundaryHalfMultiplierBudget
  let CN := |weakConormalTaylorJetBudget N CI C0 qA P1 QR|
  let CR := radialTaylorRhsJetBudget N fixedLowRadialL fixedSphereTangentialL CN
    (CB*QR) (CB*QR) (CB*P1+CB*QR) (firstLowRadialJetConstant*P1)
  have hCB : 0 ≤ CB := mul_nonneg (by norm_num) boundaryHalfMultiplierBudget_nonneg
  have hCN : 0 ≤ CN := abs_nonneg _
  have hFirst := firstLowRadialJetConstant_nonneg
  have hCR : 0 ≤ CR := by dsimp only [CR,radialTaylorRhsJetBudget];positivity
  have hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1 := by
    intro z hzB
    exact hFlat2 z (Metric.closedBall_subset_closedBall (by norm_num) (Metric.ball_subset_closedBall hzB))
  have hM0 := boundaryMatrixMultiplier_none_flat_eq_id F0 hFlat2
  have hT0 (j : I) := boundaryMatrixMultiplier_some_flat_eq_zero F0 hFlat2 j
  have hEqM : M = fun t => boundaryMatrixMultiplier none (F t) :=
    funext (fun t => commonSupport_negative_normal_multiplier_eq a ha S hS hz t)
  have hEqM1 : M1 = fun t => boundaryMatrixMultiplier none (F1 t) :=
    funext (fun t => commonSupport_negative_normal_multiplier_eq a1 ha1 S1 hS1 hz1 t)
  have hEqT (j : I) : T j = fun t => boundaryMatrixMultiplier (some j) (F t) :=
    funext (fun t => commonSupport_negative_tangent_multiplier_eq a ha S hS hz j t)
  have hM : ContDiffAt ℝ ∞ M p :=
    (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz).contDiffAt
  have hM1 : ContDiffAt ℝ ∞ M1 p :=
    (contDiff_negativeHalf_normalCoefficientFamily fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a1 ha1 S1 hS1 hz1).contDiffAt
  have hT (j : I) : ContDiffAt ℝ ∞ (T j) p :=
    (contDiff_negativeHalf_tangentCoefficientFamily fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics denseSphereHarmonics fixedUnitBallValueTrace a ha S hS hz j).contDiffAt
  have hW : ContDiffAt ℝ ∞ (commonSupportWeakHalfLift a ha) p := by
    rw [commonSupportWeakHalfLift_eq_affineInverseCorrection]
    exact contDiffAt_affineInverseCorrectionFamily (P:=P) (E:=BallH1Zero) (F:=StrongDual ℝ BallH1Zero)
      (U:=BallH1) (Z:=SphereSobolev (1/2:ℝ)) _ _ _ _ p hInv
      (contDiff_commonSupportZeroWeakEnergy a ha S hS hz).contDiffAt
      (contDiff_commonSupportWeakEnergy a ha S hS hz).contDiffAt
  have hNop : ContDiffAt ℝ ∞ Nop p := by
    dsimp only [Nop]
    rw [commonSupportWeakConormalEndpoint_eq_fixedPost]
    exact contDiffAt_const.clm_comp
      ((contDiff_commonSupportFullWeakEnergy a ha S hS hz).contDiffAt.clm_comp hW)
  have hN1 : ContDiffAt ℝ ∞ N1 p := (contDiff_commonSupport_weakFirstConormal a1 ha1 S1 hS1 hz1 1).contDiffAt
  have hB : ContDiffAt ℝ ∞ B p := (contDiff_commonSupport_lowFirstRadial_one a1 ha1 S1 hS1 hz1).contDiffAt
  have hNQ : ContDiffAt ℝ ∞ NQ p := (hNop.sub contDiffAt_const).sub (hN1.const_smul r)
  have hMQ : ContDiffAt ℝ ∞ MQ p := (hM.sub contDiffAt_const).sub (hM1.const_smul r)
  have hNQJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l NQ p‖ ≤ CN*r^2 := by
    have hh := commonSupport_weak_conormal_taylor_higher_jets a a1 aD ha ha1 haD
      S S1 SD hS hS1 hSD hz hz1 hzD r hField p N CI C0 qA P1 QR hr hr1 hCI hC0 hqA hP1 hQR
      hInv hInv0 hNI hNI0 (fun j hj i k x hx => hAJets j hj i k ⟨0,by omega⟩ x hx)
      (fun j hj i k x hx => hFirstJets j hj i k ⟨0,by omega⟩ x hx)
      (fun j hj i k x hx => hRemainderJets j hj i k ⟨0,by omega⟩ x hx) l hl
    have hStep := hh.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))
    simpa only [one_smul] using hStep
  have hMQJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l MQ p‖ ≤ (CB*QR)*r^2 := by
    rw [show MQ = fun t => M t-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))-r • M1 t from rfl,
      hEqM,hEqM1,← hM0]
    exact (norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_affine_remainder_le none
      a a1 aD ha ha1 S S1 hS hS1 hz hz1 r hField F0 hFlat p l (QR*r^2) (by positivity)
      (hRemainderJets l hl)).trans_eq (by dsimp only [CB];ring)
  have hTJ (j : I) (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l (T j) p‖ ≤ (CB*QR)*r^2 := by
    have he : (fun t => boundaryMatrixMultiplier (some j) (F t)) =ᶠ[𝓝 p]
        (fun t => boundaryMatrixMultiplier (some j) (F t)-boundaryMatrixMultiplier (some j) F0-
          r • boundaryMatrixMultiplier (some j) (F1 t)) := by
      filter_upwards [hFirstTan j] with t ht
      rw [hT0 j,ht,smul_zero,sub_zero,sub_zero]
    rw [hEqT j,(he.iteratedFDeriv ℝ l).eq_of_nhds]
    exact (norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_affine_remainder_le (some j)
      a a1 aD ha ha1 S S1 hS hS1 hz hz1 r hField F0 hFlat p l (QR*r^2) (by positivity)
      (hRemainderJets l hl)).trans_eq (by dsimp only [CB];ring)
  have hM1J (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l M1 p‖ ≤ CB*P1 := by
    rw [hEqM1]
    exact norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_le none a1 ha1 S1 hS1 hz1 p l P1 hP1
      (hFirstJets l hl)
  have hMDJ (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => M t-ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) p‖ ≤ (CB*P1+CB*QR)*r :=
    norm_iteratedFDeriv_difference_of_affine_remainder_le M M1 (ContinuousLinearMap.id ℝ _) p hM hM1 l r
      (CB*P1) (CB*QR) hr hr1 (by positivity) (by positivity) (hM1J l hl) (hMQJ l hl)
  have hBJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l B p‖ ≤ firstLowRadialJetConstant*P1 :=
    norm_iteratedFDeriv_commonSupport_lowFirstRadial_one_le a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hMJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l M p‖ ≤ CB*qA := by
    rw [hEqM]
    exact norm_iteratedFDeriv_commonSupport_boundaryMatrixMultiplier_le none a ha S hS hz p l qA hqA (hAJets l hl)
  have hRHS : ContDiffAt ℝ ∞ RHS p := by
    have hSum : ContDiffAt ℝ ∞ (fun t => ∑ j : I,(T j t).comp (fixedSphereTangentialL j)) p :=
      ContDiffAt.sum (fun j _ => (hT j).clm_comp contDiffAt_const)
    exact ((hNQ.sub (hMQ.clm_comp contDiffAt_const)).sub hSum).sub
      (((hM.sub contDiffAt_const).clm_comp hB).const_smul r)
  have hRHSJ (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l RHS p‖ ≤ CR*r^2 := by
    have hMDJ' : ∀ j : ℕ,j ≤ N →
        ‖iteratedFDeriv ℝ j (fun t => M t-(1:ℝ) • ContinuousLinearMap.id ℝ (SphereSobolev (-(1/2:ℝ)))) p‖ ≤
          (CB*P1+CB*QR)*r := by simpa only [one_smul] using hMDJ
    have hh := norm_iteratedFDeriv_radial_taylor_rhs_le NQ B MQ M T fixedLowRadialL fixedSphereTangentialL p
      hNQ hB hMQ hM hT N 1 r CN (CB*QR) (CB*QR) (CB*P1+CB*QR) (firstLowRadialJetConstant*P1)
      hr hCN (by positivity) (by positivity) (by positivity) (by positivity)
      hNQJ hMQJ hTJ hMDJ' hBJ l hl
    simpa only [one_smul] using hh
  have hIdentity : (fun t => (M t).comp (J t)) =ᶠ[𝓝 p] RHS := by
    filter_upwards [eventually_isInvertible_of_continuousAt M p hM.continuousAt hNormal] with t ht
    have hh := commonSupport_lowRadial_first_remainder_left_identity a a1 ha ha1 S S1 hS hS1 hz hz1 1 r t
      (by norm_num) ht
    simpa only [one_smul] using hh
  intro n hn
  exact norm_iteratedFDeriv_operator_family_of_left_identity_le M J RHS p hM hRHS hIdentity hNormal N r
    CNI (CB*qA) CR hCNI (by positivity) hCR hNN (fun j _ hj => hMJ j hj) hRHSJ n hn

end ShrinkingSpheres
