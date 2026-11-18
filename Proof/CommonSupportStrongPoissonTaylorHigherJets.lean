import Proof.CommonSupportStrongAffineHigherJets
import Proof.PoissonAffineRemainderHigherJets
import Proof.InverseAffineRemainderHigherJets
import Proof.StrongPoissonTaylorDerivative
import Proof.BanachInverseFamilyJetBounds
import Proof.AffineInverseFamilyJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic OAI.AnisotropicCalderon.SpectralCoreRegularity
attribute [local irreducible] fullCoefficientOperatorL strongCoefficientOperatorL

def strongPoissonTaylorJetBudget (N : ℕ) (CI C0 qA P Q : ℝ) : ℝ :=
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let FB := fullC1OperatorBudget fixedSobolevCalculus
  ‖fixedStrongH2InclusionL‖*poissonAffineRemainderJetBudget N (inverseFamilyJetBudget N CI (2*SB*qA))
    C0 (2*SB*P+2*SB*Q) (2*FB*P) (2*FB*Q) fixedHarmonicLiftL

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def strongInverseTaylorJetBudget (N : ℕ) (CI C0 qA P1 QR : ℝ) : ℝ :=
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  inverseAffineRemainderJetBudget N (inverseFamilyJetBudget N CI (2*SB*qA))
    C0 (2*SB*P1+2*SB*QR) (2*SB*P1) (2*SB*QR)

/-- The actual strong Poisson and high radial Taylor errors keep r² in every
    finite mixed parameter jet, from local coefficient jets and point inverse
    norms for the SAME principal and flat operators. -/
theorem commonSupport_strong_poisson_taylor_higher_jets
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (F0 : SmoothCoefficientMatrix 2) (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (N : ℕ) (CI C0 qA P1 QR : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hqA : 0 ≤ qA) (hP1 : 0 ≤ P1) (hQR : 0 ≤ QR)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).inverse‖ ≤ CI)
    (hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C0)
    (hAJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ qA)
    (hFirstJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a1 (t,z) i j) x) p‖ ≤ P1)
    (hRemainderJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ QR*r^2) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    ∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (fun t => strongPoissonL (F t)-fixedHarmonicLiftL-
        r • strongFirstPoissonVariationL F0 (F1 t) 1) p‖ ≤ strongPoissonTaylorJetBudget N CI C0 qA P1 QR*r^2 ∧
      ‖iteratedFDeriv ℝ n (fun t => actualHighRadialErrorL (F t)-r • highFirstRadialVariationL F0 (F1 t) 1) p‖ ≤
        ‖fixedHalfOutwardTraceL‖*strongPoissonTaylorJetBudget N CI C0 qA P1 QR*r^2 ∧
      ‖iteratedFDeriv ℝ n (fun t => (strongDirichletOperator fixedSobolevCalculus 0 (F t)).inverse-
        (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse+
        r • (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse.comp
          ((strongDirichletOperator fixedSobolevCalculus 0 (F1 t)).comp
            (strongDirichletOperator fixedSobolevCalculus 0 F0).inverse)) p‖ ≤
        strongInverseTaylorJetBudget N CI C0 qA P1 QR*r^2 := by
  intro F F1
  let SB := strongC1OperatorBudget fixedSobolevCalculus
  let FB := fullC1OperatorBudget fixedSobolevCalculus
  let A := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F t)
  let A0 := strongDirichletOperator fixedSobolevCalculus 0 F0
  let A1 := fun t => strongDirichletOperator fixedSobolevCalculus 0 (F1 t)
  let T := fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F t)
  let T0 := fullCoefficientOperatorL fixedSobolevCalculus 0 F0
  let T1 := fun t => fullCoefficientOperatorL fixedSobolevCalculus 0 (F1 t)
  let CIJ := inverseFamilyJetBudget N CI (2*SB*qA)
  let C := poissonAffineRemainderJetBudget N CIJ C0 (2*SB*P1+2*SB*QR) (2*FB*P1) (2*FB*QR) fixedHarmonicLiftL
  let Corr := fun t => (A t).inverse.comp ((T t).comp fixedHarmonicLiftL)-
    r • A0.inverse.comp ((T1 t).comp fixedHarmonicLiftL)
  let Bulk := fun t => strongPoissonL (F t)-fixedHarmonicLiftL-r • strongFirstPoissonVariationL F0 (F1 t) 1
  have hSB : 0 ≤ SB := strongC1OperatorBudget_nonneg _
  have hFB : 0 ≤ FB := fullC1OperatorBudget_nonneg _
  have hCIJ : 0 ≤ CIJ := inverseFamilyJetBudget_nonneg N CI (2*SB*qA) hCI (by positivity)
  have hA : ContDiffAt ℝ ∞ A p :=
    (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a ha S hS hz).contDiffAt
  have hA1 : ContDiffAt ℝ ∞ A1 p :=
    (contDiff_commonSupport_actual_strongDirichletOperator fixedSobolevCalculus 0 a1 ha1 S1 hS1 hz1).contDiffAt
  have hT : ContDiffAt ℝ ∞ T p := (contDiff_commonSupport_fullCoefficientOperator 0 a ha S hS hz).contDiffAt
  have hT1 : ContDiffAt ℝ ∞ T1 p := (contDiff_commonSupport_fullCoefficientOperator 0 a1 ha1 S1 hS1 hz1).contDiffAt
  have hInvA : (A p).IsInvertible := hInv
  have hInvCont : ContDiffAt ℝ ∞ (fun L : StrongDirichletSpace 0 →L[ℝ] BallSobolev 0 => L.inverse) (A p) :=
    hInvA.contDiffAt_map_inverse
  have hAI : ContDiffAt ℝ ∞ (fun t => (A t).inverse) p := hInvCont.comp p hA
  have hCorr : ContDiffAt ℝ ∞ Corr p := (hAI.clm_comp (hT.clm_comp contDiffAt_const)).sub
    ((contDiffAt_const.clm_comp (hT1.clm_comp contDiffAt_const)).const_smul r)
  have hInvJets (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l (fun t => (A t).inverse) p‖ ≤ CIJ :=
    norm_iteratedFDeriv_inverse_family_le_of_isInvertible (E:=StrongDirichletSpace 0) (F:=BallSobolev 0)
      A p hInv hA N CI (2*SB*qA) hCI (by positivity) hNI
      (fun j _ hj => norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus a ha S hS hz p j qA hqA (hAJets j hj)) l hl
  have hFirstS (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l A1 p‖ ≤ 2*SB*P1 :=
    norm_iteratedFDeriv_commonSupport_strongOperator_zero_le fixedSobolevCalculus a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hFirstT (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l T1 p‖ ≤ 2*FB*P1 :=
    norm_iteratedFDeriv_commonSupport_fullOperator_zero_le fixedSobolevCalculus a1 ha1 S1 hS1 hz1 p l P1 hP1 (hFirstJets l hl)
  have hRem (l : ℕ) (hl : l ≤ N) :
      ‖iteratedFDeriv ℝ l (fun t => A t-A0-r • A1 t) p‖ ≤ (2*SB*QR)*r^2 ∧
      ‖iteratedFDeriv ℝ l (fun t => T t-T0-r • T1 t) p‖ ≤ (2*FB*QR)*r^2 := by
    have hh := norm_iteratedFDeriv_commonSupport_strong_full_affine_remainder_le a a1 aD ha ha1 haD
      S S1 SD hS hS1 hSD hz hz1 hzD r hField F0 hFlat p l (QR*r^2) (by positivity) (hRemainderJets l hl)
    exact ⟨hh.1.trans_eq (by dsimp only [SB];ring),hh.2.trans_eq (by dsimp only [FB];ring)⟩
  have hDiff (l : ℕ) (hl : l ≤ N) : ‖iteratedFDeriv ℝ l (fun t => A t-A0) p‖ ≤ (2*SB*P1+2*SB*QR)*r :=
    norm_iteratedFDeriv_difference_of_affine_remainder_le A A1 A0 p hA hA1 l r (2*SB*P1) (2*SB*QR)
      hr hr1 (by positivity) (by positivity) (hFirstS l hl) (hRem l hl).1
  have hFlatOp : T0.comp fixedHarmonicLiftL = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change fullCoefficientOperatorL fixedSobolevCalculus 0 F0 (fixedHarmonicLiftL f) = 0
    simpa only [one_smul,fixedHarmonicLiftL] using fullCoefficientOperator_flat_harmonicLift fixedSobolevCalculus sphereFischerInner
      orthogonalSphereHarmonics F0 hFlat 1 f
  have hSN (n : ℕ) (hn : n ≤ N) : ‖iteratedFDeriv ℝ n Corr p‖ ≤ C*r^2 :=
    norm_iteratedFDeriv_poisson_affine_remainder_le A A0 T T1 T0 fixedHarmonicLiftL p hA hT hT1 hInv hInv0 hFlatOp
      N r CIJ C0 (2*SB*P1+2*SB*QR) (2*FB*P1) (2*FB*QR) hr hCIJ hC0 (by positivity) (by positivity)
      (by positivity) hNI0 hInvJets hDiff hFirstT (fun l hl => (hRem l hl).2) n hn
  have hBulkEq : Bulk = fun t => -(fixedStrongH2InclusionL.comp (Corr t)) := by
    funext t
    simpa only [strongPoissonZeroFirstRemainderL,one_smul] using strongPoisson_first_remainder_eq_zero (F t) F0 (F1 t) 1 r
  have hBulkSmooth : ContDiffAt ℝ ∞ Bulk p := by
    rw [hBulkEq]
    exact (contDiffAt_const.clm_comp hCorr).neg
  have hHighEq : (fun t => actualHighRadialErrorL (F t)-r • highFirstRadialVariationL F0 (F1 t) 1) =
      fun t => fixedHalfOutwardTraceL.comp (Bulk t) := by
    funext t
    simp only [actualHighRadialErrorL,highFirstRadialVariationL,Bulk,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_smul]
  intro n hn
  have hBulkN : ‖iteratedFDeriv ℝ n Bulk p‖ ≤ strongPoissonTaylorJetBudget N CI C0 qA P1 QR*r^2 := by
    rw [hBulkEq,norm_iteratedFDeriv_neg_at _ p (contDiffAt_const.clm_comp hCorr) n]
    exact (norm_iteratedFDeriv_operator_postcomp_fixed_le fixedStrongH2InclusionL Corr p hCorr n).trans
      ((mul_le_mul_of_nonneg_left (hSN n hn) (norm_nonneg _)).trans_eq (by dsimp only [strongPoissonTaylorJetBudget,C,CIJ,SB,FB];ring))
  refine ⟨hBulkN,?_,?_⟩
  · rw [hHighEq]
    exact (norm_iteratedFDeriv_operator_postcomp_fixed_le fixedHalfOutwardTraceL Bulk p hBulkSmooth n).trans
      ((mul_le_mul_of_nonneg_left hBulkN (norm_nonneg _)).trans_eq (by ring))
  · exact norm_iteratedFDeriv_inverse_affine_remainder_le A A1 A0 p hA hA1 hInv hInv0 N r CIJ C0
      (2*SB*P1+2*SB*QR) (2*SB*P1) (2*SB*QR) hr hCIJ hC0 (by positivity) (by positivity) (by positivity)
      hNI0 hInvJets hDiff hFirstS (fun l hl => (hRem l hl).1) n hn

end ShrinkingSpheres
