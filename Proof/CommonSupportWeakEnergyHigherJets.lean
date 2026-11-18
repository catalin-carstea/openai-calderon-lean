import Proof.CommonSupportMultiplierHigherJets
import Proof.CommonSupportWeakEnergyDerivative
import Proof.FiniteJetBoundCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] nativeCoefficientWeakEnergyL nativeZeroCoefficientEnergyL
  commonSupportFullWeakEnergy commonSupportWeakEnergy commonSupportZeroWeakEnergy

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem norm_iteratedFDeriv_commonSupportFullWeakEnergy_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (commonSupportFullWeakEnergy a ha) p‖ ≤ weakFullDerivativeBudget*q := by
  let H := Lp ℝ 2 ((volume:Measure X).restrict ballOpens)
  let M := fun i j t => coefficientMultiplier fixedSobolevCalculus 0
    (commonSupportCoefficientFamily 1 (fun v => a v i j)
      (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun t z h => by rw [hz t z h];rfl) t)
  let R (i j : I) : (H →L[ℝ] H) →L[ℝ] (BallH1 →L[ℝ] StrongDual ℝ BallH1) :=
    (ContinuousLinearMap.compL ℝ BallH1 H (StrongDual ℝ BallH1)
      (forcingFromValueL (unitBallCoordinateGradientL i))).comp
        ((ContinuousLinearMap.compL ℝ BallH1 H H).flip (unitBallCoordinateGradientL j))
  let T := fun i j => R i j ∘ M i j
  have hM (i j : I) : ContDiff ℝ ∞ (M i j) :=
    contDiff_commonSupport_actual_coefficientMultiplier fixedSobolevCalculus 0
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun t z h => by rw [hz t z h];rfl)
  have hT (i j : I) : ContDiff ℝ ∞ (T i j) := (R i j).contDiff.comp (hM i j)
  have hMN (i j : I) : ‖iteratedFDeriv ℝ n (M i j) p‖ ≤ q :=
    norm_iteratedFDeriv_commonSupport_coefficientMultiplier_zero_le fixedSobolevCalculus
      (fun v => a v i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
        (fun t z h => by rw [hz t z h];rfl) p n q hq (hJet i j)
  have hRN (i j : I) : ‖R i j‖ ≤
      ‖forcingFromValueL (unitBallCoordinateGradientL i)‖*‖unitBallCoordinateGradientL j‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro L
    change ‖(forcingFromValueL (unitBallCoordinateGradientL i)).comp
      (L.comp (unitBallCoordinateGradientL j))‖ ≤ _
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans_eq (by ring))
  have hTN (i j : I) : ‖iteratedFDeriv ℝ n (T i j) p‖ ≤
      (‖forcingFromValueL (unitBallCoordinateGradientL i)‖*‖unitBallCoordinateGradientL j‖)*q := by
    exact (norm_iteratedFDeriv_clm_comp_le (R i j) (M i j) p (hM i j).contDiffAt n).trans
      (mul_le_mul (hRN i j) (hMN i j) (norm_nonneg _) (by positivity))
  have hEq : commonSupportFullWeakEnergy a ha = fun t => ∑ i : I,∑ j : I,T i j t := by
    funext t
    rw [← commonSupportFullWeakEnergy_smooth_eq a ha K hK hz]
    have hZero : coefficientMultiplier fixedSobolevCalculus 0 (0:SmoothCoefficientJets 1) = 0 :=
      (coefficientMultiplierL fixedSobolevCalculus 0).map_zero
    simp only [nativeSmoothCoefficientFullEnergyL,hZero,ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero,Finset.sum_const_zero,add_zero]
    rfl
  have hSum : iteratedFDeriv ℝ n (fun t => ∑ i : I,∑ j : I,T i j t) p =
      ∑ i : I,∑ j : I,iteratedFDeriv ℝ n (T i j) p := by
    have hAt (i j : I) : ContDiffAt ℝ (n:ℕ∞ω) (T i j) p := (hT i j).contDiffAt.of_le (by simp)
    have hAtSum (i : I) : ContDiffAt ℝ (n:ℕ∞ω) (fun t => ∑ j : I,T i j t) p :=
      ContDiffAt.sum (fun j _ => hAt i j)
    calc
      _ = ∑ i : I,iteratedFDeriv ℝ n (fun t => ∑ j : I,T i j t) p :=
        iteratedFDeriv_fun_sum_apply (𝕜:=ℝ) (n:=n) (x:=p)
          (f:=fun i t => ∑ j : I,T i j t) (u:=Finset.univ) (fun i _ => hAtSum i)
      _ = _ := Finset.sum_congr rfl (fun i _ =>
        iteratedFDeriv_fun_sum_apply (𝕜:=ℝ) (n:=n) (x:=p)
          (f:=fun j t => T i j t) (u:=Finset.univ) (fun j _ => hAt i j))
  rw [hEq,hSum]
  calc
    _ ≤ ∑ i : I,‖∑ j : I,iteratedFDeriv ℝ n (T i j) p‖ := norm_sum_le _ _
    _ ≤ ∑ i : I,∑ j : I,‖iteratedFDeriv ℝ n (T i j) p‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i : I,∑ j : I,(‖forcingFromValueL (unitBallCoordinateGradientL i)‖*
        ‖unitBallCoordinateGradientL j‖)*q := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hTN i j))
    _ = _ := by simp only [weakFullDerivativeBudget,Finset.sum_mul]

lemma iteratedFDeriv_bilinear_apply_const {Q E F : Type*}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : Q → E →L[ℝ] F →L[ℝ] ℝ) (p : Q) (n : ℕ) (b : Fin n → Q) (u : E) (v : F)
    (hB : ContDiffAt ℝ ∞ B p) :
    iteratedFDeriv ℝ n (fun t => B t u v) p b = iteratedFDeriv ℝ n B p b u v := by
  let ev : (E →L[ℝ] F →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ v).comp (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) u)
  have h := ev.iteratedFDeriv_comp_left hB (i:=n) (by simp)
  exact congrArg (fun A => A b) h

theorem norm_iteratedFDeriv_commonSupportWeakEnergy_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (commonSupportWeakEnergy a ha) p‖ ≤ weakFullDerivativeBudget*q := by
  have hWD := (contDiff_commonSupportWeakEnergy a ha K hK hz).contDiffAt (x:=p)
  have hFD := (contDiff_commonSupportFullWeakEnergy a ha K hK hz).contDiffAt (x:=p)
  have hN := norm_iteratedFDeriv_commonSupportFullWeakEnergy_le a ha K hK hz p n q hq hJet
  have hC : 0 ≤ weakFullDerivativeBudget*q := mul_nonneg weakFullDerivativeBudget_nonneg hq
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro b
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  intro u v
  have hEq : (fun t => commonSupportWeakEnergy a ha t u v) =
      (fun t => commonSupportFullWeakEnergy a ha t u (v:BallH1)) := by
    funext t
    exact congrArg (fun L : BallH1 →L[ℝ] StrongDual ℝ BallH1Zero => L u v)
      (commonSupportWeakEnergy_restriction a ha t)
  have hAt := congrArg (fun f : P → ℝ => iteratedFDeriv ℝ n f p b) hEq
  have hLeft := iteratedFDeriv_bilinear_apply_const (commonSupportWeakEnergy a ha) p n b u v hWD
  have hRight := iteratedFDeriv_bilinear_apply_const (commonSupportFullWeakEnergy a ha) p n b u (v:BallH1) hFD
  have hPoint := hLeft.symm.trans (hAt.trans hRight)
  refine (congrArg norm hPoint).le.trans ?_
  exact (ContinuousLinearMap.le_opNorm₂ (iteratedFDeriv ℝ n (commonSupportFullWeakEnergy a ha) p b) u (v:BallH1)).trans
    (by have h := ((iteratedFDeriv ℝ n (commonSupportFullWeakEnergy a ha) p).le_opNorm b).trans
          (mul_le_mul_of_nonneg_right hN (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))

theorem norm_iteratedFDeriv_commonSupportZeroWeakEnergy_le
    (a : P × X → Mat) (ha : ContDiff ℝ ∞ a) (K : Set X) (hK : IsCompact K)
    (hz : ∀ p z,z ∉ K → a (p,z) = 0) (p : P) (n : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hJet : ∀ i j : I,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ 0 (fun z => a (t,z) i j) x) p‖ ≤ q) :
    ‖iteratedFDeriv ℝ n (commonSupportZeroWeakEnergy a ha) p‖ ≤ weakFullDerivativeBudget*q := by
  have hZD := (contDiff_commonSupportZeroWeakEnergy a ha K hK hz).contDiffAt (x:=p)
  have hWD := (contDiff_commonSupportWeakEnergy a ha K hK hz).contDiffAt (x:=p)
  have hN := norm_iteratedFDeriv_commonSupportWeakEnergy_le a ha K hK hz p n q hq hJet
  have hC : 0 ≤ weakFullDerivativeBudget*q := mul_nonneg weakFullDerivativeBudget_nonneg hq
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro b
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
  intro u v
  have hEq : (fun t => commonSupportZeroWeakEnergy a ha t u v) =
      (fun t => commonSupportWeakEnergy a ha t (u:BallH1) v) := by
    funext t
    exact congrArg (fun L : BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero => L u v)
      (commonSupportZeroWeakEnergy_restriction a ha t)
  have hAt := congrArg (fun f : P → ℝ => iteratedFDeriv ℝ n f p b) hEq
  have hLeft := iteratedFDeriv_bilinear_apply_const (commonSupportZeroWeakEnergy a ha) p n b u v hZD
  have hRight := iteratedFDeriv_bilinear_apply_const (commonSupportWeakEnergy a ha) p n b (u:BallH1) v hWD
  have hPoint := hLeft.symm.trans (hAt.trans hRight)
  refine (congrArg norm hPoint).le.trans ?_
  exact (ContinuousLinearMap.le_opNorm₂ (iteratedFDeriv ℝ n (commonSupportWeakEnergy a ha) p b) (u:BallH1) v).trans
    (by have h := ((iteratedFDeriv ℝ n (commonSupportWeakEnergy a ha) p).le_opNorm b).trans
          (mul_le_mul_of_nonneg_right hN (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (norm_nonneg u)) (norm_nonneg v))

end ShrinkingSpheres
