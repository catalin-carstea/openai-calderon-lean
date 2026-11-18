import Proof.NormalFrameRelativeAdjointHigherJets
import Proof.UniformNormalFrameRelativeMidpointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The same chosen genuine forward response and its true boundary adjoint
    have uniform all-finite-order quadratic Taylor jets on one open domain. -/
theorem uniform_normalFrameRelative_forward_adjoint_higher_jets {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (N : ℕ) (hNm : N+5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CA CQ CI CW : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧ 1 ≤ CQ ∧ 0 ≤ CI ∧ 0 ≤ CW ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
        (frameVectorLinear d.frame y) (d.radius y) (N+1) 2 CQ,
      NormalFrameRelativeNativePointData q F0 CI CW ∧
      ∃ V : Set NormalFrameRelativeParameter,IsOpen V ∧ ((y,frameVectorLinear d.frame y),0) ∈ V ∧ V ⊆ q.domain ∧
        ∃ R : NormalFrameRelativeParameter → SphereSobolev 1 →L[ℝ] SphereSobolev 0,
          ContDiffOn ℝ ∞ R V ∧
          (∀ p ∈ V,(R p).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
            (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp
              (actualHighRadialErrorL (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))) ∧
          (∀ p ∈ V,(oneBoundaryCoefficientMulL (normalCoefficientJet
            (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p))).IsInvertible) ∧
          (let Da := fun p => radialAdjointFromResponseL
              (commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported p) (R p+sphereSobolevDegreeL)
          ContDiffOn ℝ ∞ Da V ∧
          (let T := fun p => R p-d.radius y •
            (coarseFirstRadialVariationL 1 (normalFrameRelativeFirstCovector d.γ d.g₁ p)).comp
              (sphereSobolevInclusionL 1 0 (by norm_num))
          ContDiffAt ℝ ∞ T ((y,frameVectorLinear d.frame y),0) ∧ ∀ n : ℕ,n ≤ N →
            ‖iteratedFDeriv ℝ n T ((y,frameVectorLinear d.frame y),0)‖ ≤ CF*(d.radius y)^2) ∧
          ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p => Da p-sphereSobolevDegreeL-
            d.radius y • (radialCorrectionCovectorL (normalFrameRelativeFirstCovector d.γ d.g₁ p)).adjoint.comp
              (sphereSobolevInclusionL 1 0 (by norm_num))) ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2) := by
  obtain ⟨ηF,CF,CQ,CI,CW,F0,hηF,hηF1,hCF,hCQ,hCI,hCW,hF0,hForward⟩ :=
    uniform_normalFrameRelative_midpoint_higher_jets hY hΩ N hNm K ρ c₀ M Cj hK hρ
  let D : ℝ := 2*(18*coarseOneBoundaryBundleBudget)*CQ
  let CA : ℝ := 1+|normalFrameRelativeAdjointHigherJetBudget N CQ CF|
  have hCQ0 : 0 ≤ CQ := zero_le_one.trans hCQ
  have hCF0 : 0 ≤ CF := zero_le_one.trans hCF
  have hCB := coarseOneBoundaryBundleBudget_nonneg
  have hD : 0 ≤ D := by dsimp only [D];positivity
  have hDen : 0 < 2*(D+1) := by positivity
  have hCA : 1 ≤ CA := by dsimp only [CA];linarith only [abs_nonneg (normalFrameRelativeAdjointHigherJetBudget N CQ CF)]
  refine ⟨min ηF (2*(D+1))⁻¹,CF,CA,CQ,CI,CW,F0,lt_min hηF (inv_pos.mpr hDen),
    (min_le_left _ _).trans hηF1,hCF,hCA,hCQ,hCI,hCW,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨q,t,V,hV,hpV,hSub,R,hR,hRestrict,hT,hTJets⟩ :=
    hForward floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let F := commonSupportMatrixFamily 2 q.a q.smooth q.support q.compact q.supported
  let MOne := fun p => oneBoundaryCoefficientMulL (normalCoefficientJet (F p))
  have hr : 0 < d.radius y := (hd.2.2.2.2.1.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hd.2.2.2.2.1.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans ((min_le_left _ _).trans hηF1))
  have hrSmall : d.radius y ≤ (2*(D+1))⁻¹ := hrε.trans (hSmall.trans (min_le_right _ _))
  have hSmallD : D*d.radius y ≤ (1/2:ℝ) := by
    calc
      _ ≤ D*(2*(D+1))⁻¹ := mul_le_mul_of_nonneg_left hrSmall hD
      _ = D/(2*(D+1)) := by rw [div_eq_mul_inv]
      _ ≤ (1/2:ℝ) := (div_le_iff₀ hDen).mpr (by nlinarith only [hD])
  obtain ⟨hOneInv,hOneNorm,hAdjJets⟩ := q.native_adjoint_higher_jets N le_rfl hCQ0 hCF0 hr.le hr1 F0 hF0 t.flatStrong
    R (hR.contDiffAt (hV.mem_nhds hpV)) hTJets hSmallD
  let W := V ∩ {p | (MOne p).IsInvertible}
  have hM : ContDiff ℝ ∞ MOne := contDiff_commonSupport_oneNormalMul q.a q.smooth q.support q.compact q.supported
  have hW : IsOpen W := hV.inter (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hM.continuous)
  have hpW : p0 ∈ W := ⟨hpV,hOneInv⟩
  have hWSub : W ⊆ q.domain := fun p hp => hSub hp.1
  have hR' : ContDiffOn ℝ ∞ R W := hR.mono inter_subset_left
  have hInvW : ∀ p ∈ W,(oneBoundaryCoefficientMulL (normalCoefficientJet (F p))).IsInvertible := fun _ hp => hp.2
  have hDa : ContDiffOn ℝ ∞ (fun p => radialAdjointFromResponseL (F p) (R p+sphereSobolevDegreeL)) W :=
    contDiffOn_commonSupport_radialAdjointFromResponse q.a q.smooth q.support q.compact q.supported
      (fun p => R p+sphereSobolevDegreeL) W (hR'.add contDiffOn_const) hInvW
  refine ⟨q,t,W,hW,hpW,hWSub,R,hR',(fun p hp => hRestrict p hp.1),hInvW,hDa,⟨hT,hTJets⟩,?_⟩
  intro n hn
  exact (hAdjJets n hn).trans (mul_le_mul_of_nonneg_right
    ((le_abs_self _).trans (by dsimp only [CA];linarith)) (sq_nonneg (d.radius y)))

end ShrinkingSpheres
