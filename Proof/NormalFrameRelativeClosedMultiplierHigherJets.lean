import Proof.CommonSupportClosedMovingMultiplierHigherJets
import Proof.NormalFrameRelativeNativePointData

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Any completed moving multiplier is estimated for the SAME genuine
    coefficient representative and the SAME native point inverses. -/
theorem NormalFrameRelativeCoefficientJetFamily.native_closed_multiplier_higher_jets
    {Y Ω : Set X} {d : Data} {y : X} (N : ℕ) {Z C CI CW BQ : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) (N+1) Z C)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hBQ : 0 ≤ BQ)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (t : NormalFrameRelativeNativePointData q F0 CI CW)
    (Q : NormalFrameRelativeParameter → ClosedCoefficientJets 3)
    (hQ : ContDiffAt ℝ ∞ Q ((y,frameVectorLinear d.frame y),0))
    (hQJets : ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n Q ((y,frameVectorLinear d.frame y),0)‖ ≤ BQ) :
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun p =>
      commonSupportNativeClosedMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
        q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y) p (Q p))
        ((y,frameVectorLinear d.frame y),0)‖ ≤
      (2^N*(2^N*|nativeMultiplierKernelLinearJetBudget N F0 CI CI CW 5 C C C|)*BQ)*(d.radius y)^2 := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have hFlatB (z : X) (hz : z ∈ (ballOpens:Set X)) := hF0 z (unitBall_subset_closedBall_two hz)
  have hxZ (x : X) (hx : x ∈ (ballOpens:Set X)) : ‖x‖ ≤ Z := by
    have hh : ‖x‖ ≤ 2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using unitBall_subset_closedBall_two hx
    exact hh.trans hZ
  have hAJets (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => q.a (p,z) i j) x) p0‖ ≤ C :=
    q.coefficientMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hFirstJets (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => q.a1 (p,z) i j) x) p0‖ ≤ C :=
    q.firstMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hRemainderJets (l : ℕ) (hl : l ≤ N) (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => (q.affineCoefficient (p,z)-(1:Mat)) i j) x) p0‖ ≤ C*(d.radius y)^2 :=
    q.remainderMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hFlat := flat_native_weak_energy_data 1 (by norm_num)
  have hInv0 := nativeZeroCoefficientEnergy_isInvertible (flatCoefficientBound 1) hFlat.coercive
  have hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ 5 := by
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    change ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat))
      (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) (flatCoefficientBound 1)‖ ≤ 5
    simpa only [inv_one,mul_one] using hFlat.inverse_bound
  exact commonSupport_native_moving_closed_multiplier_kernel_taylor_higher_jets
    q.a q.a1 q.affineCoefficient q.smooth q.firstSmooth q.affineSmooth
    q.support q.support q.support q.compact q.compact q.compact q.supported q.firstSupported q.affineSupported
    (d.radius y) (fun _ => rfl) F0 hFlatB p0 N Q hQ CI CI CW 5 C C C BQ hr hr1 hCW (by norm_num)
    hBQ hCI hCI hC hC hC t.strong t.flatStrong t.strongNorm t.flatStrongNorm t.weak hInv0 t.weakNorm hNI0
    hAJets hFirstJets hRemainderJets hQJets

end ShrinkingSpheres
