import Proof.NormalFrameRelativeNativePointData
import Proof.CommonSupportMidpointNeighborhood
import Proof.CommonSupportLowRadialTaylorHigherJets
import Proof.CommonSupportStrongPoissonTaylorHigherJets
import Proof.CommonSupportRadialMidpointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
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

def NormalFrameRelativeCoefficientJetFamily.halfTaylor
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C) (p : NormalFrameRelativeParameter) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  commonSupportLowRadialErrorL q.a q.smooth q.support q.compact q.supported p-
    d.radius y • commonSupportLowFirstRadialL q.a1 q.firstSmooth q.support q.compact q.firstSupported 1 p

/-- The low half-order estimate is shared by midpoint interpolation and by
    the physical adjoint endpoint lift; all witnesses are unchanged. -/
theorem NormalFrameRelativeCoefficientJetFamily.native_half_taylor_higher_jets
    {Y Ω : Set X} {d : Data} {y : X} (N : ℕ) {Z C CI CW : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) (N+1) Z C)
    (hZ : 2 ≤ Z) (hC : 0 ≤ C) (hCW : 0 ≤ CW)
    (hr : 0 ≤ d.radius y) (hr1 : d.radius y ≤ 1)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (t : NormalFrameRelativeNativePointData q F0 CI CW) :
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n q.halfTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤
      |lowRadialTaylorJetBudget N 2 CW 5 C C C| * (d.radius y)^2 := by
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let r := d.radius y
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
      ‖iteratedFDeriv ℝ l (fun p => iteratedFDeriv ℝ k.val (fun z => (q.affineCoefficient (p,z)-(1:Mat)) i j) x) p0‖ ≤ C*r^2 :=
    q.remainderMixedJets x (hxZ x hx) l k.val (by omega) i j
  have hFlat := flat_native_weak_energy_data 1 (by norm_num)
  have hInv0 := nativeZeroCoefficientEnergy_isInvertible (flatCoefficientBound 1) hFlat.coercive
  have hNI0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ 5 := by
    rw [nativeZeroCoefficientEnergy_inverse_eq]
    change ‖nativeCoefficientWeakFunctionalInverse (fun _ : X => (1:ℝ) • (1:Mat))
      (fun _ : X => (0:X)) (fun _ : X => (0:ℝ)) (flatCoefficientBound 1)‖ ≤ 5
    simpa only [inv_one,mul_one] using hFlat.inverse_bound
  have hLow := commonSupport_low_radial_taylor_higher_jets
    q.a q.a1 q.affineCoefficient q.smooth q.firstSmooth q.affineSmooth
    q.support q.support q.support q.compact q.compact q.compact q.supported q.firstSupported q.affineSupported
    r (fun _ => rfl) F0 hF0 p0 N 2 CW 5 C C C hr hr1 (by norm_num) hCW (by norm_num) hC hC hC
    t.weak hInv0 t.weakNorm hNI0 t.normal t.normalNorm (q.firstTangentialGerm (by linarith only [hZ]))
    hAJets hFirstJets hRemainderJets
  intro n hn
  exact (hLow n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg r))

end ShrinkingSpheres
