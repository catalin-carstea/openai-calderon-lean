import Proof.DenseIsometryOperatorExtension
import Proof.CommonSupportMovingMultiplierHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
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
local instance : CompleteSpace (SphereSobolev (1/2:ℝ)) := lp.completeSpace
local instance : CompleteSpace (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) := by infer_instance
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

def commonSupportNativeClosedMultiplierKernel
    (a a1 : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2) (r : ℝ) (p : P) :
    ClosedCoefficientJets 3 →L[ℝ] (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :=
  (commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p).extend
    (smoothCoefficientClosureInclusionL 3)

theorem commonSupport_native_moving_closed_multiplier_kernel_taylor_higher_jets
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1) (haD : ContDiff ℝ ∞ aD)
    (S S1 SD : Set X) (hS : IsCompact S) (hS1 : IsCompact S1) (hSD : IsCompact SD)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (hzD : ∀ t z,z ∉ SD → aD (t,z) = 0) (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (F0 : SmoothCoefficientMatrix 2) (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (N : ℕ) (Q : P → ClosedCoefficientJets 3) (hQ : ContDiffAt ℝ ∞ Q p) (CI C0 CW CW0 qA P1 QR BQ : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hCW : 0 ≤ CW) (hCW0 : 0 ≤ CW0) (hBQ : 0 ≤ BQ)
    (hCI : 0 ≤ CI) (hC0 : 0 ≤ C0) (hqA : 0 ≤ qA) (hP1 : 0 ≤ P1) (hQR : 0 ≤ QR)
    (hInv : (strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).IsInvertible)
    (hInv0 : (strongDirichletOperator fixedSobolevCalculus 0 F0).IsInvertible)
    (hNI : ‖(strongDirichletOperator fixedSobolevCalculus 0 (commonSupportMatrixFamily 2 a ha S hS hz p)).inverse‖ ≤ CI)
    (hNI0 : ‖(strongDirichletOperator fixedSobolevCalculus 0 F0).inverse‖ ≤ C0)
    (hWeak : (commonSupportZeroWeakEnergy a ha p).IsInvertible)
    (hWeak0 : (nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).IsInvertible)
    (hNW : ‖(commonSupportZeroWeakEnergy a ha p).inverse‖ ≤ CW)
    (hNW0 : ‖(nativeZeroCoefficientEnergyL (fun _ : X => (1:ℝ) • (1:Mat)) 0 0 (flatCoefficientBound 1)).inverse‖ ≤ CW0)
    (hAJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a (t,z) i j) x) p‖ ≤ qA)
    (hFirstJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => a1 (t,z) i j) x) p‖ ≤ P1)
    (hRemainderJets : ∀ l : ℕ,l ≤ N → ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ l (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ QR*r^2)
    (hQJets : ∀ l : ℕ,l ≤ N → ‖iteratedFDeriv ℝ l Q p‖ ≤ BQ) :
    ∀ n : ℕ,n ≤ N → ‖iteratedFDeriv ℝ n (fun t =>
      commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r t (Q t)) p‖ ≤
      (2^N*(2^N*|nativeMultiplierKernelLinearJetBudget N F0 CI C0 CW CW0 qA P1 QR|)*BQ)*r^2 := by
  let L := commonSupportNativeMultiplierKernelInMultiplierL a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r
  let C := 2^N*|nativeMultiplierKernelLinearJetBudget N F0 CI C0 CW CW0 qA P1 QR|
  have hC : 0 ≤ C := by dsimp only [C];positivity
  have hL : ContDiffAt ℝ ∞ L p := contDiffAt_commonSupportNativeMultiplierKernelInMultiplierL
    a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p hInv hWeak
  have hFixed (j : ℕ) (hj : j ≤ N) (u : SmoothCoefficientJets 3) :
      ‖iteratedFDeriv ℝ j (fun t => L t u) p‖ ≤ C*‖u‖*r^2 := by
    have hConst (l : ℕ) (_hl : l ≤ N) : ‖iteratedFDeriv ℝ l (fun _ : P => u) p‖ ≤ ‖u‖ := by
      cases l with
      | zero => simp only [norm_iteratedFDeriv_zero,le_refl]
      | succ l => simpa only [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero l),Pi.zero_apply,norm_zero] using norm_nonneg u
    exact commonSupport_native_moving_multiplier_kernel_taylor_higher_jets
      a a1 aD ha ha1 haD S S1 SD hS hS1 hSD hz hz1 hzD r hField F0 hFlat p N (fun _ => u) contDiffAt_const
      CI C0 CW CW0 qA P1 QR ‖u‖ hr hr1 hCW hCW0 (norm_nonneg _) hCI hC0 hqA hP1 hQR
      hInv hInv0 hNI hNI0 hWeak hWeak0 hNW hNW0 hAJets hFirstJets hRemainderJets hConst j hj
  intro n hn
  exact norm_iteratedFDeriv_moving_extended_linear_family_le (smoothCoefficientClosureInclusionL 3)
    (denseRange_smoothCoefficientClosureInclusionL 3) (fun _ _ => rfl)
    L Q p hL hQ N r C BQ hC hBQ hFixed hQJets n hn

end ShrinkingSpheres
