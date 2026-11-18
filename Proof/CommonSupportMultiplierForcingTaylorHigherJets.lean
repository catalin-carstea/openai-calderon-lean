import Proof.ClosedMultiplierForcingHigherJets
import Proof.CommonSupportClosedAffineCoefficientFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Gradient BoundedContinuousFunction Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

attribute [local irreducible] nativeBulkMultiplierCommutatorForcingL

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The native forcing Taylor error retains every parameter derivative of
    the local true coefficient remainder, for the same chosen multiplier. -/
theorem norm_iteratedFDeriv_commonSupport_nativeBulkMultiplierForcing_affine_remainder_le
    (a a1 aD : P × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ t z,z ∉ S → a (t,z) = 0) (hz1 : ∀ t z,z ∉ S1 → a1 (t,z) = 0)
    (r : ℝ) (hField : ∀ p,aD p = a p-r • a1 p)
    (F0 : SmoothCoefficientMatrix 2) (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (p : P) (Q : SmoothCoefficientJets 3) (n : ℕ) (q B : ℝ) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (hJets : ∀ i j : I,∀ k : Fin 2,∀ x ∈ (ballOpens:Set X),
      ‖iteratedFDeriv ℝ n (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) p‖ ≤ q)
    (hQ1 : ∀ j,∀ z ∈ (ballOpens:Set X),|(gradient (coefficientValue 3 Q) z) j| ≤ B)
    (hQ2 : ∀ j,∀ z ∈ (ballOpens:Set X),‖gradient (fun w => (gradient (coefficientValue 3 Q) w) j) z‖ ≤ B) :
    let F := commonSupportMatrixFamily 2 a ha S hS hz
    let F1 := commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1
    ‖iteratedFDeriv ℝ n (fun t =>
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q-
      r • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q) p‖ ≤
        (270*nativeMultiplierForcingGradientBudget*B)*q := by
  intro F F1
  let C := commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r
  have hC : ContDiffAt ℝ ∞ C p :=
    (contDiff_commonSupportClosedAffineCoefficientFamily a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r).contDiffAt
  have hIncl (t : P) : C t = smoothCoefficientMatrixClosureInclusionL 2 (F t-F0-r • F1 t) := by
    rw [(smoothCoefficientMatrixClosureInclusionL 2).map_sub,
      (smoothCoefficientMatrixClosureInclusionL 2).map_sub,(smoothCoefficientMatrixClosureInclusionL 2).map_smul]
    rfl
  have hFieldJet (i j : I) (k : Fin 2) (x : X) (hx : x ∈ (ballOpens:Set X)) :
      (fun t => (C t i j).val ⟨k.val,by omega⟩ x) =
        (fun t => iteratedFDeriv ℝ k.val (fun z => (aD (t,z)-(1:Mat)) i j) x) := by
    exact commonSupportClosedAffineCoefficientFamily_jet_value a a1 aD ha ha1
      S S1 hS hS1 hz hz1 F0 r hField hFlat i j k x hx
  have hNativeEq : (fun t =>
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F t) (fun _ => 0) Q-
      nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus F0 (fun _ => 0) Q-
      r • nativeBulkMultiplierCommutatorForcingL fixedSobolevCalculus (F1 t) (fun _ => 0) Q) =
      fun t => closedNativeBulkMultiplierForcingL (C t) Q := by
    funext t
    have hs := congrArg₂ (fun A B : BallH1 →L[ℝ] BallSobolev 0 => A-B)
      (closedNativeBulkMultiplierForcingL_eq_on_smooth (F t) Q).symm
      (closedNativeBulkMultiplierForcingL_eq_on_smooth F0 Q).symm
    have hResult := congrArg₂ (fun A B : BallH1 →L[ℝ] BallSobolev 0 => A-r • B) hs
      (closedNativeBulkMultiplierForcingL_eq_on_smooth (F1 t) Q).symm
    have hLinear : closedNativeBulkMultiplierForcingL (C t) Q =
        closedNativeBulkMultiplierForcingL (smoothCoefficientMatrixClosureInclusionL 2 (F t)) Q-
        closedNativeBulkMultiplierForcingL (smoothCoefficientMatrixClosureInclusionL 2 F0) Q-
        r • closedNativeBulkMultiplierForcingL (smoothCoefficientMatrixClosureInclusionL 2 (F1 t)) Q := by
      let LQ : ClosedCoefficientMatrix 2 →L[ℝ] (BallH1 →L[ℝ] BallSobolev 0) :=
        (ContinuousLinearMap.apply ℝ (BallH1 →L[ℝ] BallSobolev 0) Q).comp closedNativeBulkMultiplierForcingL
      let G := smoothCoefficientMatrixClosureInclusionL 2 (F t)
      let G0 := smoothCoefficientMatrixClosureInclusionL 2 F0
      let G1 := smoothCoefficientMatrixClosureInclusionL 2 (F1 t)
      change LQ (G-G0-r • G1) = LQ G-LQ G0-r • LQ G1
      have h1 := LQ.map_sub (G-G0) (r • G1)
      have h2 := LQ.map_sub G G0
      have h3 := LQ.map_smul r G1
      exact h1.trans (congrArg₂ (fun A B : BallH1 →L[ℝ] BallSobolev 0 => A-B) h2 h3)
    exact hResult.trans hLinear.symm
  rw [hNativeEq]
  apply norm_iteratedFDeriv_closedNativeBulkMultiplierForcing_le C p hC Q n q B hq hB _ hQ1 hQ2
  intro i j k x hx
  rw [hFieldJet i j k x hx]
  exact hJets i j k x hx

end ShrinkingSpheres
