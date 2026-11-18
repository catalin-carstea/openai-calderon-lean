import Proof.NormalFrameRelativeClosedCoframe
import Proof.NormalFrameRelativeClosedMultiplierHigherJets
import Proof.NativeClosedMultiplierSmoothIdentity

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
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Uniform coframe commutator bounds apply to every SAME genuine native
    representative, so later forward/adjoint callers retain their witnesses. -/
theorem uniform_normalFrameRelative_coframe_kernel_higher_jets {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K)
    (F0 : SmoothCoefficientMatrix 2)
    (hF0 : ∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1)
    (CI CW C : ℝ) (hCI : 0 ≤ CI) (hCW : 0 ≤ CW) (hC : 0 ≤ C) :
    ∃ B : ℝ,1 ≤ B ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ y ∈ Ω,∀ Z : ℝ,2 ≤ Z →
      ∀ q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
        (frameVectorLinear d.frame y) (d.radius y) (N+1) Z C,
      NormalFrameRelativeNativePointData q F0 CI CW → 0 ≤ d.radius y → d.radius y ≤ 1 →
      ∀ (Q : SmoothCoefficientJets 3) (v : X) (j : I),∀ n : ℕ,n ≤ N →
      ‖iteratedFDeriv ℝ n (fun p =>
        commonSupportNativeClosedMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
          q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y) p
          (normalFrameRelativeClosedCoframeMultiplier Q d.γ v j p)) ((y,frameVectorLinear d.frame y),0)‖ ≤
        B*‖v‖*‖Q‖*(d.radius y)^2 := by
  obtain ⟨CC,hCC,hCoframe⟩ := uniform_normalFrameRelativeClosedCoframe_higher_jets hΩ N hNm K M hK
  let A : ℝ := 2^N*(2^N*|nativeMultiplierKernelLinearJetBudget N F0 CI CI CW 5 C C C|)
  let B : ℝ := 1+A*CC
  have hA : 0 ≤ A := by dsimp only [A];positivity
  have hCC0 : 0 ≤ CC := zero_le_one.trans hCC
  have hB : 1 ≤ B := by dsimp only [B];nlinarith only [mul_nonneg hA hCC0]
  refine ⟨B,hB,?_⟩
  intro d hd y hy Z hZ q t hr hr1 Q v j n hn
  have he (i k : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis k)) = if i=k then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.2.2.2.2.2.2.2 y hy i k
  obtain ⟨hQ,hQJets⟩ := hCoframe d.γ d.g₁ d.g₂ d.frame hd y hy (frameVectorLinear d.frame y) he Q v j
  have hBQ : 0 ≤ CC*‖v‖*‖Q‖ := by positivity
  have hh := q.native_closed_multiplier_higher_jets N hZ hC hCI hCW hBQ hr hr1 F0 hF0 t
    (normalFrameRelativeClosedCoframeMultiplier Q d.γ v j) hQ hQJets n hn
  calc
    _ ≤ (A*CC)*‖v‖*‖Q‖*(d.radius y)^2 := hh.trans_eq (by dsimp only [A];ring)
    _ ≤ B*‖v‖*‖Q‖*(d.radius y)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg Q)
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      dsimp only [B]
      linarith

/-- The completed coframe kernel is exactly the supplied actual Taylor
    commutator, pointwise with its original coefficient witnesses. -/
theorem normalFrameRelative_coframe_kernel_eq_actual_commutator
    (a a1 : NormalFrameRelativeParameter × X → Mat) (ha : ContDiff ℝ ∞ a) (ha1 : ContDiff ℝ ∞ a1)
    (S S1 : Set X) (hS : IsCompact S) (hS1 : IsCompact S1)
    (hz : ∀ p z,z ∉ S → a (p,z) = 0) (hz1 : ∀ p z,z ∉ S1 → a1 (p,z) = 0)
    (F0 : SmoothCoefficientMatrix 2)
    (hFlat : ∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F0 z = 1)
    (hMem : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a ha S hS hz t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hMem1 : ∀ t,MemLp (fun z => TauCeti.PDE.energyIntegrand
      (coefficientMatrixField 2 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 t) z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (hMem0 : MemLp (fun z => TauCeti.PDE.energyIntegrand (coefficientMatrixField 2 F0 z) 0 0) ⊤
      ((volume:Measure X).restrict ballOpens))
    (Q : SmoothCoefficientJets 3) (g : MetricField) (v : X) (j : I) (r : ℝ) :
    (fun p => commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p
      (normalFrameRelativeClosedCoframeMultiplier Q g v j p)) =
    (fun p => radialTaylorMultiplierCommutatorL
      (commonSupportMatrixFamily 2 a ha S hS hz p) F0 (commonSupportMatrixFamily 2 a1 ha1 S1 hS1 hz1 p)
      (hMem p) hMem0 (hMem1 p) (normalFrameRelativeCoframeValue g v j p • Q) r) := by
  funext p
  change commonSupportNativeClosedMultiplierKernel a a1 ha ha1 S S1 hS hS1 hz hz1 F0 r p
    (normalFrameRelativeCoframeValue g v j p • smoothCoefficientClosureInclusionL 3 Q) = _
  rw [← (smoothCoefficientClosureInclusionL 3).map_smul,commonSupportNativeClosedMultiplierKernel_on_smooth]
  exact (congrFun (commonSupport_moving_multiplier_commutator_eq_curried_kernel a a1 ha ha1 S S1 hS hS1 hz hz1
    F0 hFlat hMem hMem1 hMem0 (fun t => normalFrameRelativeCoframeValue g v j t • Q) r) p).symm

end ShrinkingSpheres
