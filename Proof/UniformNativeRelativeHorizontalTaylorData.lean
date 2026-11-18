import Proof.UniformNormalFrameHorizontalThirdJets
import Proof.NormalFrameRelativeResponsePacket
import Proof.NativeClosedMovingMultiplierSmoothness
import Proof.UniformNormalFrameRelativeCoframeKernelJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
local instance : CompleteSpace (SphereSobolev (1/2:ℝ)) := lp.completeSpace
local instance : CompleteSpace (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) := by infer_instance

def NormalFrameRelativeHorizontalTaylorBounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : Data) (y : X) (F : NormalFrameRelativeParameter → E) (C : ℝ) : Prop :=
  ∀ a : ℕ → X,(∀ j,‖a j‖ ≤ 1) → ∀ n : ℕ,n ≤ 3 →
    ‖orderedDirectionalFamily (fun j => normalFrameRelativeHorizontalField d.γ d.radius (a j)) F n
      ((y,frameVectorLinear d.frame y),0)‖ ≤ C*(d.radius y)^2*(beta d.γ d.radius y)^n

def NormalFrameRelativeCoefficientJetFamily.coframeKernel
    {Y Ω : Set X} {d : Data} {y : X} {N : ℕ} {Z C : ℝ}
    (q : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
      (frameVectorLinear d.frame y) (d.radius y) N Z C)
    (F0 : SmoothCoefficientMatrix 2) (Q : SmoothCoefficientJets 3) (v : X) (j : I)
    (p : NormalFrameRelativeParameter) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
  commonSupportNativeClosedMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
    q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y) p
    (normalFrameRelativeClosedCoframeMultiplier Q d.γ v j p)

structure NativeRelativeHorizontalTaylorData (Y Ω : Set X) (d : Data) (y : X)
    (F0 : SmoothCoefficientMatrix 2) (CQ CI CW CF CA CM : ℝ) where
  coefficients : NormalFrameRelativeCoefficientJetFamily Y Ω d.γ d.g₁ d.expMap y
    (frameVectorLinear d.frame y) (d.radius y) 4 2 CQ
  point : NormalFrameRelativeNativePointData coefficients F0 CI CW
  response : NormalFrameRelativeResponsePacket coefficients
  forwardJoint : ∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n response.forwardTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CF*(d.radius y)^2
  adjointJoint : ∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n response.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2
  forwardHorizontal : NormalFrameRelativeHorizontalTaylorBounds d y response.forwardTaylor CF
  adjointHorizontal : NormalFrameRelativeHorizontalTaylorBounds d y response.adjointTaylor CA
  coframeHorizontal : ∀ (Q : SmoothCoefficientJets 3) (v : X) (j : I),
    NormalFrameRelativeHorizontalTaylorBounds d y (coefficients.coframeKernel F0 Q v j) (CM*‖v‖*‖Q‖)

/-- One genuine coefficient family, one response and its true adjoint have
    simultaneous joint and actual horizontal Taylor bounds. The moving
    geometric coframe commutator uses precisely the same native witnesses. -/
theorem uniform_native_relative_horizontal_taylor_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω) {m : ℕ} (hm : 8 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CF CA CM CQ CI CW : ℝ,∃ F0 : SmoothCoefficientMatrix 2,
      0 < η ∧ η ≤ 1 ∧ 1 ≤ CF ∧ 1 ≤ CA ∧ 1 ≤ CM ∧ 1 ≤ CQ ∧ 0 ≤ CI ∧ 0 ≤ CW ∧
      (∀ z ∈ Metric.closedBall (0:X) 2,coefficientMatrixField 2 F0 z = 1) ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      Nonempty (NativeRelativeHorizontalTaylorData Y Ω d y F0 CQ CI CW CF CA CM) := by
  obtain ⟨η,CF,CA,CQ,CI,CW,F0,hη,hη1,hCF,hCA,hCQ,hCI,hCW,hF0,hNative⟩ :=
    uniform_normalFrameRelative_forward_adjoint_higher_jets hY hΩ 3 (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨CH,hCH,hHorizontal⟩ := uniform_normalFrame_horizontal_third_jets hY hΩ hSub (by omega) K M Cj hK
  obtain ⟨CM,hCM,hCoframe⟩ := uniform_normalFrameRelative_coframe_kernel_higher_jets (Y:=Y) hΩ 3 (by omega)
    K M hK F0 hF0 CI CW CQ hCI hCW (zero_le_one.trans hCQ)
  obtain ⟨CC,hCC,hCoframeSmooth⟩ := uniform_normalFrameRelativeClosedCoframe_higher_jets hΩ 3 (by omega) K M hK
  have hCH0 : 0 ≤ CH := zero_le_one.trans hCH
  have hCF0 : 0 ≤ CF := zero_le_one.trans hCF
  have hCA0 : 0 ≤ CA := zero_le_one.trans hCA
  have hCM0 : 0 ≤ CM := zero_le_one.trans hCM
  refine ⟨η,CH*CF,CH*CA,CH*CM,CQ,CI,CW,F0,hη,hη1,
    (by nlinarith only [mul_le_mul hCH hCF zero_le_one hCH0]),
    (by nlinarith only [mul_le_mul hCH hCA zero_le_one hCH0]),
    (by nlinarith only [mul_le_mul hCH hCM zero_le_one hCH0]),hCQ,hCI,hCW,hF0,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨q,t,V,hV,hpV,hSubV,R,hR,hRestrict,hInv,hDa,⟨hFS,hFJ⟩,hAJ⟩ :=
    hNative floor hf ε hε hSmall d hd y hy
  let s : NormalFrameRelativeResponsePacket q := ⟨V,hV,hpV,hSubV,R,hR,hRestrict,hInv,hDa⟩
  have hFS' : ContDiffAt ℝ ∞ s.forwardTaylor ((y,frameVectorLinear d.frame y),0) := hFS
  have hFJ' : ∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n s.forwardTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CF*(d.radius y)^2 := hFJ
  have hAJ' : ∀ n : ℕ,n ≤ 3 → ‖iteratedFDeriv ℝ n s.adjointTaylor ((y,frameVectorLinear d.frame y),0)‖ ≤ CA*(d.radius y)^2 := hAJ
  have hp := hd.2.2.2.2.1
  have hr : 0 < d.radius y := (hp.2 y hy).1
  have hrε : d.radius y ≤ ε := (radius_bounds (d.radius y) (beta d.γ d.radius y) floor ε hr.le hf
    (hp.2 y hy).2.1 (hd.2.2.2.2.2 y hy).2).2.2
  have hr1 : d.radius y ≤ 1 := hrε.trans (hSmall.trans hη1)
  have hFH := hHorizontal d hd.1 floor c₀ hf hp y hy (SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    s.forwardTaylor hFS' CF (d.radius y) hCF0 hFJ'
  have hAH := hHorizontal d hd.1 floor c₀ hf hp y hy (SphereSobolev 1 →L[ℝ] SphereSobolev 0)
    s.adjointTaylor s.contDiffAt_adjointTaylor CA (d.radius y) hCA0 hAJ'
  refine ⟨⟨q,t,s,?_,?_,?_,?_,?_⟩⟩
  · intro n hn
    exact (hFJ' n hn).trans (mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_right hCH hCF0]) (sq_nonneg _))
  · intro n hn
    exact (hAJ' n hn).trans (mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_right hCH hCA0]) (sq_nonneg _))
  · intro a ha n hn
    exact (hFH a ha n hn).trans_eq (by ring)
  · intro a ha n hn
    exact (hAH a ha n hn).trans_eq (by ring)
  · intro Q v j
    have he (i k : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
        (frameVectorLinear d.frame y (axis k)) = if i=k then 1 else 0 := by
      simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hSub hy) i k
    have hQS := (hCoframeSmooth d.γ d.g₁ d.g₂ d.frame hd.1 y (hSub hy) (frameVectorLinear d.frame y) he Q v j).1
    have hKS : ContDiffAt ℝ ∞ (q.coframeKernel F0 Q v j) ((y,frameVectorLinear d.frame y),0) :=
      contDiffAt_commonSupportNativeClosedMovingMultiplierKernel q.a q.a1 q.smooth q.firstSmooth
        q.support q.support q.compact q.compact q.supported q.firstSupported F0 (d.radius y)
        ((y,frameVectorLinear d.frame y),0) t.strong t.weak (normalFrameRelativeClosedCoframeMultiplier Q d.γ v j) hQS
    have hKJ (n : ℕ) (hn : n ≤ 3) : ‖iteratedFDeriv ℝ n (q.coframeKernel F0 Q v j)
        ((y,frameVectorLinear d.frame y),0)‖ ≤ (CM*‖v‖*‖Q‖)*(d.radius y)^2 :=
      hCoframe d hd.1 y (hSub hy) 2 le_rfl q t hr.le hr1 Q v j n hn
    intro a ha n hn
    have hh := hHorizontal d hd.1 floor c₀ hf hp y hy (SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
      (q.coframeKernel F0 Q v j) hKS (CM*‖v‖*‖Q‖) (d.radius y) (by positivity) hKJ a ha n hn
    exact hh.trans_eq (by ring)

end ShrinkingSpheres
