import Proof.BoundaryNormalContractionJets
import Proof.NormalFrameRelativeCoefficientJetFamily
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

def normalFrameRelativeNormalScalarRemainder (d : Data) (r : ℝ) : NormalFrameRelativeParameter × X → ℝ :=
  boundaryNormalContraction (fun q => normalFrameRelativeCoefficient d.γ d.g₁ d.expMap r q-(1:Mat)-
    r • normalFrameRelativeFirstModel d.γ d.g₁ q)

structure RelativeNormalScalarRemainderFamily (d : Data) (y : X) (C : ℝ) where
  scalar : NormalFrameRelativeParameter × X → ℝ
  smooth : ContDiff ℝ ∞ scalar
  support : Set X
  compact : IsCompact support
  supported : ∀ p z,z ∉ support → scalar (p,z)=0
  domain : Set NormalFrameRelativeParameter
  isOpen : IsOpen domain
  point : ((y,frameVectorLinear d.frame y),0) ∈ domain
  actual : ∀ p ∈ domain,∀ z ∈ Metric.closedBall (0:X) 2,scalar =ᶠ[𝓝 (p,z)]
    normalFrameRelativeNormalScalarRemainder d (d.radius y)
  jets : SmoothFiniteJetBound (commonSupportClosedCoefficientFamily 3 scalar smooth support compact supported)
    ((y,frameVectorLinear d.frame y),0) 3 (C*(d.radius y)^2)

def RelativeNormalScalarRemainderFamily.closed {d : Data} {y : X} {C : ℝ}
    (R : RelativeNormalScalarRemainderFamily d y C) : NormalFrameRelativeParameter → ClosedCoefficientJets 3 :=
  commonSupportClosedCoefficientFamily 3 R.scalar R.smooth R.support R.compact R.supported

theorem uniform_relative_normal_scalar_remainder_family {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 10 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ,0 < η ∧ η ≤ 1 ∧ 1 ≤ C ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      Nonempty (RelativeNormalScalarRemainderFamily d y C) := by
  classical
  obtain ⟨η,CQ,hη,hη1,hCQ,hProduce⟩ := uniform_normalFrameRelativeCoefficient_jet_family
    hY hΩ 6 (by omega) K ρ c₀ M Cj hK hρ 4 (by norm_num)
  obtain ⟨CS,hCS,hScalar⟩ := exists_closed_boundary_normal_contraction_family (P:=NormalFrameRelativeParameter) 3
  have hC : 1 ≤ CS*CQ := by nlinarith only [mul_le_mul hCS hCQ zero_le_one (zero_le_one.trans hCS)]
  refine ⟨η,CS*CQ,hη,hη1,hC,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  let p0 : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  have he (i j : I) : metricPair d.γ y (frameVectorLinear d.frame y (axis i))
      (frameVectorLinear d.frame y (axis j))=if i=j then 1 else 0 := by
    simpa only [frameVectorLinear_apply,frameVector_axis] using hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy) i j
  obtain ⟨q⟩ := hProduce floor hf ε hε hSmall d hd y hy (frameVectorLinear d.frame y) he (d.radius y)
    (by rw [abs_of_pos (hd.2.2.2.2.1.2 y hy).1])
  let A : NormalFrameRelativeParameter × X → Mat := fun q0 => q.a q0-(1:Mat)-d.radius y • q.a1 q0
  have hA : ContDiff ℝ ∞ A := (q.smooth.sub contDiff_const).sub (q.firstSmooth.const_smul (d.radius y))
  have hAJets (j : ℕ) (hj : j ≤ 3+3) (z : X) (hz : z ∈ Metric.closedBall (0:X) 4) :
      ‖iteratedFDeriv ℝ j A (p0,z)‖ ≤ CQ*(d.radius y)^2 := by
    exact q.remainderJets z (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz) j (by omega)
  obtain ⟨b,hb,S,hS,hz,V,hV,hpV,hRep,hJets⟩ := hScalar A hA p0 (CQ*(d.radius y)^2)
    (mul_nonneg (zero_le_one.trans hCQ) (sq_nonneg _)) hAJets
  refine ⟨{
    scalar := b, smooth := hb, support := S, compact := hS, supported := hz,
    domain := q.domain ∩ V, isOpen := q.domainOpen.inter hV, point := ⟨q.pointMem,hpV⟩,
    actual := ?_, jets := ?_ }⟩
  · intro p hp z hz2
    have hz4 := Metric.closedBall_subset_closedBall (by norm_num : (2:ℝ) ≤ 4) hz2
    have hMatrix : A =ᶠ[𝓝 (p,z)] (fun q0 => normalFrameRelativeCoefficient d.γ d.g₁ d.expMap (d.radius y) q0-
        (1:Mat)-d.radius y • normalFrameRelativeFirstModel d.γ d.g₁ q0) :=
      ((q.coefficientGerm p hp.1 z hz4).sub (Filter.EventuallyEq.rfl)).sub
        ((q.firstGerm p hp.1 z hz4).const_smul (d.radius y))
    have hCon : boundaryNormalContraction A =ᶠ[𝓝 (p,z)] normalFrameRelativeNormalScalarRemainder d (d.radius y) := by
      filter_upwards [hMatrix] with q0 hq
      exact congrArg (fun B : Mat => ∑ i : I,∑ j : I,B i j*q0.2 i*q0.2 j) hq
    exact (hRep p hp.2 z hz2).trans hCon
  · convert hJets using 1 <;> ring
end ShrinkingSpheres
