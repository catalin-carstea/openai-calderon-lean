import Proof.UniformEffectiveFirstBalancedDerivative
import Proof.UniformEffectiveFirstAdjointDerivativePair

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- Complete first strong-half covariant jets, fixed through genuine
coarse squares before every test. -/
structure EffectiveFirstCoarseStrongHalfTwoJets
    {Y : Set X} {d : Data} {CF CT : ℝ} (P : PhysicalPrincipalData Y d CF CT) (CE ε : ℝ) where
  coarse : I → I → X → SphereSobolev 1 →L[ℝ] SphereSobolev 0
  low : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  coarse_smooth : ∀ b i,ContDiffOn ℝ ∞ (coarse b i) Y
  low_smooth : ∀ b i,ContDiffOn ℝ ∞ (low b i) Y
  first_graph : ∀ b i y,y ∈ Y →
    CoarseCovariantRotationGraph d y (axis i) (P.firstCovariantCoordinateCoarseL b) (coarse b i y)
  first_compatible : ∀ b i y,y ∈ Y →
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp (coarse b i y)=
      (low b i y).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num))
  first_norm : ∀ b i y,y ∈ Y → ‖low b i y‖ ≤ CE*ε
  second : ∀ b i j y,y ∈ Y →
    ∃ T : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
    ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      CoarseCovariantRotationGraph d y (axis j) (coarse b i) T ∧
      (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp T=
        N.comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) ∧
      ‖N‖ ≤ CE*ε*beta d.γ d.radius y

/-- Only the FORWARD higher graph is needed after moving the first
adjoint jet across the pairing. No second higher-adjoint norm is assumed. -/
structure EffectiveFirstForwardStrongHalfTwoJets
    {Y : Set X} {d : Data} {CF CT CB CS ε : ℝ} {P : PhysicalPrincipalData Y d CF CT}
    (WF : PhysicalFirstCommutatorPacket P CB CS ε) (CE : ℝ) where
  low : I → I → X → SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))
  higher : I → I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)
  low_smooth : ∀ b i,ContDiffOn ℝ ∞ (low b i) Y
  adjoint_graph : ∀ b i y,y ∈ Y → WF.covariantCoordinateAdjointDerivative b i y=
    (low b i y).adjoint.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  higher_graph : ∀ b i y,y ∈ Y →
    (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (higher b i y)=
      (low b i y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))
  low_norm : ∀ b i y,y ∈ Y → ‖low b i y‖ ≤ CE*ε
  second : ∀ b i j y,y ∈ Y →
    ∃ N : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      halfOperatorCovariantDerivativeL d (low b i) (higher b i) y (axis j)=
        N.comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) ∧
      ‖N‖ ≤ CE*ε*beta d.γ d.radius y

/-- Transfer a complete coherent coarse/half two-jet packet to the SAME
physical WF. HIGH is used only by its genuine coarse graph. -/
def forward_strong_half_two_jets_of_coarse
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CE : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (P : PhysicalPrincipalData Y d CF CT) (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (p : EffectiveFirstCoarseStrongHalfTwoJets P CE ε)
    (higher : I → I → X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hHigher : ∀ b i y,y ∈ Y →
      (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (higher b i y)=
        (p.coarse b i y).comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)))
    (hP : ∀ b y,y ∈ Y →
      (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (P.firstCovariantCoordinateHigherL b y)=
        (P.firstCovariantCoordinateHalfL b y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hW : ∀ b,ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) :
    EffectiveFirstForwardStrongHalfTwoJets WF CE := by
  refine ⟨p.low,higher,p.low_smooth,?_,?_,p.first_norm,?_⟩
  · intro b i y hy
    have hCoarseS : ContDiffOn ℝ ∞ (P.firstCovariantCoordinateCoarseL b) Y :=
      (P.firstDerivativeCoordinateCoarse_smooth hd hY hΩ (fun x hx => hd.2.1.center_mem hx) hK b).sub
        ((hW b).smul contDiffOn_const)
    have hLowS := P.firstCovariantCoordinateHalfL_smooth hd hY hΩ hK b (hW b)
    have hCoarse := P.firstCovariantCoordinate_covariant_eq_coarse hd hY hΩ hK b (hW b)
      hCoarseS hy (axis i) (P.firstCovariantCoordinateHigherL b) (hP b y hy)
      (p.coarse b i y) (p.first_graph b i y hy)
    have hD : halfOperatorCovariantDerivativeL d (P.firstCovariantCoordinateHalfL b)
        (P.firstCovariantCoordinateHigherL b) y (axis i)=
        (p.low b i y).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
      rw [hCoarse]
      apply ContinuousLinearMap.ext
      intro u
      have hh := DFunLike.congr_fun (p.first_compatible b i y hy)
        (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
      simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh
    exact half_covariant_adjoint_strong_extension d (P.firstCovariantCoordinateHalfL b)
      (P.firstCovariantCoordinateHigherL b) (WF.covariantCoordinateAdjointHigher b)
      (hLowS.contDiffAt (hY.mem_nhds hy)) (axis i) (hP b y hy)
      (WF.covariantCoordinateAdjointHigher_balanced b hy) (p.low b i y) hD
  · intro b i y hy
    apply ContinuousLinearMap.ext
    intro u
    have hH := DFunLike.congr_fun (hHigher b i y hy) u
    have hL := DFunLike.congr_fun (p.first_compatible b i y hy)
      (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num) u)
    have hh := congrArg (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)) hH
    simpa only [ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply] using hh.trans hL
  · intro b i j y hy
    obtain ⟨T,N,hT,hN,hNN⟩ := p.second b i j y hy
    refine ⟨N,halfOperatorCovariantDerivativeL_eq_strong_extension (p.coarse b i)
      (p.low b i) (higher b i) T N
      (((p.coarse_smooth b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (((p.low_smooth b i).contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
      (by filter_upwards [hY.mem_nhds hy] with x hx;exact p.first_compatible b i x hx)
      (hHigher b i y hy) hT hN,hNN⟩

end ShrinkingSpheres.ParallelEnergy
