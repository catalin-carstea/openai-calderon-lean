module

public import Proof.CalderonN.FiniteLinearizedWeakRadial
public import Proof.CalderonN.FiniteRadialResponseLinear

import Proof.CalderonN.SmoothStrongBallEstimates
import Mathlib.Tactic

/-! A common linear boundary operator for all Sobolev endpoint estimates.
Uniqueness identifies the actual response independently of extensions. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 25
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private def blendAdd (u v : SmoothData dim) : SmoothData dim := ⟨u.1+v.1,u.2.add v.2⟩
private def blendScale (c : ℝ) (u : SmoothData dim) : SmoothData dim := ⟨c • u.1,u.2.const_smul c⟩

private theorem parametric_response_germ {A G : X dim → Mat dim}
    (hA : ContDiff ℝ ∞ A) {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (b₁ b₂ w₁ w₂ : SmoothData dim)
    (hTb : EqOn b₁.1 b₂.1 (standardSphere dim)) (hTw : EqOn w₁.1 w₂.1 (standardSphere dim))
    (hb : EqOn (negativeBallDivergence A b₁.1) (negativeBallDivergence A b₂.1) (ball (0 : X dim) 1))
    (hw₁ : ∀ z ∈ ball (0 : X dim) 1,
      negativeBallDivergence A w₁.1 z = -negativeBallDivergence G b₁.1 z)
    (hw₂ : ∀ z ∈ ball (0 : X dim) 1,
      negativeBallDivergence A w₂.1 z = -negativeBallDivergence G b₂.1 z) :
    EqOn w₁.1 w₂.1 (closedBall (0 : X dim) 1) := by
  have hB := eqOn_closedUnitBall_of_equal_ball_forcing hA hEll (fun _ _ => rfl) b₁ b₂ hb hTb
  apply eqOn_closedUnitBall_of_equal_ball_forcing hA hEll (fun _ _ => rfl) w₁ w₂ _ hTw
  intro z hz
  have hG : b₁.1 =ᶠ[𝓝 z] b₂.1 := by
    filter_upwards [isOpen_ball.mem_nhds hz] with v hv using hB (ball_subset_closedBall hv)
  rw [hw₁ z hz,hw₂ z hz,negativeBallDivergence_congr_germ EventuallyEq.rfl hG]

@[expose] def finiteLinearizedRadialResponseL (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    {A G : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (b w : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hbT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hwT : ∀ f, EqOn (w f).1 0 (standardSphere dim))
    (hbH : ∀ f, EqOn (negativeBallDivergence A (b f).1) 0 (ball (0 : X dim) 1))
    (hwH : ∀ f z, z ∈ ball (0 : X dim) 1 →
      negativeBallDivergence A (w f).1 z = -negativeBallDivergence G (b f).1 z) :
    HarmonicFiniteCoefficients dim →ₗ[ℝ] SphereSobolev dim s where
  toFun f := smoothBoundarySobolev hn s hs (smoothBallRadialDerivative (w f))
  map_add' f g := by
    let b₂ := blendAdd (b f) (b g)
    let w₂ := blendAdd (w f) (w g)
    have hBT : EqOn (b (f+g)).1 b₂.1 (standardSphere dim) := by
      intro z hz
      change (b (f+g)).1 z = (b f).1 z+(b g).1 z
      rw [hbT (f+g) hz,hbT f hz,hbT g hz,← harmonicFiniteSmoothL_val,← harmonicFiniteSmoothL_val,
        ← harmonicFiniteSmoothL_val,map_add]
      rfl
    have hWT : EqOn (w (f+g)).1 w₂.1 (standardSphere dim) := by
      intro z hz
      change (w (f+g)).1 z = (w f).1 z+(w g).1 z
      rw [hwT (f+g) hz,hwT f hz,hwT g hz,Pi.zero_apply,zero_add]
    have hB : EqOn (negativeBallDivergence A (b (f+g)).1)
        (negativeBallDivergence A b₂.1) (ball (0 : X dim) 1) := by
      intro z hz
      change negativeBallDivergence A (b (f+g)).1 z = negativeBallDivergence A ((b f).1+(b g).1) z
      rw [negativeBallDivergence_add hA (b f).2 (b g).2,hbH (f+g) hz,hbH f hz,hbH g hz,Pi.zero_apply,zero_add]
    have hW (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
        negativeBallDivergence A w₂.1 z = -negativeBallDivergence G b₂.1 z := by
      change negativeBallDivergence A ((w f).1+(w g).1) z = -negativeBallDivergence G ((b f).1+(b g).1) z
      rw [negativeBallDivergence_add hA (w f).2 (w g).2,
        negativeBallDivergence_add hG (b f).2 (b g).2,hwH f z hz,hwH g z hz]
      ring
    have hAny := parametric_response_germ hA hEll (b (f+g)) b₂ (w (f+g)) w₂ hBT hWT hB (hwH _) hW
    have hRad := eqOn_radialDerivative_of_eqOn_closedUnitBall hAny
    rw [smoothBoundarySobolev_eq_of_eqOn hn s hs (smoothBallRadialDerivative (w (f+g)))
      (smoothBallRadialDerivative w₂) hRad]
    let L := (smoothBoundarySobolevLinear hn s hs).comp (smoothBallRadialDataL (dim:=dim))
    exact map_add L (⟨(w f).1,(w f).2⟩ : smoothBallDataSubmodule dim) ⟨(w g).1,(w g).2⟩
  map_smul' c f := by
    let b₂ := blendScale c (b f)
    let w₂ := blendScale c (w f)
    have hBT : EqOn (b (c • f)).1 b₂.1 (standardSphere dim) := by
      intro z hz
      change (b (c • f)).1 z = c*(b f).1 z
      rw [hbT (c • f) hz,hbT f hz,← harmonicFiniteSmoothL_val,← harmonicFiniteSmoothL_val,map_smul]
      rfl
    have hWT : EqOn (w (c • f)).1 w₂.1 (standardSphere dim) := by
      intro z hz
      change (w (c • f)).1 z = c*(w f).1 z
      rw [hwT (c • f) hz,hwT f hz,Pi.zero_apply,mul_zero]
    have hB : EqOn (negativeBallDivergence A (b (c • f)).1)
        (negativeBallDivergence A b₂.1) (ball (0 : X dim) 1) := by
      intro z hz
      change negativeBallDivergence A (b (c • f)).1 z = negativeBallDivergence A (c • (b f).1) z
      rw [negativeBallDivergence_const_smul_solution hA (b f),hbH (c • f) hz,hbH f hz,Pi.zero_apply,mul_zero]
    have hW (z : X dim) (hz : z ∈ ball (0 : X dim) 1) :
        negativeBallDivergence A w₂.1 z = -negativeBallDivergence G b₂.1 z := by
      change negativeBallDivergence A (c • (w f).1) z = -negativeBallDivergence G (c • (b f).1) z
      rw [negativeBallDivergence_const_smul_solution hA (w f),
        negativeBallDivergence_const_smul_solution hG (b f),hwH f z hz,mul_neg]
    have hAny := parametric_response_germ hA hEll (b (c • f)) b₂ (w (c • f)) w₂ hBT hWT hB (hwH _) hW
    have hRad := eqOn_radialDerivative_of_eqOn_closedUnitBall hAny
    rw [smoothBoundarySobolev_eq_of_eqOn hn s hs (smoothBallRadialDerivative (w (c • f)))
      (smoothBallRadialDerivative w₂) hRad,RingHom.id_apply]
    let L := (smoothBoundarySobolevLinear hn s hs).comp (smoothBallRadialDataL (dim:=dim))
    exact map_smul L c (⟨(w f).1,(w f).2⟩ : smoothBallDataSubmodule dim)

theorem finiteLinearizedRadialResponseL_apply (hn : 3 ≤ dim) (s : ℝ) (hs : s ≤ 2)
    {A G : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ G)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    (b w : HarmonicFiniteCoefficients dim → SmoothData dim)
    (hbT : ∀ f, EqOn (b f).1 (harmonicFiniteSmooth f).1 (standardSphere dim))
    (hwT : ∀ f, EqOn (w f).1 0 (standardSphere dim))
    (hbH : ∀ f, EqOn (negativeBallDivergence A (b f).1) 0 (ball (0 : X dim) 1))
    (hwH : ∀ f z, z ∈ ball (0 : X dim) 1 →
      negativeBallDivergence A (w f).1 z = -negativeBallDivergence G (b f).1 z)
    (f : HarmonicFiniteCoefficients dim) :
    finiteLinearizedRadialResponseL hn s hs hA hG hEll b w hbT hwT hbH hwH f =
      smoothBoundarySobolev hn s hs (smoothBallRadialDerivative (w f)) :=
  rfl

end CalderonN
