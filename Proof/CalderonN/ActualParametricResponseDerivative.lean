module

public import Proof.CalderonN.ParametricBallLinearization
public import Proof.CalderonN.FixedBallFluxUnique

import Mathlib.Tactic

/-! On the actual joint solution family, the parameter derivative is
the unique solution of the linearized zero-Dirichlet problem. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem actualBallParameterDerivative_zeroDirichlet
    {a : ℝ × X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {B : ℝ × X dim → ℝ} (hB : ContDiff ℝ ∞ B) (u : X dim → ℝ)
    (hEq : ∀ᶠ t : ℝ in 𝓝 0,
      EqOn (fun z => B (t,z)) u (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun z => a (t,z)) (fun z => B (t,z))) 0 (ball (0 : X dim) 1)) :
    let b : SmoothData dim := ⟨fun z => B (0,z),hB.comp (contDiff_const.prodMk contDiff_id)⟩
    let w : SmoothData dim := ⟨fun z => ballParameterDerivative B (0,z),
      (contDiff_ballParameterDerivative hB).comp (contDiff_const.prodMk contDiff_id)⟩
    EqOn b.1 u (standardSphere dim) ∧
    EqOn (negativeBallDivergence (fun z => a (0,z)) b.1) 0 (ball (0 : X dim) 1) ∧
    EqOn w.1 0 (standardSphere dim) ∧
    (∀ z ∈ ball (0 : X dim) 1,
      negativeBallDivergence (fun z => a (0,z)) w.1 z =
        -negativeBallDivergence (fun z => ballParameterDerivative a (0,z)) b.1 z) := by
  dsimp only
  refine ⟨hEq.self_of_nhds.1,hEq.self_of_nhds.2,?_,?_⟩
  · intro z hz
    have hConst : (fun t => B (t,z)) =ᶠ[𝓝 (0:ℝ)] fun _ => u z := by
      filter_upwards [hEq] with t ht using ht.1 hz
    exact (hasDerivAt_ballParameterDerivative hB (0,z)).unique
      ((hasDerivAt_const (0:ℝ) (u z)).congr_of_eventuallyEq hConst)
  · intro z hz
    have hConst : (fun t => negativeBallDivergence (fun z => a (t,z)) (fun z => B (t,z)) z)
        =ᶠ[𝓝 (0:ℝ)] fun _ => 0 := by
      filter_upwards [hEq] with t ht using ht.2 hz
    have h := (hasDerivAt_negativeBallDivergence_family ha hB 0 z).unique
      ((hasDerivAt_const (0:ℝ) (0:ℝ)).congr_of_eventuallyEq hConst)
    exact eq_neg_of_add_eq_zero_left h

theorem hasDerivAt_actualBallRadialResponse_of_linearized
    {a : ℝ × X dim → Mat dim} (ha : ContDiff ℝ ∞ a)
    {B : ℝ × X dim → ℝ} (hB : ContDiff ℝ ∞ B) (u : X dim → ℝ)
    (hEq : ∀ᶠ t : ℝ in 𝓝 0,
      EqOn (fun z => B (t,z)) u (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun z => a (t,z)) (fun z => B (t,z))) 0 (ball (0 : X dim) 1))
    {lo hi : ℝ}
    (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) (fun z => a (0,z)) lo hi)
    {A G : X dim → Mat dim}
    (hA : EqOn (fun z => a (0,z)) A (ball (0 : X dim) 1))
    (hG : EqOn (fun z => ballParameterDerivative a (0,z)) G (ball (0 : X dim) 1))
    (b w : SmoothData dim)
    (hbT : EqOn b.1 u (standardSphere dim)) (hwT : EqOn w.1 0 (standardSphere dim))
    (hbH : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hwH : ∀ z ∈ ball (0 : X dim) 1, negativeBallDivergence A w.1 z = -negativeBallDivergence G b.1 z) :
    ∀ z ∈ standardSphere dim,
      HasDerivAt (fun t => fderiv ℝ (fun x => B (t,x)) z z) (fderiv ℝ w.1 z z) 0 := by
  let A₀ (z : X dim) := a (0,z)
  let G₀ (z : X dim) := ballParameterDerivative a (0,z)
  let b₀ : SmoothData dim := ⟨fun z => B (0,z),hB.comp (contDiff_const.prodMk contDiff_id)⟩
  let w₀ : SmoothData dim := ⟨fun z => ballParameterDerivative B (0,z),
    (contDiff_ballParameterDerivative hB).comp (contDiff_const.prodMk contDiff_id)⟩
  obtain ⟨hb₀T,hb₀H,hw₀T,hw₀H⟩ := actualBallParameterDerivative_zeroDirichlet ha hB u hEq
  have hA₀ : ContDiff ℝ ∞ A₀ := ha.comp (contDiff_const.prodMk contDiff_id)
  have hAg (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : A₀ =ᶠ[𝓝 z] A := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hA hx
  have hGg (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : G₀ =ᶠ[𝓝 z] G := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hG hx
  have hB₀ : EqOn b₀.1 b.1 (closedBall (0 : X dim) 1) := by
    apply eqOn_closedUnitBall_of_equal_ball_forcing hA₀ hEll hA b₀ b
    · intro z hz
      have hh := hb₀H hz
      change negativeBallDivergence A₀ b₀.1 z = 0 at hh
      rw [negativeBallDivergence_congr_germ (hAg z hz) EventuallyEq.rfl] at hh
      exact hh.trans (hbH hz).symm
    · exact fun z hz => (hb₀T hz).trans (hbT hz).symm
  have hW₀ : EqOn w₀.1 w.1 (closedBall (0 : X dim) 1) := by
    apply eqOn_closedUnitBall_of_equal_ball_forcing hA₀ hEll hA w₀ w
    · intro z hz
      have hBg : b₀.1 =ᶠ[𝓝 z] b.1 := by
        filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hB₀ (ball_subset_closedBall hx)
      have hh := hw₀H z hz
      change negativeBallDivergence A₀ w₀.1 z = -negativeBallDivergence G₀ b₀.1 z at hh
      rw [negativeBallDivergence_congr_germ (hAg z hz) EventuallyEq.rfl,
        negativeBallDivergence_congr_germ (hGg z hz) hBg] at hh
      exact hh.trans (hwH z hz).symm
    · exact fun z hz => (hw₀T hz).trans (hwT hz).symm
  intro z hz
  exact (hasDerivAt_ballSpatialTrace hB 0 z z).congr_deriv
    (eqOn_radialDerivative_of_eqOn_closedUnitBall hW₀ hz)

end CalderonN
