module

public import Proof.CalderonN.ActualParametricResponseDerivative

import Proof.CalderonN.FixedBallMetricEllipticity
import Mathlib.Tactic

/-! Identification of a selected linearized radial response with a
derivative of the actual, locally defined coefficient family. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_matched_ball_radial_family
    {U : Set (ℝ × X dim)} (hU : IsOpen U)
    (hClosed : {(0 : ℝ)} ×ˢ closedBall (0 : X dim) 1 ⊆ U)
    {a : ℝ × X dim → Mat dim} (ha : ContDiffOn ℝ ∞ a U)
    (hPos : ∀ p ∈ U, (a p).PosDef)
    {A G : X dim → Mat dim}
    (hA : EqOn (fun z => a (0,z)) A (ball (0 : X dim) 1))
    (hG : ∀ z ∈ ball (0 : X dim) 1, HasDerivAt (fun t => a (t,z)) (G z) 0)
    (u b w : SmoothData dim)
    (hbT : EqOn b.1 u.1 (standardSphere dim)) (hwT : EqOn w.1 0 (standardSphere dim))
    (hbH : EqOn (negativeBallDivergence A b.1) 0 (ball (0 : X dim) 1))
    (hwH : ∀ z ∈ ball (0 : X dim) 1, negativeBallDivergence A w.1 z = -negativeBallDivergence G b.1 z) :
    ∃ W : Set ℝ, IsOpen W ∧ (0 : ℝ) ∈ W ∧ ∃ B : ℝ × X dim → ℝ, ContDiff ℝ ∞ B ∧
      (∀ t ∈ W,
        EqOn (fun z => B (t,z)) u.1 (standardSphere dim) ∧
        EqOn (negativeBallDivergence (fun z => a (t,z)) (fun z => B (t,z))) 0 (ball (0 : X dim) 1)) ∧
      ∀ z ∈ standardSphere dim, HasDerivAt (fun t => fderiv ℝ (fun x => B (t,x)) z z)
        (fderiv ℝ w.1 z z) 0 := by
  obtain ⟨W,hW,hW₀,Z,hZ,hCZ,a',ha',hSame,B,hB,hBEq⟩ :=
    exists_local_joint_smooth_ballResponse hU hClosed ha hPos (fun p => u.1 p.2) (u.2.comp contDiff_snd)
  have hMatch (t : ℝ) (z : X dim) (ht : t ∈ W) (hz : z ∈ Z) : a' (t,z) = a (t,z) :=
    @hSame (t,z) ⟨ht,hz⟩
  have hA' (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : a' (0,z) = A z :=
    (hMatch 0 z hW₀ (hCZ (ball_subset_closedBall hz))).trans (@hA z hz)
  have hG' (z : X dim) (hz : z ∈ ball (0 : X dim) 1) : ballParameterDerivative a' (0,z) = G z := by
    have hEq : (fun t => a' (t,z)) =ᶠ[𝓝 (0 : ℝ)] (fun t => a (t,z)) := by
      filter_upwards [hW.mem_nhds hW₀] with t ht using hMatch t z ht (hCZ (ball_subset_closedBall hz))
    exact (hasDerivAt_ballParameterDerivative ha' (0,z)).unique ((hG z hz).congr_of_eventuallyEq hEq)
  let A₀ (z : X dim) := a' (0,z)
  have hA₀ : Continuous A₀ := ha'.continuous.comp (continuous_const.prodMk continuous_id)
  have hA₀pos (z : X dim) (hz : z ∈ closedBall (0 : X dim) 1) : (A₀ z).PosDef := by
    change (a' (0,z)).PosDef
    rw [hMatch 0 z hW₀ (hCZ hz)]
    exact hPos _ (hClosed ⟨mem_singleton _,hz⟩)
  obtain ⟨lo,hi,hEll⟩ := exists_uniformEllipticOn_fixedBall A₀ hA₀ hA₀pos
  have hBE : ∀ᶠ t : ℝ in 𝓝 0,
      EqOn (fun z => B (t,z)) u.1 (standardSphere dim) ∧
      EqOn (negativeBallDivergence (fun z => a' (t,z)) (fun z => B (t,z))) 0 (ball (0 : X dim) 1) := by
    filter_upwards [hW.mem_nhds hW₀] with t ht using hBEq t ht
  refine ⟨W,hW,hW₀,B,hB,?_,?_⟩
  · intro t ht
    refine ⟨(hBEq t ht).1,?_⟩
    intro z hz
    have hGerm : (fun x => a' (t,x)) =ᶠ[𝓝 z] fun x => a (t,x) := by
      filter_upwards [hZ.mem_nhds (hCZ (ball_subset_closedBall hz))] with x hx
      exact hMatch t x ht hx
    rw [← negativeBallDivergence_congr_germ hGerm EventuallyEq.rfl]
    exact (hBEq t ht).2 hz
  · exact hasDerivAt_actualBallRadialResponse_of_linearized (a:=a') (B:=B) (A:=A) (G:=G)
      ha' hB u.1 hBE hEll hA' hG' b w hbT hwT hbH hwH

end CalderonN
