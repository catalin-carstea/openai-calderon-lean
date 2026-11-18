import Proof.ScalarPrincipalConnectionDrift
import Proof.UniformBackgroundConnectionHigherJets
import Proof.SmoothFiniteJetApply

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- The actual coordinate Christoffel entries inherit the SAME common
finite reference-geometry jet bound by genuine continuous-linear
evaluation of the connection tensor. No chosen frame jet is bounded. -/
theorem uniform_background_christoffel_higher_jet_bounds {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hNm : N+1 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 0 < K) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField) (e : Frame),Background Ω K M g g₁ g₂ e →
      ∀ y ∈ Ω,∀ k a b : I,SmoothFiniteJetBound (fun x => christoffel g x k a b) y N C := by
  obtain ⟨C,hC,hConnection⟩ := uniform_background_connection_higher_jet_bounds hΩ N hNm K M hK
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e hd y hy k a b
  have hΓ : SmoothFiniteJetBound (connectionBilinear g) y N C :=
    ⟨zero_le_one.trans hC,(hd.1.contDiffOn_connectionBilinear hΩ hK).contDiffAt (hΩ.mem_nhds hy),
      hConnection g g₁ g₂ e hd y hy⟩
  have hA : SmoothFiniteJetBound (fun x => connectionBilinear g x (axis a)) y N C := by
    simpa only [norm_axis,mul_one] using hΓ.apply_const (axis a)
  have hB : SmoothFiniteJetBound (fun x => connectionBilinear g x (axis a) (axis b)) y N C := by
    simpa only [norm_axis,mul_one] using hA.apply_const (axis b)
  have hProj : ‖EuclideanSpace.proj (𝕜:=ℝ) k‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [PiLp.proj_apply,one_mul,Real.norm_eq_abs] using PiLp.norm_apply_le x k
  have hP := (hB.clm (EuclideanSpace.proj (𝕜:=ℝ) k)).weaken
    ((mul_le_mul_of_nonneg_right hProj (zero_le_one.trans hC)).trans_eq (one_mul C))
  have hEq : (fun x => EuclideanSpace.proj (𝕜:=ℝ) k (connectionBilinear g x (axis a) (axis b)))=
      (fun x => christoffel g x k a b) := by
    funext x
    simp only [PiLp.proj_apply,connectionBilinear_apply,connection_axis_coordinate]
  rw [hEq] at hP
  exact hP

end ShrinkingSpheres
