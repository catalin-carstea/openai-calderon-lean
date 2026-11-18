import Proof.FramedRaisingHalfEndpoints
import Proof.CovariantHalfCoarseBridge
import Proof.HalfCovariantDirectionLinear
import Proof.BalancedCoarsePotential
import Proof.BackgroundBudgets
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def framedRaisingHalfBudget (K M0 M1 : ℝ) : ℝ :=
  3*K*(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ))+
    6*(9*|M0| *K)*(243*K*|M1| *K))

lemma framedRaisingHalfBudget_nonneg (K M0 M1 : ℝ) (hK : 0 ≤ K) :
    0 ≤ framedRaisingHalfBudget K M0 M1 := by
  have hN0 : 0 ≤ radialDriftSobolevBound (-(1/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  have hN1 : 0 ≤ radialDriftSobolevBound (-(3/2:ℝ)) := zero_le_one.trans (le_max_left _ _)
  unfold framedRaisingHalfBudget
  positivity

/-- The physical raising family has fixed covariant bounds even when
    the orthonormal frame has unrestricted smooth derivatives. -/
theorem Admissible.framedRaisingHalf_covariant_data {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 1 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (b : I) :
    let Q := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
    ∀ x ∈ Y,‖framedRaisingHalfL d x (axis b)‖ ≤ Q ∧
      ‖framedRaisingHigherL d x (axis b)‖ ≤ Q ∧
      ∀ i : I,‖halfOperatorCovariantDerivativeL d
        (fun y => framedRaisingHalfL d y (axis b))
        (fun y => framedRaisingHigherL d y (axis b)) x (axis i)‖ ≤ Q := by
  let NL := 10*radialDriftSobolevBound (-(1/2:ℝ))
  let NH := 10*radialDriftSobolevBound (-(3/2:ℝ))
  let CC := 9*|M 0| *K
  let CG := 243*K*|M ⟨1,by omega⟩|
  let CJ := 6*CC*(CG*K)
  let Q := framedRaisingHalfBudget K (M 0) (M ⟨1,by omega⟩)
  have hK0 := zero_lt_one.trans_le hK
  have hNL : 0 ≤ NL := mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
  have hNH : 0 ≤ NH := mul_nonneg (by norm_num) (zero_le_one.trans (le_max_left _ _))
  have hCC : 0 ≤ CC := by dsimp only [CC];positivity
  have hCG : 0 ≤ CG := by dsimp only [CG];positivity
  have hCJ : 0 ≤ CJ := by dsimp only [CJ];positivity
  have hloQ : 3*K*NL ≤ Q := mul_le_mul_of_nonneg_left (by linarith only [hNH,hCJ]) (by positivity)
  have hhiQ : 3*K*NH ≤ Q := mul_le_mul_of_nonneg_left (by linarith only [hNL,hCJ]) (by positivity)
  have hJQ : 3*K*CJ ≤ Q := mul_le_mul_of_nonneg_left (by linarith only [hNL,hNH]) (by positivity)
  have hS := hd.framedRaisingHalf_smooth (axis b)
  change ∀ x ∈ Y,‖framedRaisingHalfL d x (axis b)‖ ≤ Q ∧
    ‖framedRaisingHigherL d x (axis b)‖ ≤ Q ∧
    ∀ i : I,‖halfOperatorCovariantDerivativeL d
      (fun y => framedRaisingHalfL d y (axis b))
      (fun y => framedRaisingHigherL d y (axis b)) x (axis i)‖ ≤ Q
  intro x hx
  have hxΩ := hd.2.1.center_mem hx
  have hFrame := hd.1.2.2.2.2.2.2.2 x hxΩ
  have hc (j : I) : |frameCoordinateLinear d.γ d.frame x j (axis b)| ≤ K := by
    rw [frameCoordinateLinear_apply]
    exact hd.1.1.frame_coordinate_abs_bound hK d.frame hxΩ hFrame b j
  have hLo : ‖framedRaisingHalfL d x (axis b)‖ ≤ 3*K*NL :=
    norm_weighted_sum_three_le _ _ _ _ hK0.le hc norm_flatHalfRaisingL_le
  have hHi : ‖framedRaisingHigherL d x (axis b)‖ ≤ 3*K*NH :=
    norm_weighted_sum_three_le _ _ _ _ hK0.le hc norm_flatThreeHalfRaisingL_le
  have hD (i : I) : ‖halfOperatorCovariantDerivativeL d
      (fun y => framedRaisingHalfL d y (axis b))
      (fun y => framedRaisingHigherL d y (axis b)) x (d.frame x i)‖ ≤ CJ := by
    have hEop := hd.1.1.norm_frameVectorLinear_le hK hxΩ d.frame hFrame
    have hE : ‖d.frame x i‖ ≤ K := by
      have hh := (frameVectorLinear d.frame x).le_opNorm (axis i)
      rw [frameVectorLinear_apply,frameVector_axis,norm_axis,mul_one] at hh
      exact hh.trans hEop
    have hΓ : ‖connectionBilinear d.γ x‖ ≤ CG := hd.1.connection_budget hK0 (by omega) hxΩ
    have hConn : ‖connection d.γ x (d.frame x i) (axis b)‖ ≤ CG*K := by
      rw [← connectionBilinear_apply]
      calc
        _ ≤ ‖connectionBilinear d.γ x‖*‖d.frame x i‖*‖axis b‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ CG*K*1 := by rw [norm_axis];gcongr
        _ = _ := mul_one _
    have hGraph := framedFlatRaising_covariant_graph hΩ d hd.1.1 hK0
      (fun j => hd.1.2.2.2.2.2.2.1 j) hd.1.2.2.2.2.2.2.2 hxΩ (d.frame x i) (axis b)
    have hEq := halfOperatorCovariantDerivativeL_eq_coarse
      (fun y => framedFlatRaisingSobolevL 1 d.γ d.frame y (axis b))
      (fun y => framedRaisingHalfL d y (axis b))
      (fun y => framedRaisingHigherL d y (axis b))
      (framedFlatRaisingSobolevL 1 d.γ d.frame x (connection d.γ x (d.frame x i) (axis b)))
      ((hS.2.2.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      ((hS.1.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp))
      (Eventually.of_forall (fun y => framedRaisingHalfL_coarse d y (axis b)))
      (framedRaisingHigherL_coarse d x (axis b)) hGraph
    rw [hEq]
    exact (norm_balancedCoarsePotentialL_le _).trans
      (((hd.framedFlatRaisingSobolevL_norms hK hx _).1).trans
        (mul_le_mul_of_nonneg_left hConn (by positivity)))
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  have hg : Elliptic Y K d.γ := ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun y hy => hd.1.1.2 y (hSub hy)⟩
  refine ⟨hLo.trans hloQ,hHi.trans hhiQ,?_⟩
  intro i
  exact (norm_halfOperatorCovariantDerivativeL_axis_le d hg hK hx hFrame _ _ CJ hD i).trans hJQ
end ShrinkingSpheres
