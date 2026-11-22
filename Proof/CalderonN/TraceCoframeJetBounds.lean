module

public import Proof.CalderonN.NormalizedRadialInverseJets
public import Proof.CalderonN.TraceFrameCoefficients

import Proof.CalderonN.UniformCanonicalFrameJets
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Uniform ordinary chart jets of the orthonormal coframe. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 3300000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem uniform_traceFrameCoordinate_jets {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hm : N ≤ m) (K : ℝ) (hK : 0 < K) (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g g₁ g₂ : MetricField dim} {e : Frame dim},
      Background Ω K M g g₁ g₂ e → (∀ x i,e x i = smoothMetricFrame (g x) i) →
      ∀ x ∈ Ω,∀ a i,LocalSmoothJetBudget (traceFrameCoordinate g e a i) x N C := by
  obtain ⟨B,hB,hFrame⟩ := uniform_canonical_metric_frame_jets (dim:=dim) K hK M
  let A := backgroundAllMetricJetBudget M
  have hA := backgroundAllMetricJetBudget_ge_one M
  let D := (2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*A*B
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let C := (dim:ℝ)*D
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro g g₁ g₂ e hbg hCan x hx a i
  have he : LocalSmoothJetBudget (fun y => e y a) x N B := by
    refine ⟨(hbg.2.2.2.2.2.2.1 a).contDiffAt (hΩ.mem_nhds hx),fun n hn => ?_⟩
    simp_rw [hCan]
    exact hFrame hΩ hbg.1 (hbg.2.2.2.2.1 g (by simp)) x hx a n (hn.trans hm)
  have hγ (j : I dim) : LocalSmoothJetBudget (fun y => g y i j) x N A := by
    refine ⟨(hbg.1.1 i j).contDiffAt (hΩ.mem_nhds hx),fun n hn => ?_⟩
    exact (hbg.2.2.2.2.1 g (by simp) ⟨n,by omega⟩ i j x hx).trans
      ((le_abs_self _).trans (abs_metricJet_le_all_budget M _))
  have he' (j : I dim) : LocalSmoothJetBudget (fun y => e y a j) x N B :=
    (he.linear_postcomp (EuclideanSpace.proj (𝕜:=ℝ) j)).enlarge
      ((mul_le_mul_of_nonneg_right (norm_euclidean_proj_le_one j) (zero_le_one.trans hB)).trans_eq (one_mul _))
  have h := LocalSmoothJetBudget.finite_sum Finset.univ (fun j : I dim => fun y => g y i j*e y a j)
    (fun _ => D) (fun j _ => (hγ j).real_mul (he' j))
  have hEq : traceFrameCoordinate g e a i = fun y => ∑ j : I dim,g y i j*e y a j := by
    funext y
    rw [traceFrameCoordinate,frameCoordinatesL_apply]
    exact metricPair_axis_left g y (e y a) i
  rw [hEq]
  simpa only [C,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

theorem uniform_frameCoordinatesL_jets {Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (N : ℕ) (hm : N ≤ m) (K : ℝ) (hK : 0 < K) (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g g₁ g₂ : MetricField dim} {e : Frame dim},
      Background Ω K M g g₁ g₂ e → (∀ x i,e x i = smoothMetricFrame (g x) i) →
      ∀ x ∈ Ω,LocalSmoothJetBudget (fun y => frameCoordinatesL g y (e y)) x N C := by
  obtain ⟨C,hC,hCof⟩ := uniform_traceFrameCoordinate_jets hΩ N hm K hK M
  let A (a i : I dim) : X dim →L[ℝ] X dim := (EuclideanSpace.proj (𝕜:=ℝ) i).smulRight (axis a)
  let W := ∑ a : I dim,∑ i : I dim,‖A a i‖*C
  have hW : 0 ≤ W := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => by positivity
  refine ⟨W,hW,?_⟩
  intro g g₁ g₂ e hbg he x hx
  have hEq : (fun y => frameCoordinatesL g y (e y)) =
      fun y => ∑ a : I dim,∑ i : I dim,traceFrameCoordinate g e a i y • A a i := by
    funext y
    ext v : 1
    ext a
    let L := frameCoordinatesL g y (e y)
    let K := EuclideanSpace.proj (𝕜:=ℝ) a
    change K (L v) = K ((∑ b : I dim,∑ i : I dim,traceFrameCoordinate g e b i y • A b i) v)
    have hL : K (L v) = ∑ i : I dim,v i*traceFrameCoordinate g e a i y := by
      calc
        K (L v) = K (L (∑ i : I dim,v i • axis i)) := congrArg (fun v => K (L v)) (axis_sum_chart v).symm
        _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]; rfl
    rw [hL]
    have hK (b : I dim) : K (axis b) = if b=a then 1 else 0 := by
      simp only [K,PiLp.proj_apply,axis,PiLp.single_apply]
      by_cases h : b=a
      · subst b; rfl
      · simp [h,Ne.symm h]
    simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,A,
      ContinuousLinearMap.smulRight_apply,map_sum,map_smul,smul_eq_mul,PiLp.proj_apply,hK]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_ite,mul_zero,mul_one,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring
  rw [hEq]
  apply LocalSmoothJetBudget.finite_sum
  intro a _
  apply LocalSmoothJetBudget.finite_sum
  intro i _
  exact (hCof hbg he x hx a i).linear_postcomp ((ContinuousLinearMap.id ℝ ℝ).smulRight (A a i))
    |>.enlarge (by rw [ContinuousLinearMap.norm_smulRight_apply,ContinuousLinearMap.norm_id,one_mul])

end CalderonN
