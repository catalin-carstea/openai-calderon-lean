module

public import Proof.CalderonN.TraceCoordinatePotential
public import Proof.CalderonN.TraceCoframeJetBounds
public import Proof.CalderonN.UniformBackgroundChristoffelJets

import Proof.CalderonN.CoordinateJets
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! Base jets of the frame and of the rotation coefficients in the
coordinate horizontal derivative. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem traceCoordinateConnectionScalar_eq_sum
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {g : MetricField dim} {e : Frame dim}
    (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Ω)
    (x : X dim) (hx : x ∈ Ω) (i a b : I dim) :
    traceCoordinateConnectionScalar g e i a b x =
      (-(1/2:ℝ))*(∑ k : I dim,traceFrameCoordinate g e b k x *
        (coordDeriv i (fun y => e y a k) x+∑ j : I dim,christoffel g x k i j*e x a j)) := by
  let v := covariantFrameVector g e x (axis i) a
  let L := frameCoordinatesL g x (e x)
  have hv : (L v) b = metricPair g x v (e x b) := by rw [frameCoordinatesL_apply]; rfl
  have hL : (L v) b = ∑ k : I dim,traceFrameCoordinate g e b k x * v k := by
    have hh := congrArg (EuclideanSpace.proj (𝕜:=ℝ) b) (congrArg L (axis_sum_chart v))
    simpa only [map_sum,map_smul,PiLp.proj_apply,smul_eq_mul,mul_comm,traceFrameCoordinate,L] using hh.symm
  have hComp (k : I dim) : v k =
      coordDeriv i (fun y => e y a k) x+∑ j : I dim,christoffel g x k i j*e x a j := by
    let P := EuclideanSpace.proj (𝕜:=ℝ) k
    have he' := ((he a).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
    have hh := congrArg (fun T : X dim →L[ℝ] ℝ => T (axis i)) (P.hasFDerivAt.comp x he'.hasFDerivAt).fderiv
    change coordDeriv i (fun y => e y a k) x = (fderiv ℝ (fun y => e y a) x (axis i)) k at hh
    have hconn : connection g x (axis i) (e x a) k = ∑ j : I dim,christoffel g x k i j*e x a j := by
      have h := congrArg (EuclideanSpace.proj (𝕜:=ℝ) k)
        (congrArg (connectionBilinear g x (axis i)) (axis_sum_chart (e x a)))
      simpa only [map_sum,map_smul,PiLp.proj_apply,smul_eq_mul,connectionBilinear_apply,
        connection_axis_components,mul_comm] using h.symm
    rw [show v k = (fderiv ℝ (fun y => e y a) x (axis i)) k+connection g x (axis i) (e x a) k from rfl,
      ← hh,hconn]
  rw [traceCoordinateConnectionScalar,frameConnectionCoefficient,← hv,hL]
  simp only [hComp]

theorem uniform_actualTraceBackground_scalar_jets
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {m N : ℕ} (hm : N+1 ≤ m) (K : ℝ) (hK : 0 < K)
    (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g g₁ g₂ : MetricField dim) (e : Frame dim),
      Background Ω K M g g₁ g₂ e →
      (∀ y a,e y a = smoothMetricFrame (g y) a) →
      ∀ x ∈ Ω,
        (∀ i a,LocalSmoothJetBudget (fun y => e y a i) x N C) ∧
        (∀ i a,LocalSmoothJetBudget (traceFrameCoordinate g e a i) x N C) ∧
        (∀ i a b,LocalSmoothJetBudget (traceCoordinateConnectionScalar g e i a b) x N C) := by
  obtain ⟨F,hF,hFrame⟩ := uniform_canonical_metric_frame_jets (dim:=dim) K hK M
  obtain ⟨A,hA,hCoframe⟩ := uniform_traceFrameCoordinate_jets hΩ N (by omega : N ≤ m) K hK M
  obtain ⟨G,hG,hΓ⟩ := uniform_background_christoffel_jet_budget hΩ N hm K M hK
  let L := (2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖
  let D := F+(dim:ℝ)*(L*G*F)
  let E := (1/2:ℝ)*((dim:ℝ)*(L*A*D))
  let C := 1+F+A+E
  have hF₀ := zero_le_one.trans hF
  have hG₀ := zero_le_one.trans hG
  have hD : 0 ≤ D := by dsimp only [D,L]; positivity
  have hE : 0 ≤ E := by dsimp only [E,L]; positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hF₀,hA,hE]
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e hBg hCan x hx
  have he (a : I dim) := hBg.2.2.2.2.2.2.1 a
  have hE₀ (i a : I dim) : LocalSmoothJetBudget (fun y => e y a i) x (N+1) F := by
    have h : LocalSmoothJetBudget (fun y => e y a) x (N+1) F := by
      refine ⟨(he a).contDiffAt (hΩ.mem_nhds hx),fun n hn => ?_⟩
      simp_rw [hCan]
      exact hFrame hΩ hBg.1 (hBg.2.2.2.2.1 g (by simp)) x hx a n (hn.trans hm)
    refine (h.linear_postcomp (EuclideanSpace.proj (𝕜:=ℝ) i)).enlarge ?_
    exact (mul_le_mul_of_nonneg_right (norm_euclidean_proj_le_one i) hF₀).trans_eq (one_mul _)
  have hA₀ (i a : I dim) := hCoframe hBg hCan x hx a i
  have hG₁ (i j k : I dim) := hΓ g g₁ g₂ e hBg x hx k i j
  refine ⟨fun i a => ((hE₀ i a).mono_order (Nat.le_succ N)).enlarge (by dsimp only [C]; linarith only [hA,hE]),
    fun i a => (hA₀ i a).enlarge (by dsimp only [C]; linarith only [hF₀,hE]),?_⟩
  intro i a b
  let v (k : I dim) (y : X dim) := coordDeriv i (fun y => e y a k) y+
    ∑ j : I dim,christoffel g y k i j*e y a j
  have hv (k : I dim) : LocalSmoothJetBudget (v k) x N D := by
    have hDer : LocalSmoothJetBudget (coordDeriv i (fun y => e y a k)) x N F :=
      ⟨((hE₀ k a).smooth.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const,
        fun n hn => (norm_iteratedFDeriv_coordDeriv_le (hE₀ k a).smooth i n).trans
          ((hE₀ k a).bound (n+1) (Nat.succ_le_succ hn))⟩
    have hSum := LocalSmoothJetBudget.finite_sum Finset.univ
      (fun j : I dim => fun y => christoffel g y k i j*e y a j) (fun _ => L*G*F)
      (fun j _ => (hG₁ i j k).real_mul ((hE₀ j a).mono_order (Nat.le_succ N)))
    simpa only [v,D,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hDer.add hSum
  have hSum := LocalSmoothJetBudget.finite_sum Finset.univ
    (fun k : I dim => fun y => traceFrameCoordinate g e b k y*v k y) (fun _ => L*A*D)
    (fun k _ => (hA₀ k b).real_mul (hv k))
  have heq : (fun y => (-(1/2:ℝ)) • (∑ k : I dim,traceFrameCoordinate g e b k y*v k y)) =ᶠ[𝓝 x]
      traceCoordinateConnectionScalar g e i a b := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (traceCoordinateConnectionScalar_eq_sum hΩ he y hy i a b).symm
  have hh : LocalSmoothJetBudget (traceCoordinateConnectionScalar g e i a b) x N E := by
    have hScale := hSum.linear_postcomp ((-(1/2:ℝ)) • ContinuousLinearMap.id ℝ ℝ)
    have hce : ‖(-(1/2:ℝ)) • ContinuousLinearMap.id ℝ ℝ‖ = (1/2:ℝ) := by
      rw [norm_smul,ContinuousLinearMap.norm_id,Real.norm_eq_abs,mul_one]
      norm_num
    rw [hce] at hScale
    simpa only [E,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hScale.congr_germ heq.symm
  exact hh.enlarge (by dsimp only [C]; linarith only [hF₀,hA])

end CalderonN
