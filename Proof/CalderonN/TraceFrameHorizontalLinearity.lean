module

public import Proof.CalderonN.TraceFrameCoefficients
public import Proof.CalderonN.SmoothSupportedTraceBaseCommutation

import Mathlib.Tactic

/-! The frame horizontal derivative is the variable-coefficient linear
combination of coordinate horizontal derivatives. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [Nontrivial (Fin dim)] in
private theorem frameConnection_axis_sum (g : MetricField dim) (e : Frame dim)
    (x v : X dim) (a b : I dim) :
    frameConnectionCoefficient g e x v a b =
      ∑ i : I dim,v i*frameConnectionCoefficient g e x (axis i) a b := by
  conv_lhs => rw [← axis_sum_chart v]
  unfold frameConnectionCoefficient covariantFrameVector
  simp only [← connectionBilinear_apply,map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,
    ← Finset.sum_add_distrib,← smul_add,← metricBilinear_apply]
  simp only [smul_eq_mul]

omit [Nontrivial (Fin dim)] in
private theorem frameAngularVector_axis_sum (g : MetricField dim) (e : Frame dim)
    (x v z : X dim) :
    frameAngularVector (frameConnectionCoefficient g e x v) z =
      ∑ i : I dim,v i • frameAngularVector (frameConnectionCoefficient g e x (axis i)) z := by
  unfold frameAngularVector
  simp_rw [frameConnection_axis_sum g e x v,← Finset.sum_neg_distrib,Finset.sum_mul,
    Finset.sum_smul,Finset.smul_sum,smul_smul]
  let C (i a b : I dim) := frameConnectionCoefficient g e x (axis i) a b
  have hSum : (∑ i : I dim,∑ a : I dim,∑ b : I dim,
        (v i * (-C i a b * z a)) • axis b) =
      ∑ a : I dim,∑ b : I dim,∑ i : I dim,(v i * (-C i a b * z a)) • axis b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  rw [hSum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  dsimp [C]
  ring

variable {Y : Set (X dim)} {g : MetricField dim} {e : Frame dim}
variable (hY : IsOpen Y) {K : ℝ} (hg : Elliptic Y K g) (hK : 0 < K)
  (he : ∀ a,ContDiffOn ℝ ∞ (fun x => e x a) Y)
  (hframe : ∀ x ∈ Y,∀ i j,metricPair g x (e x i) (e x j) = if i=j then 1 else 0)

include hframe in
theorem supportedHorizontal_axis_sum (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y) :
    supportedHorizontal hY hg hK he a ha =
      ∑ i : I dim,smoothSupportedTraceBaseMul hY (fun x => a x i) (contDiffOn_vector_component a ha i) *
        supportedHorizontal hY hg hK he (fun _ => axis i) contDiffOn_const := by
  ext u : 1
  apply smoothSupportedTraceSection_ext_by_fibers
  intro x hx
  apply Subtype.ext
  funext z
  obtain ⟨G,hG,hRep⟩ := smoothSupportedTraceSection_repr u
  simp only [smoothSupportedTraceFiberL_apply,LinearMap.sum_apply,Submodule.coe_sum,Finset.sum_apply,
    Module.End.mul_apply,supportedTraceBaseMul_apply,
    supportedHorizontal_apply_of_repr hY hg hK he hframe _ _ _ hG hRep hx]
  simp_rw [← smul_eq_mul,← map_smul,← map_sum]
  congr 1
  apply Prod.ext
  · change a x = (∑ i : I dim,a x i • (axis i,
        frameAngularVector (frameConnectionCoefficient g e x (axis i)) (z:X dim))).1
    simp only [Prod.fst_sum,Prod.fst_smul]
    exact (axis_sum_chart (a x)).symm
  · change frameAngularVector (frameConnectionCoefficient g e x (a x)) (z:X dim) =
      (∑ i : I dim,a x i • (axis i,
        frameAngularVector (frameConnectionCoefficient g e x (axis i)) (z:X dim))).2
    simp only [Prod.snd_sum,Prod.snd_smul]
    exact frameAngularVector_axis_sum g e x (a x) (z:X dim)

end CalderonN
