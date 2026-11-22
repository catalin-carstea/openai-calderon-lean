module

public import Proof.CalderonN.ActualTraceSections
public import Proof.CalderonN.SmoothSupportedTraceScalarCalculus

import Proof.CalderonN.LocalJetIntegral
import Proof.CalderonN.TraceFrameCoefficients
import Proof.CalderonN.SmoothTraceSobolevCompletion
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

/-! Localize a constant angular trace and factor a smooth section
vanishing on one fiber by the ordinary base coordinates. -/

public section

noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {Y : Set (X dim)}

theorem exists_chart_difference_factors (F : X dim × X dim → ℝ) (hF : ContDiff ℝ ∞ F)
    (x : X dim) :
    ∃ G : I dim → X dim × X dim → ℝ, (∀ i,ContDiff ℝ ∞ (G i)) ∧
      ∀ y z : X dim,F (y,z)-F (x,z) = ∑ i : I dim,(y i-x i)*G i (y,z) := by
  let p (q : ℝ × (X dim × X dim)) := (x+q.1 • (q.2.1-x),q.2.2)
  have hp : ContDiff ℝ ∞ p :=
    (contDiff_const.add (contDiff_fst.smul (contDiff_snd.fst.sub contDiff_const))).prodMk contDiff_snd.snd
  let U (i : I dim) (q : ℝ × (X dim × X dim)) := fderiv ℝ F (p q) (axis i,0)
  have hU (i : I dim) : ContDiff ℝ ∞ (U i) :=
    (((hF.fderiv_right (m:=∞) (by simp)).comp hp).clm_apply contDiff_const)
  let G (i : I dim) (q : X dim × X dim) := ∫ t in (0:ℝ)..1,U i (t,q)
  have hG (i : I dim) : ContDiff ℝ ∞ (G i) := by
    have h := (contDiffOn_intervalIntegral_unit_of_tube (V:=univ) isOpen_univ (hU i).contDiffOn).2
    have hEq : {p' : X dim × X dim | Icc (0:ℝ) 1 ×ˢ {p'} ⊆ (univ : Set (ℝ × (X dim × X dim)))} = univ := by simp
    simpa only [hEq,contDiffOn_univ,G] using h
  refine ⟨G,hG,?_⟩
  intro y z
  let a (t : ℝ) := F (p (t,(y,z)))
  let b (t : ℝ) := fderiv ℝ F (p (t,(y,z))) (y-x,0)
  have hDer (t : ℝ) : HasDerivAt a (b t) t := by
    have h1 : HasDerivAt (fun t : ℝ => x+t • (y-x)) (y-x) t := by
      simpa only [id_eq,one_smul] using ((hasDerivAt_id t).smul_const (y-x)).const_add x
    have h2 : HasDerivAt (fun t : ℝ => p (t,(y,z))) (y-x,0) t := h1.prodMk (hasDerivAt_const t z)
    exact ((hF.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t h2)
  have hCont : Continuous b := (((hF.fderiv_right (m:=∞) (by simp)).comp
    (hp.comp (contDiff_id.prodMk contDiff_const))).clm_apply contDiff_const).continuous
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=a) (f':=b)
    (fun t _ => hDer t) (hCont.intervalIntegrable 0 1)
  have hB (t : ℝ) : b t = ∑ i : I dim,(y i-x i)*U i (t,(y,z)) := by
    have hAxis : (∑ i : I dim,(y i-x i) • ((axis i,0) : X dim × X dim)) = (y-x,0) := by
      apply Prod.ext
      · simpa only [Prod.fst_sum,Prod.smul_fst,PiLp.sub_apply] using axis_sum_chart (y-x)
      · simp only [Prod.snd_sum,Prod.smul_snd,smul_zero,Finset.sum_const_zero]
    change fderiv ℝ F (p (t,(y,z))) (y-x,0) = _
    rw [← hAxis,map_sum]
    simp only [map_smul,smul_eq_mul,U]
  have hEnd : a 1-a 0 = F (y,z)-F (x,z) := by
    have h : x+(y-x) = y := by abel
    simp only [a,p,one_smul,zero_smul,add_zero,h]
  rw [hEnd] at hInt
  rw [← hInt]
  simp_rw [hB]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul,G]
  · intro i _
    exact (continuous_const.mul ((hU i).continuous.comp
      (continuous_id.prodMk (continuous_const (y:=(y,z)))))).intervalIntegrable 0 1

omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem exists_supportedTrace_ambient_near (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (F : X dim × X dim → ℝ) (hF : ContDiff ℝ ∞ F) :
    ∃ v : SmoothSupportedTraceSection Y, ∀ᶠ y in 𝓝 x,∀ z : ↥(standardSphere dim),v.1 (y,z) = F (y,z) := by
  obtain ⟨r,hr,hB⟩ := Metric.mem_nhds_iff.mp (hY.mem_nhds hx)
  let χ : ContDiffBump x := ⟨r/4,r/2,by positivity,by linarith⟩
  let G (p : X dim × X dim) := χ p.1*F p
  have hG : ContDiff ℝ ∞ G := (χ.contDiff.comp contDiff_fst).mul hF
  have hK : closedBall x (r/2) ⊆ Y := (closedBall_subset_ball (by linarith)).trans hB
  let w := smoothSupportedTraceOfAmbient G hG (isCompact_closedBall x (r/2)) hK
    (fun y hy z => by
      have hχ : χ y = 0 := by
        apply Function.notMem_support.mp
        rw [χ.support_eq]
        exact fun hz => hy (ball_subset_closedBall hz)
      change χ y*F (y,z) = 0
      rw [hχ,zero_mul])
  refine ⟨w,?_⟩
  filter_upwards [ball_mem_nhds x (show 0 < r/4 by positivity)] with y hy
  intro z
  change χ y*F (y,z) = F (y,z)
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy),one_mul]

theorem exists_supportedTrace_const_fiber_near (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (u : SmoothSphereTrace dim) :
    ∃ v : SmoothSupportedTraceSection Y, ∀ᶠ y in 𝓝 x,smoothSupportedTraceFiberL y v = u := by
  let v := smoothSphereTraceRepresentative u
  obtain ⟨w,hw⟩ := exists_supportedTrace_ambient_near hY hx (v.1 ∘ Prod.snd) (v.2.comp contDiff_snd)
  refine ⟨w,?_⟩
  filter_upwards [hw] with y hy
  rw [← smoothSphereTrace_representative u]
  exact Subtype.ext (funext hy)

@[expose] def chartDifference (x : X dim) (i : I dim) (y : X dim) : ℝ := y i-x i

omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem contDiff_chartDifference (x : X dim) (i : I dim) : ContDiff ℝ ∞ (chartDifference x i) :=
  (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff.sub contDiff_const

theorem exists_supportedTrace_chart_factorization (hY : IsOpen Y) {x : X dim} (hx : x ∈ Y)
    (u : SmoothSupportedTraceSection Y) (hU : smoothSupportedTraceFiberL x u = 0) :
    ∃ w : I dim → SmoothSupportedTraceSection Y,
      ∀ᶠ y in 𝓝 x, smoothSupportedTraceFiberL y u =
        smoothSupportedTraceFiberL y
          (∑ i : I dim,smoothSupportedTraceBaseMul hY (chartDifference x i)
            (contDiff_chartDifference x i).contDiffOn (w i)) := by
  obtain ⟨F,hF,hRep⟩ := smoothSupportedTraceSection_repr u
  obtain ⟨G,hG,hEq⟩ := exists_chart_difference_factors F hF x
  choose w hw using fun i : I dim => exists_supportedTrace_ambient_near hY hx (G i) (hG i)
  refine ⟨w,?_⟩
  have hW : ∀ᶠ y in 𝓝 x,∀ i : I dim,∀ z : ↥(standardSphere dim),(w i).1 (y,z) = G i (y,z) :=
    Filter.eventually_all.mpr hw
  filter_upwards [hW,hY.mem_nhds hx] with y hy hyY
  simp only [map_sum,smoothSupportedTraceBaseMul_fiber]
  apply Subtype.ext
  funext z
  have hz : F (x,z) = 0 := by
    have h := congrArg (fun v : SmoothSphereTrace dim => v.1 z) hU
    simpa only [smoothSupportedTraceFiberL_apply,hRep x z,Submodule.coe_zero,Pi.zero_apply] using h
  simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
    chartDifference,smoothSupportedTraceFiberL_apply,hy, hRep y z]
  simpa only [hz,sub_zero] using hEq y z

end CalderonN
