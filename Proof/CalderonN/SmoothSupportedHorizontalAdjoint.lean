module

public import Proof.CalderonN.SmoothSupportedTraceAdjointCalculus
public import Proof.CalderonN.DensityDivergence

import Proof.CalderonN.MetricSmooth
import Mathlib.Tactic

/-! Integration by parts for the physical horizontal connection on
the fixed smooth trace space. -/

public section

noncomputable section
open Set
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 23
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
variable {Y : Set (X dim)} (hY : IsOpen Y)
variable (hn : 3 ≤ dim) (μ : X dim → ℝ) (hμ : ContDiffOn ℝ ∞ μ Y)
  (hPos : ∀ x ∈ Y, 0 < μ x)

@[expose] def traceDensityDivergence (μ : X dim → ℝ) (a : X dim → X dim) (x : X dim) : ℝ :=
  weightedDivergence μ a x/μ x

include hY hμ hPos in
theorem contDiffOn_traceDensityDivergence (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y) :
    ContDiffOn ℝ ∞ (traceDensityDivergence μ a) Y := by
  apply ContDiffOn.div _ hμ (fun x hx => (hPos x hx).ne')
  exact ContDiffOn.sum fun i _ =>
    (((hμ.mul (contDiffOn_vector_component a ha i)).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const)

include hY hμ hPos in
theorem traceDensityDivergence_eq_coordinate_sum (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y)
    {x : X dim} (hx : x ∈ Y) :
    traceDensityDivergence μ a x =
      ∑ i : I dim, (coordDeriv i (fun y => a y i) x+coordDeriv i μ x/μ x*a x i) := by
  unfold traceDensityDivergence weightedDivergence
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have hμ' := (hμ.contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  have ha' := ((contDiffOn_vector_component a ha i).contDiffAt (hY.mem_nhds hx)).differentiableAt (by simp)
  simp only [coordDeriv,fderiv_fun_mul hμ' ha',ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp [(hPos x hx).ne']

theorem pairedAdjoint_supportedDirectionalBase (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y) :
    let Op := ∑ i : I dim, smoothSupportedTraceBaseMul hY (fun x => a x i) (contDiffOn_vector_component a ha i) *
      smoothSupportedTraceBaseDiff (axis i)
    let δ := traceDensityDivergence μ a
    let hδ := contDiffOn_traceDensityDivergence hY μ hμ hPos a ha
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) Op (-Op-smoothSupportedTraceBaseMul hY δ hδ) := by
  dsimp only
  let M (i : I dim) := smoothSupportedTraceBaseMul hY (fun x => a x i) (contDiffOn_vector_component a ha i)
  let D (i : I dim) := smoothSupportedTraceBaseDiff (Y:=Y) (axis i)
  let b (i : I dim) (x : X dim) := coordDeriv i μ x/μ x
  let c (i : I dim) (x : X dim) := coordDeriv i (fun y => a y i) x
  have hb (i : I dim) : ContDiffOn ℝ ∞ (b i) Y :=
    ((hμ.fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const).div hμ
      (fun x hx => (hPos x hx).ne')
  have hc (i : I dim) : ContDiffOn ℝ ∞ (c i) Y :=
    ((contDiffOn_vector_component a ha i).fderiv_of_isOpen (m:=∞) hY (by simp)).clm_apply contDiffOn_const
  let d (i : I dim) (x : X dim) := c i x+b i x*a x i
  have hd (i : I dim) : ContDiffOn ℝ ∞ (d i) Y := (hc i).add ((hb i).mul (contDiffOn_vector_component a ha i))
  let B := smoothSupportedTracePairingL hn hY μ hμ
  have hCoord (i : I dim) : PairedAdjoint B (D i) (-D i-smoothSupportedTraceBaseMul hY (b i) (hb i)) :=
    fun u v => smoothSupportedTrace_coordinate_adjoint hn hY μ hμ hPos i u v
  have hPart (i : I dim) : PairedAdjoint B (M i*D i)
      (-(M i*D i)-smoothSupportedTraceBaseMul hY (d i) (hd i)) := by
    have hAdj : PairedAdjoint B (M i*D i) ((-D i-smoothSupportedTraceBaseMul hY (b i) (hb i))*M i) :=
      (pairedAdjoint_supportedBaseMul hn hY μ hμ _ _).mul (hCoord i)
    have hProduct : D i*M i = M i*D i+smoothSupportedTraceBaseMul hY (c i) (hc i) :=
      smoothSupportedTraceBaseDiff_mul hY (axis i) (fun x => a x i) (contDiffOn_vector_component a ha i)
    change PairedAdjoint B (M i*D i) (-(M i*D i)-smoothSupportedTraceBaseMul hY
      (fun x => c i x+b i x*a x i) (hd i))
    rw [smoothSupportedTraceBaseMul_add hY _ _ (hc i) ((hb i).mul (contDiffOn_vector_component a ha i)),
      smoothSupportedTraceBaseMul_mul hY _ _ (hb i) (contDiffOn_vector_component a ha i)]
    rw [sub_mul,neg_mul,hProduct] at hAdj
    change PairedAdjoint B (M i*D i)
      (-(M i*D i)-(smoothSupportedTraceBaseMul hY (c i) (hc i)+smoothSupportedTraceBaseMul hY (b i) (hb i)*M i))
    convert hAdj using 1
    abel
  have hTotal := PairedAdjoint.sum Finset.univ _ _ (fun i _ => hPart i)
  simp only [Finset.sum_sub_distrib,Finset.sum_neg_distrib] at hTotal
  rw [← smoothSupportedTraceBaseMul_sum hY Finset.univ d hd,
    smoothSupportedTraceBaseMul_congr hY _ (contDiffOn_traceDensityDivergence hY μ hμ hPos a ha)
      (fun x hx => (traceDensityDivergence_eq_coordinate_sum hY μ hμ hPos a ha hx).symm)] at hTotal
  exact hTotal

variable {g : MetricField dim} {e : Frame dim} {K : ℝ}
  (hg : Elliptic Y K g) (hK : 0 < K) (he : ∀ i, ContDiffOn ℝ ∞ (fun x => e x i) Y)

include hg hK he in
theorem pairedAdjoint_supportedHorizontal (a : X dim → X dim) (ha : ContDiffOn ℝ ∞ a Y) :
    let H := supportedHorizontal hY hg hK he a ha
    let δ := traceDensityDivergence μ a
    let hδ := contDiffOn_traceDensityDivergence hY μ hμ hPos a ha
    PairedAdjoint (smoothSupportedTracePairingL hn hY μ hμ) H (-H-smoothSupportedTraceBaseMul hY δ hδ) := by
  dsimp only
  let α (i j : I dim) (x : X dim) := (-(1/2:ℝ))*frameConnectionCoefficient g e x (a x) i j
  have hα (i j : I dim) : ContDiffOn ℝ ∞ (α i j) Y :=
    contDiffOn_const.mul (hg.contDiffOn_frameConnection hY hK e he a ha i j)
  let W (i j : I dim) := smoothSupportedTraceBaseMul hY (α i j) (hα i j)*supportedRotation hY i j
  let B := smoothSupportedTracePairingL hn hY μ hμ
  have hAngular (i j : I dim) : PairedAdjoint B (W i j) (-W i j) := by
    have h := (pairedAdjoint_supportedBaseMul hn hY μ hμ (α i j) (hα i j)).mul
      (pairedAdjoint_supportedRotation hn hY μ hμ i j)
    rw [neg_mul,← smoothSupportedTraceBaseMul_comm_fiber hY (α i j) (hα i j) _ _] at h
    exact h
  have hAll := PairedAdjoint.sum Finset.univ _ _ (fun i _ =>
    PairedAdjoint.sum Finset.univ _ _ (fun j _ => hAngular i j))
  simp only [Finset.sum_neg_distrib] at hAll
  have h := (pairedAdjoint_supportedDirectionalBase hY hn μ hμ hPos a ha).add hAll
  let F := ∑ i : I dim, smoothSupportedTraceBaseMul hY (fun x => a x i)
    (contDiffOn_vector_component a ha i) * smoothSupportedTraceBaseDiff (axis i)
  let G := ∑ i : I dim,∑ j : I dim,W i j
  let M := smoothSupportedTraceBaseMul hY (traceDensityDivergence μ a)
    (contDiffOn_traceDensityDivergence hY μ hμ hPos a ha)
  change PairedAdjoint B (F+G) (-(F+G)-M)
  have h' : PairedAdjoint B (F+G) ((-F-M)+ -G) := h
  convert h' using 1
  abel

end CalderonN
