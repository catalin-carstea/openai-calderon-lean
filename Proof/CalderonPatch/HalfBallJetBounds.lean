module

public import Proof.CalderonPatch.NativeBoundaryMetricChart

import Proof.CalderonN.ClosedBallPointwise
import Proof.CalderonN.ScaledRadiusJetBudget
import Proof.CalderonN.SobolevInteriorRepresentative
import Proof.ReleasedAnalysis.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Tactic

public section

noncomputable section

open Set Filter MeasureTheory Metric
open scoped ContDiff ENNReal Pointwise Topology

namespace CalderonPatch

open CalderonN (X I axis)

variable {n : ℕ} [NeZero n]
local notation "E" => X n
local notation "μ" => (volume : Measure E)

omit [NeZero n] in
private theorem exists_smooth_eqOn_compact {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {O K : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f O) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨χ,hχ,_,hχ1,_,hχs⟩ := hK.exists_contDiff_cutoff hO hKO
  let g (x : E) := χ x • f x
  refine ⟨g,contDiff_iff_contDiffAt.2 (fun x => ?_),fun x hx => ?_⟩
  · by_cases hx : x ∈ O
    · exact (hχ.contDiffAt.smul ((hf x hx).contDiffAt (hO.mem_nhds hx)))
    · have hNot : x ∉ tsupport χ := fun ht => hx (hχs ht)
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hNot] with y hy
      simp [g,hy]
  · filter_upwards [isOpen_interior.mem_nhds (hχ1 hx)] with y hy
    have hy' : χ y = 1 := mem_singleton_iff.1 (interior_subset hy : y ∈ χ ⁻¹' ({1} : Set ℝ))
    simp [g,hy']

omit [NeZero n] in
private theorem setIntegral_sq_affine_closedBall {F : Type*} [NormedAddCommGroup F]
    {r : ℝ} (hr : 0 < r) (c : E) (f : E → F) :
    (∫ y in closedBall (0 : E) 1, ‖f (c + r • y)‖ ^ 2 ∂μ) =
      (r ^ n)⁻¹ * (∫ y in closedBall c r, ‖f y‖ ^ 2 ∂μ) := by
  let T := MeasurableEquiv.addLeft c
  have hpre : T ⁻¹' closedBall c r = closedBall (0 : E) r := by
    ext y
    change dist (c + y) c ≤ r ↔ dist y 0 ≤ r
    simp [dist_eq_norm]
  have htr := (measurePreserving_add_left μ c).setIntegral_preimage_emb T.measurableEmbedding
    (fun y => ‖f y‖ ^ 2) (closedBall c r)
  change (∫ x in T ⁻¹' closedBall c r, ‖f (c+x)‖ ^ 2 ∂μ) = _ at htr
  rw [hpre] at htr
  change (∫ x in closedBall (0 : E) 1, (fun y => ‖f (c+y)‖ ^ 2) (r • x) ∂μ) = _
  rw [Measure.setIntegral_comp_smul_of_pos μ (fun y => ‖f (c+y)‖ ^ 2) (closedBall (0 : E) 1) hr,
    show Module.finrank ℝ E = n by simp,
    _root_.smul_closedBall r (0 : E) (by norm_num : (0 : ℝ) ≤ 1),Real.norm_of_nonneg hr.le,smul_zero,mul_one,smul_eq_mul,htr]

set_option maxHeartbeats 3200000 in
/-- Uniform pointwise control of the smooth derivatives in a smaller
half-ball. A translated ball of a fixed radius lies on the inward
side of the face and contains the evaluation point at its bottom. -/
theorem exists_iteratedFDeriv_bound_on_halfBall {p : E} {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (ball p R ∩ positiveHalfSpace n))
    (hLp : ∀ k, MemLp (iteratedFDeriv ℝ k f) 2 ((μ).restrict (ball p R ∩ positiveHalfSpace n)))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ ball p (R / 4) ∩ positiveHalfSpace n,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  let O := ball p R ∩ positiveHalfSpace n
  have hO : IsOpen O := isOpen_ball.inter isOpen_positiveHalfSpace
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; positivity
  let B := closedBall (0 : E) 1
  let M := (2 : ℝ)^(n+1) / Real.sqrt ((μ).real B)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let Q (j : ℕ) := ∫ z in O, ‖iteratedFDeriv ℝ (j+k) f z‖ ^ 2 ∂μ
  let C := M * ∑ j ∈ Finset.range (n+2), Real.sqrt (r^(2*j) * (r^n)⁻¹ * Q j)
  refine ⟨C,by dsimp only [C]; positivity,fun x hx => ?_⟩
  let v : E := axis 0
  have hv (t : E) : |t 0| ≤ ‖t‖ := by simpa using PiLp.norm_apply_le t 0
  have hv0 : v 0 = 1 := by simp [v,axis]
  have hvn : ‖v‖ = 1 := by simp [v,axis]
  let c := x + r • v
  have hxc : dist x c ≤ r := by rw [dist_comm,dist_eq_norm]; simp [c,hvn,norm_smul,abs_of_pos hr]
  have hsub (z : E) (hz : z ∈ closedBall c r) : z ∈ O := by
    refine ⟨?_,?_⟩
    · have hz' := mem_closedBall.mp hz
      apply mem_ball.mpr
      have hx' := mem_ball.mp hx.1
      have h := (dist_triangle z c p).trans (add_le_add hz'
        ((dist_triangle c x p).trans (add_le_add (dist_comm x c ▸ hxc) hx'.le)))
      dsimp [r] at h
      linarith
    · apply mem_positiveHalfSpace.mpr
      have hx' := mem_positiveHalfSpace.mp hx.2
      have hz' := mem_closedBall.mp hz
      rw [dist_eq_norm] at hz'
      have hcoord := (neg_le_abs (z 0 - c 0)).trans ((hv (z-c)).trans hz')
      have hc0 : c 0 = x 0 + r := by simp [c,hv0]
      change -(z 0 - c 0) ≤ r at hcoord
      linarith
  obtain ⟨g,hg,hgEq⟩ := exists_smooth_eqOn_compact hO (isCompact_closedBall c r) hsub hf
  let gₖ := iteratedFDeriv ℝ k g
  let G (y : E) := gₖ (c + r • y)
  have hG : ContDiff ℝ ∞ G :=
    (hg.iteratedFDeriv_right (m := ∞) (by simp)).comp (by fun_prop)
  have hTest : -v ∈ B := by
    change dist (-v) 0 ≤ 1
    simp [hvn]
  have hxRead : G (-v) = iteratedFDeriv ℝ k f x := by
    have hEq := (Filter.EventuallyEq.iteratedFDeriv ℝ (hgEq x (mem_closedBall.mpr hxc)) k).eq_of_nhds
    simpa only [G,gₖ,c,smul_neg,add_neg_cancel_right] using hEq
  rw [← hxRead]
  refine (CalderonN.norm_le_unitBall_L2_jets (hG.of_le (by simp)) hTest).trans ?_
  change M * _ ≤ M * _
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hM
  apply Real.sqrt_le_sqrt
  have hnorm (y : E) :
      ‖iteratedFDeriv ℝ j G y‖ = r^j * ‖iteratedFDeriv ℝ (j+k) g (c + r • y)‖ := by
    rw [CalderonN.norm_iteratedFDeriv_affine_scale gₖ c y r hr.ne' j,abs_of_pos hr,
      CalderonN.norm_iteratedFDeriv_iteratedFDeriv g k j]
  simp_rw [hnorm,mul_pow]
  rw [integral_const_mul,setIntegral_sq_affine_closedBall hr c (iteratedFDeriv ℝ (j+k) g),
    mul_assoc,← pow_mul, mul_comm j 2, pow_mul]
  have hEq : EqOn (fun y => ‖iteratedFDeriv ℝ (j+k) g y‖ ^ 2)
      (fun y => ‖iteratedFDeriv ℝ (j+k) f y‖ ^ 2) (closedBall c r) :=
    fun y hy => congrArg (fun T => ‖T‖ ^ 2) ((Filter.EventuallyEq.iteratedFDeriv ℝ (hgEq y hy) (j+k)).eq_of_nhds)
  rw [setIntegral_congr_fun measurableSet_closedBall hEq]
  have hMp := hLp (j+k)
  have hI : Integrable (fun x => ‖iteratedFDeriv ℝ (j+k) f x‖ ^ 2) ((μ).restrict O) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      hMp.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact setIntegral_mono_set hI (.of_forall fun _ => sq_nonneg _) (.of_forall hsub)

end CalderonPatch
