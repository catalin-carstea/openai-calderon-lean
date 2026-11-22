module

public import Proof.CalderonN.DilationConnection

public import Proof.CalderonN.FixedTube.JetContinuity
import Proof.CalderonN.MetricConnection
import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.Conformal
import Proof.CalderonN.MetricPair
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Set Filter Metric
open scoped BigOperators ContDiff Topology

namespace CalderonN

variable {dim : ℕ} {normal : I dim}
open FixedTube

/-- The parabolic height in the tangent-normal chart. -/
def parabolicHeight (normal : I dim) (y : X dim) : ℝ := tubeHeight normal 0 1 y

def depthScale (normal : I dim) (L : ℝ) (y : X dim) : ℝ :=
  Real.exp (-2 * L * parabolicHeight normal y)

/-- The integral of the conformal scale from height one eighth. -/
def conformalDepth (normal : I dim) (L : ℝ) (y : X dim) : ℝ :=
  (Real.exp (-L / 4) - depthScale normal L y) / (2 * L)

theorem contDiff_parabolicHeight : ContDiff ℝ ∞ (parabolicHeight normal) := contDiff_tubeHeight 0 1

theorem contDiff_depthScale (L : ℝ) : ContDiff ℝ ∞ (depthScale normal L) :=
  (contDiff_const.mul (contDiff_parabolicHeight (normal := normal))).exp

theorem depthScale_pos (L : ℝ) (y : (X dim)) : 0 < depthScale normal L y := Real.exp_pos _

theorem contDiff_conformalDepth (L : ℝ) : ContDiff ℝ ∞ (conformalDepth normal L) :=
  (contDiff_const.sub ((contDiff_depthScale (normal := normal)) L)).div_const _

theorem conformalDepth_at_origin_neg {L : ℝ} (hL : 0 < L) :
    conformalDepth normal L (0 : (X dim)) < 0 := by
  have he : depthScale normal L (0 : (X dim)) = 1 := by simp [depthScale, parabolicHeight, tubeHeight, transversePair]
  exact div_neg_of_neg_of_pos (by
    rw [he, sub_neg, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)) (by positivity)

private theorem hasDerivAt_depthScale_scalar (L t : ℝ) :
    HasDerivAt (fun z => Real.exp (-2 * L * z)) ((-2 * L) * Real.exp (-2 * L * t)) t := by
  rw [mul_comm (-2 * L) (Real.exp (-2 * L * t))]
  simpa only [id_eq, mul_one, one_mul] using ((hasDerivAt_id t).const_mul (-2 * L)).exp

private theorem hasDerivAt_conformalDepth_scalar {L : ℝ} (hL : 0 < L) (t : ℝ) :
    HasDerivAt (fun z => (Real.exp (-L / 4) - Real.exp (-2 * L * z)) / (2 * L))
      (Real.exp (-2 * L * t)) t := by
  have h := ((hasDerivAt_depthScale_scalar L t).const_sub (Real.exp (-L / 4))).div_const (2 * L)
  convert h using 1
  field_simp [hL.ne']

theorem coordDeriv_depthScale (L : ℝ) (y : (X dim)) (i : (I dim)) :
    coordDeriv i (depthScale normal L) y = (-2 * L * depthScale normal L y) * coordDeriv i (parabolicHeight normal) y :=
  coordDeriv_scalar_comp ((contDiff_parabolicHeight (normal := normal)).differentiable (by simp) y)
    (hasDerivAt_depthScale_scalar L ((parabolicHeight normal) y)) i

theorem coordDeriv_conformalDepth {L : ℝ} (hL : 0 < L) (y : (X dim)) (i : (I dim)) :
    coordDeriv i (conformalDepth normal L) y = depthScale normal L y * coordDeriv i (parabolicHeight normal) y :=
  coordDeriv_scalar_comp ((contDiff_parabolicHeight (normal := normal)).differentiable (by simp) y)
    (hasDerivAt_conformalDepth_scalar hL ((parabolicHeight normal) y)) i

theorem coordDeriv_parabolicHeight (y : X dim) (i : I dim) :
    coordDeriv i (parabolicHeight normal) y = tubeHeightDeriv normal 1 y (axis i) := by
  change fderiv ℝ (tubeHeight normal 0 1) y (axis i) = _
  rw [(tube_height_hasFDerivAt (normal := normal) 0 1 y).fderiv]

theorem hessian_parabolicHeight (y : X dim) (i j : I dim) :
    hessian (parabolicHeight normal) y i j = 2 * transversePair normal (axis i) (axis j) := by
  obtain ⟨D, hD, hval⟩ := tube_height_deriv_hasFDerivAt (normal := normal) 1 y
  have he : coordDeriv j (parabolicHeight normal) =
      fun x => tubeHeightDeriv normal 1 x (axis j) := funext fun x => coordDeriv_parabolicHeight x j
  have h := hD.clm_apply (hasFDerivAt_const (axis j) y)
  rw [hessian, he, coordDeriv, h.fderiv]
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_smul, add_zero, zero_add, mul_one] using hval (axis i) (axis j)

theorem metricHessian_conformalDepth {U : Set (X dim)} (hU : IsOpen U) {g : (MetricField dim)}
    (hg : SmoothMetric U g) {y : (X dim)} (hy : y ∈ U) {L : ℝ} (hL : 0 < L) (i j : (I dim)) :
    metricHessian (fun z => depthScale normal L z • g z) (conformalDepth normal L) y i j =
      depthScale normal L y * (metricHessian g (parabolicHeight normal) y i j -
        L * covectorSq g (parabolicHeight normal) y * g y i j) := by
  let σ := depthScale normal L y
  let d (k : (I dim)) := coordDeriv k (parabolicHeight normal) y
  let Γ (k : (I dim)) := christoffel g y k i j
  let H (k : (I dim)) := (if k = j then d i else 0) + (if k = i then d j else 0) -
    g y i j * ∑ l, (g y)⁻¹ k l * d l
  have hσ : 0 < σ := (depthScale_pos (normal := normal)) L y
  have hΓ (k : (I dim)) : christoffel (fun z => depthScale normal L z • g z) y k i j = Γ k - L * H k := by
    rw [christoffel_of_conformal_smul hU hg hy (((contDiff_depthScale (normal := normal)) L).differentiable (by simp) y) hσ]
    simp only [(coordDeriv_depthScale (normal := normal)), Γ]
    have hite (l m : (I dim)) : (if k = l then (-2 * L * σ) * d m else 0) =
        (-2 * L * σ) * (if k = l then d m else 0) := by split <;> simp
    rw [← show σ = depthScale normal L y from rfl]
    change Γ k + (((if k = j then _ else 0) + (if k = i then _ else 0)) -
      g y i j * (∑ l, (g y)⁻¹ k l * ((-2 * L * σ) * d l))) / (2 * σ) = _
    rw [hite, hite]
    have hsum : (∑ l, (g y)⁻¹ k l * ((-2 * L * σ) * d l)) =
        (-2 * L * σ) * (∑ l, (g y)⁻¹ k l * d l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hsum]
    dsimp only [H]
    field_simp [hσ.ne']
    ring
  have hH : (∑ k, H k * d k) = 2 * d i * d j -
      g y i j * covectorSq g (parabolicHeight normal) y := by
    have hsum : (∑ k, (g y i j * ∑ l, (g y)⁻¹ k l * d l) * d k) =
        g y i j * covectorSq g (parabolicHeight normal) y := by
      dsimp only [covectorSq]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by dsimp only [d]; ring
    simp only [H, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hsum]
    ring
  have hc := metricHessian_scalar_comp hU (fun z => depthScale normal L z • g z)
    (contDiff_parabolicHeight (normal := normal)).contDiffOn
    (fun t => hasDerivAt_conformalDepth_scalar hL t) hy
    (hasDerivAt_depthScale_scalar L ((parabolicHeight normal) y)) i j
  change metricHessian (fun z => depthScale normal L z • g z) (conformalDepth normal L) y i j =
    σ * metricHessian (fun z => depthScale normal L z • g z) (parabolicHeight normal) y i j +
      (-2 * L * σ) * d i * d j at hc
  rw [hc]
  have hb :
      metricHessian (fun z => depthScale normal L z • g z) (parabolicHeight normal) y i j =
      metricHessian g (parabolicHeight normal) y i j + L * (∑ k, H k * d k) := by
    simp only [metricHessian, hΓ, sub_mul, Finset.sum_sub_distrib]
    change _ = hessian (parabolicHeight normal) y i j - (∑ k, Γ k * d k) + _
    simp only [Finset.mul_sum, mul_assoc]
    ring
  rw [hb, hH]
  change σ * _ + (-2 * L * σ) * d i * d j = σ * _
  ring

theorem coordDeriv_parabolicHeight_vertical (y : X dim) :
    coordDeriv normal (parabolicHeight normal) y = 1 := by
  rw [coordDeriv_parabolicHeight, tubeHeightDeriv_apply]
  have h : transversePair normal y (axis normal) = 0 := by
    unfold transversePair
    apply Finset.sum_eq_zero
    intro i hi
    simp [axis, EuclideanSpace.single_apply, Ne.symm (Finset.ne_of_mem_erase hi)]
  rw [h]
  simp [axis]

private theorem covectorSq_parabolicHeight_one (y : X dim) :
    1 ≤ covectorSq (fun _ => (1 : Mat dim)) (parabolicHeight normal) y := by
  have hinv : (1 : Mat dim)⁻¹ = 1 := by simp
  simp only [covectorSq, hinv, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h := Finset.single_le_sum (f := fun i : I dim =>
    coordDeriv i (parabolicHeight normal) y * coordDeriv i (parabolicHeight normal) y)
    (fun i _ => mul_self_nonneg _) (Finset.mem_univ normal)
  simpa only [coordDeriv_parabolicHeight_vertical, mul_one] using h

private theorem hessian_parabolicHeight_quadratic_le (y v : X dim) :
    (∑ i, ∑ j, hessian (parabolicHeight normal) y i j * v i * v j) ≤ 2 * ‖v‖ ^ 2 := by
  obtain ⟨D, hD, hval⟩ := tube_height_deriv_hasFDerivAt (normal := normal) 1 y
  have hexp : (∑ i, ∑ j, hessian (parabolicHeight normal) y i j * v i * v j) = D v v := by
    conv_rhs => rw [← axis_expansion v]
    simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hessian_parabolicHeight, hval]
    have hcomm : transversePair normal (axis i) (axis j) = transversePair normal (axis j) (axis i) := by
      unfold transversePair
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hcomm]
    ring
  rw [hexp, hval, mul_one]
  exact mul_le_mul_of_nonneg_left (transversePair_le_norm_sq normal v) (by norm_num)

private theorem smoothMetric_one : SmoothMetric (univ : Set (X dim)) (fun _ => (1 : (Mat dim))) :=
  ⟨fun _ _ => contDiffOn_const, fun _ _ => Matrix.PosDef.one⟩

private theorem christoffel_one (y : (X dim)) (k i j : (I dim)) :
    christoffel (fun _ => (1 : (Mat dim))) y k i j = 0 := by
  simp [christoffel, coordDeriv]

private theorem conformalDepth_metricHessian_at_normalized_limit (y v : (X dim)) :
    let γ := fun z : (X dim) => depthScale normal 4 z • (1 : (Mat dim))
    (∑ i, ∑ j, metricHessian γ (conformalDepth normal 4) y i j * v i * v j) ≤
      -2 * metricPair γ y v v := by
  dsimp only
  have he (i j : (I dim)) :
      metricHessian (fun z => depthScale normal 4 z • (1 : (Mat dim))) (conformalDepth normal 4) y i j =
        depthScale normal 4 y * (hessian (parabolicHeight normal) y i j -
          4 * covectorSq (fun _ => (1 : (Mat dim))) (parabolicHeight normal) y * (1 : (Mat dim)) i j) := by
    rw [(metricHessian_conformalDepth (normal := normal)) isOpen_univ smoothMetric_one (mem_univ y) (by norm_num)]
    simp only [metricHessian, christoffel_one, zero_mul, Finset.sum_const_zero, sub_zero]
  have hcontract :
      (∑ i, ∑ j, metricHessian (fun z => depthScale normal 4 z • (1 : (Mat dim))) (conformalDepth normal 4)
        y i j * v i * v j) =
      depthScale normal 4 y * ((∑ i, ∑ j, hessian (parabolicHeight normal) y i j * v i * v j) -
        (4 * covectorSq (fun _ => (1 : (Mat dim))) (parabolicHeight normal) y) *
          metricPair (fun _ => (1 : (Mat dim))) y v v) := by
    unfold metricPair
    simp_rw [he, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    all_goals
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hcontract, metricPair_smul_metric, metricPair_one]
  have hp := (covectorSq_parabolicHeight_one (normal := normal)) y
  have hh := (hessian_parabolicHeight_quadratic_le (normal := normal)) y v
  have hb : (∑ i, ∑ j, hessian (parabolicHeight normal) y i j * v i * v j) -
      (4 * covectorSq (fun _ => (1 : (Mat dim))) (parabolicHeight normal) y) * ‖v‖^2 ≤ -2 * ‖v‖^2 := by
    have h := mul_le_mul_of_nonneg_right (show 4 ≤ 4 * covectorSq (fun _ => (1 : (Mat dim)))
      (parabolicHeight normal) y by linarith) (sq_nonneg ‖v‖)
    linarith
  calc
    _ ≤ depthScale normal 4 y * (-2 * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left hb ((depthScale_pos (normal := normal)) 4 y).le
    _ = _ := by ring

/-- The strict depth inequality persists from the normalized constant
metric on a fixed compact neighborhood when the spatial dilation is small. -/
theorem eventually_conformalDepth_strict {Ω K : Set (X dim)} (hΩ : IsOpen Ω)
    (h₀ : (0 : (X dim)) ∈ Ω) (hK : IsCompact K)
    {g : (MetricField dim)} (hg : SmoothMetric Ω g) (hunit : g 0 = 1) :
    ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K, lam • y ∈ Ω ∧
      ∀ v : (X dim), let γ := conformalReference (depthScale normal 4) g lam
        (∑ i, ∑ j, metricHessian γ (conformalDepth normal 4) y i j * v i * v j) ≤ -metricPair γ y v v := by
  let γ := conformalReference (depthScale normal 4) g
  let T : Set (ℝ × (X dim)) := {q | q.1 • q.2 ∈ Ω}
  let U : Set (ℝ × ((X dim) × (X dim))) := {q | q.1 • q.2.1 ∈ Ω}
  let S := sphere (0 : (X dim)) 1
  let J (q : ℝ × ((X dim) × (X dim))) :=
    (∑ i, ∑ j, metricHessian (γ q.1) (conformalDepth normal 4) q.2.1 i j * q.2.2 i * q.2.2 j) +
      metricPair (γ q.1) q.2.1 q.2.2 q.2.2
  have hc : Continuous (fun q : ℝ × ((X dim) × (X dim)) => (q.1, q.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hT : IsOpen T := hΩ.preimage (continuous_fst.smul continuous_snd)
  have hU : IsOpen U := hT.preimage hc
  have hγ := contDiffOn_conformalReference_family_entry hg ((contDiff_depthScale (normal := normal)) 4)
  have hγpos (q : ℝ × (X dim)) (hq : q ∈ T) : (γ q.1 q.2).PosDef :=
    (hg.2 _ hq).smul ((depthScale_pos (normal := normal)) 4 q.2)
  have hΓ := contDiffOn_christoffel_slice hT hγ hγpos
  have hD (k : (I dim)) : ContDiff ℝ ∞ (coordDeriv k (conformalDepth normal 4)) :=
    (((contDiff_conformalDepth (normal := normal)) 4).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hH (i j : (I dim)) : ContDiff ℝ ∞ (fun y => hessian (conformalDepth normal 4) y i j) :=
    ((hD j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hC (i j : (I dim)) : ContDiffOn ℝ ∞
      (fun q : ℝ × (X dim) => metricHessian (γ q.1) (conformalDepth normal 4) q.2 i j) T :=
    ((hH i j).comp contDiff_snd).contDiffOn.sub
      (ContDiffOn.sum fun k _ => (hΓ k i j).mul ((hD k).comp contDiff_snd).contDiffOn)
  have hJ : ContinuousOn J U := by
    unfold J metricPair
    apply ContinuousOn.add
    all_goals
      refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      have hp (k : (I dim)) : Continuous (fun q : ℝ × ((X dim) × (X dim)) => q.2.2 k) :=
        (EuclideanSpace.proj k : (X dim) →L[ℝ] ℝ).continuous.comp (continuous_snd.comp continuous_snd)
    · exact ((((hC i j).continuousOn.comp hc.continuousOn (fun _ hp => hp)).mul
        (hp i).continuousOn).mul (hp j).continuousOn)
    · exact ((((hγ i j).continuousOn.comp hc.continuousOn (fun _ hp => hp)).mul
        (hp i).continuousOn).mul (hp j).continuousOn)
  have hγ₀ : γ 0 = fun y => depthScale normal 4 y • (1 : (Mat dim)) := by
    funext y
    simp [γ, conformalReference, dilatedMetric, hunit]
  have hbase (z : (X dim) × (X dim)) (hz : z ∈ K ×ˢ S) : J (0, z) < 0 := by
    have hpos : 0 < metricPair (γ 0) z.1 z.2 z.2 :=
      metricPair_pos_of_posDef (hγpos (0, z.1) (by simpa [T] using h₀))
        (norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hz.2).trans_ne one_ne_zero))
    have hmain := (conformalDepth_metricHessian_at_normalized_limit (normal := normal)) z.1 z.2
    dsimp only at hmain
    simp only [J, hγ₀] at *
    linarith
  have hevt : ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ z ∈ K ×ˢ S, lam • z.1 ∈ Ω ∧ J (lam, z) < 0 := by
    apply (hK.prod (isCompact_sphere _ _)).eventually_forall_of_forall_eventually
    intro z hz
    have hU₀ : ((0 : ℝ), z) ∈ U := by simpa [U] using h₀
    have hn := hU.mem_nhds hU₀
    have he := (hJ.continuousAt hn).preimage_mem_nhds (Iio_mem_nhds (hbase z hz))
    filter_upwards [hn, he] with q hq hneg
    exact ⟨hq, hneg⟩
  filter_upwards [hevt] with lam hlam y hy
  have hv₀ : axis normal ∈ S := mem_sphere_zero_iff_norm.mpr (by simp [axis, PiLp.norm_single])
  refine ⟨(hlam (y, axis normal) ⟨hy, hv₀⟩).1, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv, metricPair]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hv' : ‖v‖⁻¹ • v ∈ S := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hj := (hlam (y, ‖v‖⁻¹ • v) ⟨hy, hv'⟩).2
    have hscale : J (lam, (y, ‖v‖⁻¹ • v)) = ‖v‖⁻¹ ^ 2 * J (lam, (y, v)) := by
      simp only [J, metricPair_smul_same, mul_add]
      simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hscale] at hj
    have hm : J (lam, (y, v)) < 0 := by
      apply lt_of_mul_lt_mul_left _ (sq_nonneg (‖v‖⁻¹))
      simpa only [mul_zero] using hj
    dsimp only [J] at hm
    linarith

theorem exists_uniform_conformalDepth_covector_bounds
    {Ω K : Set (X dim)} (hΩ : IsOpen Ω) (h₀ : (0 : (X dim)) ∈ Ω) (hK : IsCompact K)
    {g : (MetricField dim)} (hg : SmoothMetric Ω g) {L : ℝ} (hL : 0 < L) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ᶠ lam in 𝓝 (0 : ℝ), ∀ y ∈ K, lam • y ∈ Ω ∧
        m ≤ Real.sqrt (covectorSq (conformalReference (depthScale normal L) g lam) (conformalDepth normal L) y) ∧
        Real.sqrt (covectorSq (conformalReference (depthScale normal L) g lam) (conformalDepth normal L) y) ≤ M := by
  let U : Set (ℝ × (X dim)) := {q | q.1 • q.2 ∈ Ω}
  let S (q : ℝ × (X dim)) :=
    Real.sqrt (covectorSq (conformalReference (depthScale normal L) g q.1) (conformalDepth normal L) q.2)
  have hU : IsOpen U := hΩ.preimage (continuous_fst.smul continuous_snd)
  have hS : ContinuousOn S U :=
    (contDiffOn_covectorSq_conformalReference_family hg ((contDiff_depthScale (normal := normal)) L) ((depthScale_pos (normal := normal)) L)
      ((contDiff_conformalDepth (normal := normal)) L)).continuousOn.sqrt
  have hbase (y : (X dim)) : ((0 : ℝ), y) ∈ U := by simpa [U] using h₀
  have hS₀ : ContinuousOn (fun y => S (0, y)) K :=
    hS.comp (continuous_const.prodMk continuous_id).continuousOn (fun y _ => hbase y)
  obtain ⟨m, hm, hlo⟩ := hK.exists_forall_le' hS₀ (a := (0 : ℝ)) (by
    intro y _
    apply Real.sqrt_pos.2 (covectorSq_pos ((hg.2 _ (hbase y)).smul ((depthScale_pos (normal := normal)) L y)) (k := normal) ?_)
    rw [(coordDeriv_conformalDepth (normal := normal)) hL, (coordDeriv_parabolicHeight_vertical (normal := normal)), mul_one]
    exact ((depthScale_pos (normal := normal)) L y).ne')
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hS₀
  let M := max 0 b + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨m / 2, M, by positivity, hM, ?_⟩
  apply hK.eventually_forall_of_forall_eventually
  intro y hy
  have hn := hU.mem_nhds (hbase y)
  have hY : S (0, y) ∈ Ioo (m / 2) M := by
    refine ⟨(half_lt_self hm).trans_le (hlo y hy), ?_⟩
    exact (le_abs_self _).trans_lt ((hb y hy).trans_lt ((le_max_right _ _).trans_lt (lt_add_one _)))
  have hE := (hS.continuousAt hn).preimage_mem_nhds (Ioo_mem_nhds hY.1 hY.2)
  filter_upwards [hn, hE] with q hq hq'
  exact ⟨hq, hq'.1.le, hq'.2.le⟩

end CalderonN
