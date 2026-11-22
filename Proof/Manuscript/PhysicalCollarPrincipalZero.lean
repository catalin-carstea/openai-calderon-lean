module

public import Proof.Manuscript.MovingTrace.NormalBallPoissonTube
public import Proof.Manuscript.MovingTrace.CollarNormalizedPrincipal
public import Proof.CalderonN.MetricVolumeDifferential
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section

open Set Filter Metric CalderonN CalderonPatch CalderonPatch.BoundaryLayer Matrix
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Operator

namespace CalderonPaper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ}
local notation "Z" => X (n+1)
local notation "P" => NormalMetricParameter (n+1) × ℝ

local instance principalCurveTopology (k : ℕ) : TopologicalSpace (Mat k) :=
  @NormedAddCommGroup.toMetricSpace (Mat k) Matrix.linftyOpNormedAddCommGroup
    |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

private theorem hasDerivAt_sandwich_entry_zero {d : ℕ} {A : ℝ → Mat d}
    (hA : ∀ i j, HasDerivAt (fun r => A r i j) 0 0) (L R : Mat d) (i j : I d) :
    HasDerivAt (fun r => (L * A r * R) i j) 0 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
    (HasDerivAt.fun_sum (u := Finset.univ) fun l _ => (hA l k).const_mul (L i l)).mul_const (R k j)
  simpa only [Matrix.mul_apply, mul_zero, zero_mul, Finset.sum_const_zero] using h

private theorem hasDerivAt_matrix_zero_of_entries {d : ℕ} {A : ℝ → Mat d}
    (hA : ∀ i j, HasDerivAt (fun r => A r i j) 0 0) : HasDerivAt A 0 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
      (hA i j).smul_const (Matrix.single i j (1 : ℝ) : Mat d)
  have hRewrite (r : ℝ) :
      (∑ i : I d, ∑ j : I d, A r i j • (Matrix.single i j (1 : ℝ) : Mat d)) = A r := by
    simp only [Matrix.smul_single,smul_eq_mul,mul_one]
    exact Matrix.sum_sum_single (A r)
  simpa only [hRewrite,zero_smul,Finset.sum_const_zero] using h

private theorem symmetrizedNormalMetric_conformal_at
    {g γ : ℝ → MetricField (n+1)} {E : ℝ → Z × Z → Z} {e : ℝ → Frame (n+1)}
    (lam : ℝ) (y z : Z) (r c : ℝ)
    (h : g lam (normalBallChartMap (E lam) (e lam) y r z) =
      c • γ lam (normalBallChartMap (E lam) (e lam) y r z)) :
    symmetrizedNormalMetric g E e ((lam,y,r),z) =
      c • symmetrizedNormalMetric γ E e ((lam,y,r),z) := by
  have hN : normalizedBallMetric (g lam) (E lam) (e lam) y r z =
      c • normalizedBallMetric (γ lam) (E lam) (e lam) y r z := by
    simp only [normalizedBallMetric,h,Matrix.mul_smul,Matrix.smul_mul]
  unfold symmetrizedNormalMetric
  change (1/2 : ℝ) • (normalizedBallMetric (g lam) (E lam) (e lam) y r z + _) =
    c • ((1/2 : ℝ) • (normalizedBallMetric (γ lam) (E lam) (e lam) y r z + _))
  rw [hN,Matrix.transpose_smul,← smul_add,smul_comm]

private theorem radializedMetric_conformal_at {d : ℕ} [NeZero d]
    {g γ : MetricField d} {z : X d} {c : ℝ} (h : g z = c • γ z) :
    radializedMetric radialCutoff g z = c • radializedMetric radialCutoff γ z := by
  dsimp only [radializedMetric]
  rw [h,Matrix.mul_smul,Matrix.smul_mul,smul_comm (1-radialCutoff z/2) c,
    smul_comm (radialCutoff z/2) c,← smul_add]

private theorem normalizedCollarMetric_continuous_radius_cancel
    {A D : Mat (n+1)} {a : ℝ} (ha : 0 < a) (hD : D.PosDef) (h : A = a • D) (i j : I n) :
    A⁻¹ i.succ j.succ / A⁻¹ 0 0 = D⁻¹ i.succ j.succ / D⁻¹ 0 0 := by
  have hInv : A⁻¹ = a⁻¹ • D⁻¹ := by
    rw [h]
    exact Matrix.inv_smul' _ (Units.mk0 a ha.ne') (isUnit_iff_ne_zero.mpr hD.det_pos.ne')
  rw [hInv]
  simp only [Matrix.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ (inv_ne_zero ha.ne')

set_option maxHeartbeats 1200000 in
/-- The actual signed-collar principal root at fixed angle, direction and
slope is stationary to first order in the physical radius. The endpoint
conformal factor cancels in the ratio of inverse metric entries. -/
theorem signedPoissonCollar_kappa_first_radius_zero [Nontrivial (Fin (n+1))]
    {Y Ω : Set Z} (hΩ : IsOpen Ω)
    {γ g q : ℝ → MetricField (n+1)} {K : ℝ} {m : ℕ} {B : Fin (m+1) → ℝ}
    {E : ℝ → Z × Z → Z} {e : ℝ → Frame (n+1)}
    (lam : ℝ) (hB : Background Ω K B (γ lam) (g lam) (q lam) (e lam))
    (hK : 0 < K) (hE : ContDiff ℝ ∞ (E lam))
    {R : Z → ℝ} (hN : NormalCoordinates Y Ω (γ lam) (E lam) R) {y : Z} (hy : y ∈ Y)
    {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)
    (hG : G.g = radializedNormalFamily (fun p => symmetrizedNormalMetric g E e (p.1.1,p.2)))
    (b : ℝ) (hG0 : ((lam,y,0),b) ∈ G.V) (x ν : X n) (hν : ν ≠ 0) :
    HasDerivAt (fun r : ℝ => C.coefficients.kappa ((((lam,y,r),b),ν),x)) 0 0 := by
  let P0 (r : ℝ) : P := ((lam,y,r),b)
  let u := signedLayerCoordinates (x,(0 : ℝ))
  let Cmap := signedSphericalCollar C.pole
  let w := Cmap u
  let L := coordinateJacobian Cmap u
  let W (r : ℝ) (z : Z) := symmetrizedNormalMetric γ E e ((lam,y,r),z)
  let ref (r : ℝ) := (Lᵀ * radializedMetric radialCutoff (W r) w) * L
  let realMetric (r : ℝ) := (Lᵀ * G.g (P0 r,w)) * L
  let endpoint (r : ℝ) := normalBallChartMap (E lam) (e lam) y r w
  let α (r : ℝ) := firstMetricConformalFactor (γ lam) (g lam) (endpoint r)
  let ζ := (2 * Real.pi) • ν
  have hyΩ := hN.center_mem hy
  have he := hB.2.2.2.2.2.2.2 y hyΩ
  have hEnd : ∀ᶠ r in 𝓝 (0 : ℝ), endpoint r ∈ Ω := by
    have hC : Continuous endpoint := hE.continuous.comp (continuous_const.prodMk (continuous_id.smul continuous_const))
    have hh : endpoint 0 ∈ Ω := by simp [endpoint,normalBallChartMap,hN.exp_zero hy,hyΩ]
    exact hC.continuousAt.preimage_mem_nhds (hΩ.mem_nhds hh)
  have hP : Continuous P0 := continuous_const.prodMk (continuous_const.prodMk continuous_id) |>.prodMk continuous_const
  have hPV : ∀ᶠ r in 𝓝 0, P0 r ∈ G.V := hP.continuousAt.preimage_mem_nhds (G.openV.mem_nhds hG0)
  have hCollar (r : ℝ) (hr : P0 r ∈ G.V) : ((((P0 r),ν),x),0) ∈ C.collarDomain := by
    exact ⟨⟨⟨hr,mem_univ _⟩,mem_univ _⟩,by constructor <;> linarith [C.pos]⟩
  have hMpos : ∀ᶠ r in 𝓝 (0 : ℝ), (realMetric r).PosDef := by
    filter_upwards [hPV] with r hr
    have hP := C.metric_posDef (q := (((P0 r,ν),x),(0:ℝ))) (hCollar r hr)
    simpa only [SignedPoissonCollar.metric,realMetric,L,Cmap,u,w,pullbackMetric] using hP
  have hα : ∀ᶠ r in 𝓝 (0 : ℝ), 0 < α r := hEnd.mono (fun r hr => hB.firstMetricConformalFactor_pos hK hr)
  have hConf : realMetric =ᶠ[𝓝 (0 : ℝ)] fun r => α r • ref r := by
    filter_upwards [hEnd] with r hr
    have hPoint : G.g (P0 r,w) = α r • radializedMetric radialCutoff (W r) w := by
      rw [hG]
      exact radializedMetric_conformal_at (symmetrizedNormalMetric_conformal_at lam y w r (α r)
        (hB.firstMetric_eq_conformalFactor hK hr))
    change (Lᵀ * G.g (P0 r,w)) * L = α r • ((Lᵀ * radializedMetric radialCutoff (W r) w) * L)
    rw [hPoint,Matrix.mul_smul,Matrix.smul_mul]
  have hRefPos : ∀ᶠ r in 𝓝 (0 : ℝ), (ref r).PosDef := by
    filter_upwards [hMpos,hα,hConf] with r hr ha heq
    have h := hr.smul (inv_pos.mpr ha)
    rw [heq,smul_smul,inv_mul_cancel₀ ha.ne',one_smul] at h
    exact h
  have hEntry (i j : I (n+1)) : HasDerivAt (fun r => W r w i j) 0 0 := by
    have hN' (i j : I (n+1)) : HasDerivAt
        (fun r => normalizedBallMetric (γ lam) (E lam) (e lam) y r w i j) 0 0 := by
      have hf := hN.framedNormalMetric_first_zero hΩ hB.1 hK hy hyΩ (e lam) he w i j
      simpa only [framedNormalMetric_eq_normalizedBallMetric (γ lam) (E lam) hE (e lam) y] using hf
    have h := ((hN' i j).add (hN' j i)).const_mul (1/2 : ℝ)
    simpa only [W,symmetrizedNormalMetric,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,
      Matrix.transpose_apply,Pi.add_apply,add_zero,mul_zero] using h
  have hRad (i j : I (n+1)) : HasDerivAt (fun r => radializedMetric radialCutoff (W r) w i j) 0 0 := by
    let O := coordinateMatrix (radialReflection w)
    have hCon := hasDerivAt_sandwich_entry_zero hEntry Oᵀ O i j
    have h := ((hEntry i j).const_mul (1-radialCutoff w/2)).fun_add ((hCon).const_mul (radialCutoff w/2))
    simpa only [radializedMetric,O,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Pi.add_apply,mul_zero,add_zero] using h
  have hRef : HasDerivAt ref 0 0 := hasDerivAt_matrix_zero_of_entries
    (hasDerivAt_sandwich_entry_zero hRad Lᵀ L)
  have hInvF := ((hasFDerivAt_inverseMatrix_of_isUnit (ref 0) hRefPos.self_of_nhds.isUnit).comp_hasDerivAt 0 hRef).congr_deriv (map_zero _)
  have hInvE (i j : I (n+1)) : HasDerivAt (fun r => (ref r)⁻¹ i j) 0 0 := by
    let A : Mat (n+1) →L[ℝ] ℝ := (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
    have h := (A.hasFDerivAt.comp_hasDerivAt 0 hInvF).congr_deriv (map_zero A)
    exact h
  let A (r : ℝ) (i j : I n) := SignedPoissonCollar.tangential G C.pole (((P0 r,ν),x),0) i j
  have hA (i j : I n) : HasDerivAt (fun r => A r i j) 0 0 := by
    have hDen : (ref 0)⁻¹ 0 0 ≠ 0 := (inverseRadial_pos_of_posDef (g := fun _ => ref 0)
      (q := (x,0)) hRefPos.self_of_nhds).ne'
    have h := (hInvE i.succ j.succ).fun_div (hInvE 0 0) hDen
    have h' : HasDerivAt (fun r => (ref r)⁻¹ i.succ j.succ / (ref r)⁻¹ 0 0) 0 0 := by
      simpa only [Pi.div_apply,zero_mul,mul_zero,sub_self,zero_div] using h
    apply h'.congr_of_eventuallyEq
    filter_upwards [hRefPos,hα,hConf] with r hr ha heq
    exact normalizedCollarMetric_continuous_radius_cancel ha hr heq i j
  let Q (r : ℝ) := ∑ i : I n, ∑ j : I n, A r i j * ζ i * ζ j
  have hQ : HasDerivAt Q 0 0 := by
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      HasDerivAt.fun_sum (u := Finset.univ) fun j _ => ((hA i j).mul_const (ζ i)).mul_const (ζ j)
    simpa only [Q,zero_mul,Finset.sum_const_zero] using h
  have hQ0 : 0 < Q 0 := by
    have hPM := C.metric_posDef (q := (((P0 0,ν),x),(0 : ℝ))) (hCollar 0 hG0)
    have hp := collarTangential_posDef (g := SignedPoissonCollar.metric G C.pole (P0 0,ν))
      (q := (x,0)) hPM
    change 0 < metricPair (fun _ => A 0) 0 ζ ζ
    exact metricPair_pos_of_posDef hp (smul_ne_zero (by positivity) hν)
  change HasDerivAt (fun r => Real.sqrt (Q r)) 0 0
  simpa only [zero_div] using hQ.sqrt hQ0.ne'

end CalderonPaper
