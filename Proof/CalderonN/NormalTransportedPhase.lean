module

public import Proof.CalderonN.NormalHessianBound
public import Proof.CalderonN.RadiusHessianBound

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 1400000 in
/-- For the same transported identification at both endpoints, the phase
covectors have the normal forms from the source, and its Hessian has the
profile gain and the quadratic curvature loss. -/
theorem exists_normalPhase_framed_estimates
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {R : ℝ}
    {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => R))
    {r : (X dim) → ℝ} (hYΩ : Y ⊆ Ω) {e : (Frame dim)} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ}
    (hprof : Profile Y γ e r floor c₀ Cj)
    (hD : IsOpen (normalPairDomain Y γ R E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ R E))
    (hinv : ∀ p ∈ normalPairDomain Y γ R E,
      (p.2,V p) ∈ normalVelocityDomain Y γ R ∧ E (p.2,V p) = p.1)
    {p : (X dim) × (X dim)} (hp : p ∈ normalPairDomain Y γ R E)
    (hsphere : normalPhase γ V r p = 0)
    (he : ∀ i j, metricPair γ p.2 (e p.2 i) (e p.2 j) = if i = j then 1 else 0)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 < K) (hsmall : B * K^2 * (r p.2)^2 ≤ 1/2)
    (hell : ∀ x ∈ Ω, ∀ u, K⁻¹ * ‖u‖^2 ≤ metricPair γ x u u ∧
      metricPair γ x u u ≤ K * ‖u‖^2)
    (hcurv : ∀ x ∈ Ω, ∀ v J : (X dim), ‖jacobiCurvatureTerm γ x v J‖ ≤ B * ‖v‖^2 * ‖J‖) :
    let direction := (r p.2)⁻¹ • frameCoordinates γ p.2 (e p.2) (V p)
    let b := frameCoordinates γ p.2 (e p.2) (chartMetricGradient γ r p.2)
    ‖direction‖ = 1 ∧ ‖b‖ = r p.2 * beta γ r p.2 ∧
      ∃ e₁ : (I dim) → (X dim), (∀ i j, metricPair γ p.1 (e₁ i) (e₁ j) = if i = j then 1 else 0) ∧
        ∀ u : (X dim) × (X dim),
          let U₁ := frameCoordinates γ p.1 e₁ u.1
          let U₂ := frameCoordinates γ p.2 (e p.2) u.2
          (fderiv ℝ (normalPhase γ V r) p u =
            r p.2 * (⟪direction,U₁⟫_ℝ - ⟪direction+b,U₂⟫_ℝ)) ∧
          ‖U₁-U₂‖^2 - 2*⟪b,U₂⟫_ℝ^2 + c₀ * beta γ r p.2 * (r p.2)^2 * ‖U₂‖^2 -
            (2*B*K^2) * (r p.2)^2 * (‖U₁‖+‖U₂‖)^2 ≤
            productMetricHessian γ γ (normalPhase γ V r) p u u := by
  let a (t : ℝ) := E (p.2,t • V p)
  let direction := (r p.2)⁻¹ • frameCoordinates γ p.2 (e p.2) (V p)
  let b := frameCoordinates γ p.2 (e p.2) (chartMetricGradient γ r p.2)
  have hγΩ : SmoothMetric Ω γ := ⟨fun i j => (hγ.1 i j).mono (subset_univ _),
    fun x _ => hγ.2 x (mem_univ _)⟩
  have hy : p.2 ∈ Y := (hinv p hp).1.1
  have hpos := (hprof.2 p.2 hy).1
  have hrs : ContDiffAt ℝ ∞ r p.2 := hprof.1.contDiffAt (hY.mem_nhds hy)
  have hrD := hrs.differentiableAt (by simp)
  have hdirection₀ : ‖frameCoordinates γ p.2 (e p.2) (V p)‖ = r p.2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) hpos.le).mp
    rw [norm_frameCoordinates_sq γ p.2 (V p) (e p.2) he]
    unfold normalPhase at hsphere
    linarith only [hsphere]
  have hdirection : ‖direction‖ = 1 := by
    rw [show direction = (r p.2)⁻¹ • frameCoordinates γ p.2 (e p.2) (V p) from rfl, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hpos.le),hdirection₀,inv_mul_cancel₀ hpos.ne']
  have hb : ‖b‖ = r p.2 * beta γ r p.2 :=
    norm_framed_radiusGradient_eq (hγ.2 _ (mem_univ _)) _ he hrD hpos
  have hdirectionr : r p.2 • direction = frameCoordinates γ p.2 (e p.2) (V p) := by
    simp only [direction,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
  obtain ⟨F,_,hF₀,hF,hHess⟩ := exists_normalTransported_hessian_lower
    hY hΩ hγ hE hN hprof.1 hYΩ hD hV hinv hp hsphere (e p.2) he hB hK hsmall hell hcurv
  have hF₀eq : F 0 = e p.2 := funext hF₀
  obtain ⟨q,hq,hbase,hq₀,hq₁,hv₀,_,_,hgeom,_⟩ :=
    exists_normalPhase_jacobi_boundary hY hΩ hγΩ hE hN hprof.1 hYΩ hD hV hinv hp 0
  have hbaseEq : (fun s : ℝ => q (0,s)) = a := funext hbase
  let velocity (s : ℝ) := timeVelocity q (0,s)
  have hvel (s : ℝ) : deriv a s = velocity s := by
    rw [← hbaseEq]
    exact (hasDerivAt_geodesicTime (hq.differentiable (by simp) (0,s))).deriv
  have hterminal : terminalVelocity E p.2 (V p) = velocity 1 := hvel 1
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by simp
  have hG₁ (i j : (I dim)) : metricPair γ p.1 (F 1 i) (F 1 j) = if i = j then 1 else 0 := by
    rw [← hq₁,hbase 1]
    exact (hF 1 h1).self_of_nhds.2 i j
  have hTransport : frameCoordinates γ p.1 (F 1) (terminalVelocity E p.2 (V p)) =
      frameCoordinates γ p.2 (e p.2) (V p) := by
    rw [hterminal,← hv₀,← hF₀eq,← hq₀,← hq₁]
    ext i
    change metricPair γ (q (0,1)) (velocity 1) (F 1 i) =
      metricPair γ (q (0,0)) (velocity 0) (F 0 i)
    apply metricPair_parallel_eq_initial hΩ hγΩ (q := fun s => q (0,s)) velocity velocity (fun s => F s i) ?_ ?_ ?_ h1
    · intro s hs
      exact ⟨(hgeom.self_of_nhds s hs).1,hasDerivAt_geodesicTime (hq.differentiable (by simp) (0,s))⟩
    · intro s hs
      have hd := hasDerivAt_geodesicTime ((contDiff_timeVelocity hq).differentiable (by simp) (0,s))
      rw [(hgeom.self_of_nhds s hs).2] at hd
      exact hd
    · intro s hs
      rw [hbase s,← hvel s]
      exact (hF s hs).self_of_nhds.1 i
  refine ⟨hdirection,hb,F 1,hG₁,fun u => ⟨?_,?_⟩⟩
  · rw [fderiv_normalPhase_eq_endpoint_terms hY hΩ hγΩ hE hN hprof.1 hYΩ hD hV hinv hp u,
      ← inner_frameCoordinates γ p.1 _ u.1 (F 1) hG₁, hTransport,
      ← inner_frameCoordinates γ p.2 _ u.2 (e p.2) he, ← hdirectionr,
      fderiv_eq_inner_frameCoordinates_chartMetricGradient γ p.2 u.2 (hγ.2 _ (mem_univ _)) (e p.2) he r]
    simp only [real_inner_smul_left,inner_add_left]
    field_simp [hpos.ne']
    ring
  · have h := hHess u
    simp only [hF₀eq, ← metricHessianEval_eq_fderiv γ
      ((hrs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt] at h
    have hgain := radius_covariantHessian_le_of_profile hY hprof hy u.2
    have hdr := fderiv_eq_inner_frameCoordinates_chartMetricGradient γ p.2 u.2
      (hγ.2 _ (mem_univ _)) (e p.2) he r
    change fderiv ℝ r p.2 u.2 = ⟪b,frameCoordinates γ p.2 (e p.2) u.2⟫_ℝ at hdr
    rw [← norm_frameCoordinates_sq γ p.2 u.2 (e p.2) he,hdr] at hgain
    rw [hdr] at h
    nlinarith only [h,hgain]

end CalderonN
