module

public import Proof.CalderonN.FramedJacobiBound

import Proof.CalderonN.JacobiCurvatureBounds
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

set_option maxHeartbeats 1000000 in
/-- On an actual shrinking sphere, the squared-distance Hessian is
bounded by the difference of the endpoint vectors in one transported
frame, with an error of order the squared physical radius. The frame
depends only on the radial geodesic and is shared by all test vectors. -/
theorem exists_normalTransported_hessian_lower
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {γ : (MetricField dim)} (hγ : SmoothMetric univ γ) {R : ℝ}
    {E V : (X dim) × (X dim) → (X dim)} (hE : ContDiff ℝ ∞ E)
    (hN : NormalCoordinates Y Ω γ E (fun _ => R))
    {r : (X dim) → ℝ} (hr : ContDiffOn ℝ ∞ r Y) (hYΩ : Y ⊆ Ω)
    (hD : IsOpen (normalPairDomain Y γ R E))
    (hV : ContDiffOn ℝ ∞ V (normalPairDomain Y γ R E))
    (hinv : ∀ p ∈ normalPairDomain Y γ R E,
      (p.2,V p) ∈ normalVelocityDomain Y γ R ∧ E (p.2,V p) = p.1)
    {p : (X dim) × (X dim)} (hp : p ∈ normalPairDomain Y γ R E)
    (hsphere : normalPhase γ V r p = 0)
    (e : (I dim) → (X dim)) (he : ∀ i j, metricPair γ p.2 (e i) (e j) = if i = j then 1 else 0)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 < K) (hsmall : B * K^2 * (r p.2)^2 ≤ 1/2)
    (hell : ∀ x ∈ Ω, ∀ u, K⁻¹ * ‖u‖^2 ≤ metricPair γ x u u ∧
      metricPair γ x u u ≤ K * ‖u‖^2)
    (hcurv : ∀ x ∈ Ω, ∀ v J : (X dim), ‖jacobiCurvatureTerm γ x v J‖ ≤ B * ‖v‖^2 * ‖J‖) :
    let a (t : ℝ) := E (p.2,t • V p)
    ∃ F : ℝ → (I dim) → (X dim), (∀ i, ContDiff ℝ ∞ (fun t => F t i)) ∧
      (∀ i, F 0 i = e i) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ s in 𝓝 t,
        (∀ i, HasDerivAt (fun u => F u i)
          (-connection γ (a s) (deriv a s) (F s i)) s) ∧
        ∀ i j, metricPair γ (a s) (F s i) (F s j) = if i = j then 1 else 0) ∧
      ∀ u : (X dim) × (X dim),
        let U₁ := frameCoordinates γ p.1 (F 1) u.1
        let U₂ := frameCoordinates γ p.2 (F 0) u.2
        ‖U₁ - U₂‖^2 - 2 * (B * K^2 * (r p.2)^2) * (‖U₂‖ + ‖U₁‖)^2 -
          fderiv ℝ r p.2 u.2 ^ 2 -
          r p.2 * (fderiv ℝ (fderiv ℝ r) p.2 u.2 u.2 -
            fderiv ℝ r p.2 (connection γ p.2 u.2 u.2)) ≤
          productMetricHessian γ γ (normalPhase γ V r) p u u := by
  let a (t : ℝ) := E (p.2,t • V p)
  have ha : ContDiff ℝ ∞ a :=
    hE.comp (contDiff_const.prodMk (contDiff_id.smul contDiff_const))
  have hγΩ : SmoothMetric Ω γ := ⟨fun i j => (hγ.1 i j).mono (subset_univ _),
    fun x _ => hγ.2 x (mem_univ _)⟩
  obtain ⟨⟨hy,hv⟩,_⟩ := hinv p hp
  have hzero : a 0 = p.2 := ((hN.2 p.2 hy).2.2 (V p) hv.le).2.2.1
  obtain ⟨F,hF,hF₀,hTransport⟩ := exists_parallelFrame hγ ha e
  have hDframe (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun u => F u i)
        (-connection γ (a s) (deriv a s) (F s i)) s) ∧
      ∀ i j, metricPair γ (a s) (F s i) (F s j) = if i = j then 1 else 0 := by
    filter_upwards [hTransport t ht] with s hs
    exact ⟨hs.1,fun i j => (hs.2 i j).trans (by simpa only [hzero] using he i j)⟩
  refine ⟨F,hF,hF₀,hDframe,fun u => ?_⟩
  obtain ⟨q,hq,hbase,hq₀,hq₁,hv₀,hJ₀,hJ₁,hfamily,hH⟩ :=
    exists_normalPhase_jacobi_boundary hY hΩ hγΩ hE hN hr hYΩ hD hV hinv hp u
  have hbaseEq : (fun s : ℝ => q (0,s)) = a := funext hbase
  have hvel (s : ℝ) : deriv a s = timeVelocity q (0,s) := by
    rw [← hbaseEq]
    exact (hasDerivAt_geodesicTime (hq.differentiable (by simp) (0,s))).deriv
  have hFrameQ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∀ᶠ s in 𝓝 t,
      (∀ i, HasDerivAt (fun u => F u i)
        (-connection γ (q (0,s)) (timeVelocity q (0,s)) (F s i)) s) ∧
      ∀ i j, metricPair γ (q (0,s)) (F s i) (F s j) = if i = j then 1 else 0 := by
    filter_upwards [hDframe t ht] with s hs
    rw [hbase s, ← hvel s]
    exact hs
  have hspeed (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      metricPair γ (q (0,t)) (timeVelocity q (0,t)) (timeVelocity q (0,t)) ≤ (r p.2)^2 := by
    rw [geodesic_squaredSpeed_eq_initial hΩ hγΩ hq hfamily.self_of_nhds ht,hq₀,hv₀]
    unfold normalPhase at hsphere
    linarith
  have hBnd := framed_jacobi_boundary_lower_of_curvature hγ hq
    (hfamily.mono fun _ hs t ht => (hs t ht).2) F hF hFrameQ hB hK hsmall
    (fun t ht => hell _ (hfamily.self_of_nhds t ht).1)
    (fun t ht => hcurv _ (hfamily.self_of_nhds t ht).1) hspeed
  simp only [hq₀,hq₁,hJ₀,hJ₁] at hBnd
  rw [hH u]
  dsimp only
  rw [pow_two (fderiv ℝ r p.2 u.2)]
  exact sub_le_sub_right (sub_le_sub_right hBnd _) _

end CalderonN
