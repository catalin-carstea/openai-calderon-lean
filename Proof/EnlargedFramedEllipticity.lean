import Proof.EnlargedNormalInverse
import Proof.FramedNormalRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

lemma frameVector_mem_disk (g : MetricField) (e : Frame) (y z : X) (L : ℝ)
    (hframe : ∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    (hz : z ∈ Metric.closedBall (0:X) L) : frameVector e y z ∈ disk g y L := by
  have hzNorm : ‖z‖ ≤ L := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
  change metricPair g y (frameVector e y z) (frameVector e y z) ≤ L^2
  rw [metricPair_frameVector_self g e y z hframe]
  exact (sq_le_sq₀ (norm_nonneg z) ((norm_nonneg z).trans hzNorm)).2 hzNorm

/-- Uniform smooth ellipticity on an arbitrary fixed enlarged rescaled ball. In
    particular L=2 supplies the coefficient neighborhood required by the supplied
    fixed-ball Dirichlet regularity theorem. -/
theorem uniform_enlarged_framed_normal_elliptic {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),
      Elliptic (Metric.closedBall (0:X) L) (4*K^2)
        (framedNormalMetric g d.frame d.expMap y (d.radius y)) := by
  obtain ⟨η,hη,hInv⟩ := uniform_normal_inverse_bound_on_disk hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hEll : Elliptic Ω K g := by
    have hh := hmem
    simp only [mem_insert_iff,mem_singleton_iff] at hh
    rcases hh with rfl | rfl
    · exact hd.1.1
    · exact hd.1.2.1
  have hcenter := hd.2.1.center_mem hy
  have hframe := hd.1.2.2.2.2.2.2.2 y hcenter
  have hPack (z : X) (hz : z ∈ Metric.closedBall (0:X) L) :=
    hInv floor hf ε hε hSmall d hd y hy (frameVector d.frame y z)
      (frameVector_mem_disk d.γ d.frame y z L hframe hz)
  refine ⟨?_,?_⟩
  · intro i j z hz
    exact (ShrinkingSpheres.contDiffAt_framedNormalMetric_entry g d.frame d.expMap y z (d.radius y) i j
      (hPack z hz).2.1 (fun a b => (hEll.1 a b).contDiffAt (hΩ.mem_nhds (hPack z hz).1))).contDiffWithinAt
  · intro z hz
    refine ⟨framedNormalMetric_symmetric g d.frame d.expMap y z (d.radius y) (hEll.2 _ (hPack z hz).1).1,?_⟩
    intro u
    have hF := hd.1.1.frameVector_norm_sq_bounds hKpos hcenter d.frame hframe u
    have hb0 := metricPair_pullback_bounds hEll hKpos (hPack z hz).1
      (normalVerticalJacobian d.expMap y (d.radius y • frameVector d.frame y z)) (hPack z hz).2.2.1
      (frameVector d.frame y u)
    have hb : ‖frameVector d.frame y u‖^2 ≤ 4*K*normalPullbackMetricPair g d.expMap y (d.radius y)
        (frameVector d.frame y z) (frameVector d.frame y u) (frameVector d.frame y u) ∧
        normalPullbackMetricPair g d.expMap y (d.radius y) (frameVector d.frame y z)
          (frameVector d.frame y u) (frameVector d.frame y u) ≤ 4*K*‖frameVector d.frame y u‖^2 := by
      simpa only [normalPullbackMetricPair,normalVerticalJacobian,ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] using hb0
    rw [← framedNormalMetric_pair g d.frame d.expMap y z u u (d.radius y)] at hb
    have hLo : ‖u‖^2 ≤ (4*K^2)*metricPair (framedNormalMetric g d.frame d.expMap y (d.radius y)) z u u := by
      have hh := hF.1.trans (mul_le_mul_of_nonneg_left hb.1 hKpos.le)
      convert hh using 1 <;> ring
    have hHi : metricPair (framedNormalMetric g d.frame d.expMap y (d.radius y)) z u u ≤ (4*K^2)*‖u‖^2 := by
      have hh := hb.2.trans (mul_le_mul_of_nonneg_left hF.2 (show 0 ≤ 4*K by positivity))
      convert hh using 1 <;> ring
    have hConst : 0 < 4*K^2 := by positivity
    refine ⟨?_,hHi⟩
    have hh := mul_le_mul_of_nonneg_left hLo (inv_nonneg.mpr hConst.le)
    simpa only [← mul_assoc,inv_mul_cancel₀ hConst.ne',one_mul] using hh

end ShrinkingSpheres
