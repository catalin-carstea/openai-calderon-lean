import Proof.FramedNormalRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- The reference and first metrics, pulled back by the actual normal map and
    expressed in the given orthonormal frame, form a uniformly elliptic smooth
    family on the fixed Euclidean closed unit ball. -/
theorem uniform_framed_normal_elliptic {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),
      Elliptic (Metric.closedBall (0:X) 1) (4*K^2)
        (framedNormalMetric g d.frame d.expMap y (d.radius y)) := by
  obtain ⟨η,hη,hPull⟩ := uniform_normal_pullback_bounds hΩ hm K ρ c₀ M Cj hK hρ
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
  refine ⟨fun i j z hz => (hd.contDiffAt_framedNormalMetric_entry hΩ hy hEll z hz i j).contDiffWithinAt,?_⟩
  intro z hz
  have hw := frameVector_mem_unitDisk d.γ d.frame y z hframe hz
  have hx := hd.endpoint_unitDisk_mem hy _ hw
  refine ⟨framedNormalMetric_symmetric g d.frame d.expMap y z (d.radius y) (hEll.2 _ hx).1,?_⟩
  intro u
  have hF := hd.1.1.frameVector_norm_sq_bounds hKpos hcenter d.frame hframe u
  have hb := hPull floor hf ε hε hSmall d hd y hy _ hw g hmem (frameVector d.frame y u)
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
