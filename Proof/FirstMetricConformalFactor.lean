import Proof.NormalCenterConformal
import Proof.NormalPullbackMetric

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- A canonical smooth conformal scale from the actual two metric fields. -/
def firstMetricConformalFactor (γ g₁ : MetricField) (x : X) : ℝ := g₁ x 0 0/γ x 0 0

lemma Elliptic.diagonal_entry_pos {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (i : I) : 0 < g x i i := by
  have hh := ((hg.2 x hx).2 (axis i)).1
  have hEntry : metricPair g x (axis i) (axis i) = g x i i := by simp [metricPair,axis]
  rw [hEntry,norm_axis,one_pow,mul_one] at hh
  exact (inv_pos.mpr hK).trans_le hh

lemma Background.firstMetricConformalFactor_pos {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    0 < firstMetricConformalFactor γ g₁ x :=
  div_pos (hB.2.1.diagonal_entry_pos hK hx 0) (hB.1.diagonal_entry_pos hK hx 0)

theorem Background.firstMetricConformalFactor_smooth {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) :
    ContDiffOn ℝ ∞ (firstMetricConformalFactor γ g₁) Ω :=
  (hB.2.1.1 0 0).div (hB.1.1 0 0) (fun x hx => (hB.1.diagonal_entry_pos hK hx 0).ne')

/-- Pointwise conformality is realized by the canonical smooth factor. -/
theorem Background.firstMetric_eq_conformalFactor {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) :
    g₁ x = firstMetricConformalFactor γ g₁ x • γ x := by
  obtain ⟨a,ha,hMetric⟩ := hB.2.2.2.1 x hx
  have h00 : γ x 0 0 = a*g₁ x 0 0 := by
    simpa only [Matrix.smul_apply,smul_eq_mul] using congrArg (fun A : Mat => A 0 0) hMetric
  have hg0 := (hB.2.1.diagonal_entry_pos hK hx 0).ne'
  have hFactor : firstMetricConformalFactor γ g₁ x = a⁻¹ := by
    dsimp [firstMetricConformalFactor]
    rw [h00]
    field_simp
  rw [hFactor,hMetric,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]

lemma Background.firstMetricPair_eq_conformalFactor {Ω : Set X} {K : ℝ} {m : ℕ}
    {M : Fin (m+1) → ℝ} {γ g₁ g₂ : MetricField} {e : Frame}
    (hB : Background Ω K M γ g₁ g₂ e) (hK : 0 < K) {x : X} (hx : x ∈ Ω) (u v : X) :
    metricPair g₁ x u v = firstMetricConformalFactor γ g₁ x*metricPair γ x u v := by
  calc
    _ = metricPair (fun z => firstMetricConformalFactor γ g₁ x • γ z) x u v := by
      simp only [metricPair,hB.firstMetric_eq_conformalFactor hK hx]
    _ = _ := metricPair_scale_metric γ _ x u v

end ShrinkingSpheres
