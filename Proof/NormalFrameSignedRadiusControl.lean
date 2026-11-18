import Proof.EnlargedNormalInverse
import Proof.NormalDiskInterior
import Proof.NormalFrameNormalizationGerms

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

lemma orthonormal_linear_scaled_mem_disk (g : MetricField) (y : X) (L : X →L[ℝ] X)
    (he : ∀ i j,metricPair g y (L (axis i)) (L (axis j)) = if i=j then 1 else 0)
    (s r Z : ℝ) (hr : 0 < r) (hs : |s| ≤ r) (hZ : 0 ≤ Z) (z : X) (hz : ‖z‖ ≤ Z) :
    (s/r) • L z ∈ disk g y Z := by
  have hAlpha : |s/r| ≤ 1 := by
    rw [abs_div,abs_of_pos hr]
    exact (div_le_one hr).mpr hs
  have hAlphaSq : (s/r)^2 ≤ 1 := by
    have hh := (sq_le_sq₀ (abs_nonneg (s/r)) zero_le_one).mpr hAlpha
    simpa only [sq_abs,one_pow] using hh
  have hZSq : ‖z‖^2 ≤ Z^2 := (sq_le_sq₀ (norm_nonneg z) hZ).mpr hz
  change metricPair g y ((s/r) • L z) ((s/r) • L z) ≤ Z^2
  rw [metricPair_smul_left,metricPair_smul_right,
    metricPair_orthonormal_linear g (y,(0,L)) he z z,real_inner_self_eq_norm_sq]
  have hh := mul_le_mul_of_nonneg_right hAlphaSq (sq_nonneg ‖z‖)
  nlinarith only [hh,hZSq]

/-- Existing enlarged normal-coordinate control applies at every signed
    smaller radius and every pointwise orthonormal linear frame. -/
theorem uniform_normalFrame_signed_radius_control {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (Z : ℝ) (hZ : 0 ≤ Z) :
    ∃ η : ℝ,0 < η ∧ η ≤ 1 ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ L : X →L[ℝ] X,
      (∀ i j,metricPair d.γ y (L (axis i)) (L (axis j)) = if i=j then 1 else 0) →
      ∀ s : ℝ,|s| ≤ d.radius y → ∀ z : X,‖z‖ ≤ Z →
      (metricPair d.γ y (s • L z) (s • L z) < (max ρ (d.radius y))^2 ∧ ‖s • L z‖ ≤ 1) ∧
      d.expMap (y,s • L z) ∈ Ω ∧ ContDiffAt ℝ ∞ d.expMap (y,s • L z) ∧
      ‖normalVerticalJacobian d.expMap y (s • L z)-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ) ∧
      ‖(normalVerticalJacobian d.expMap y (s • L z)).inverse‖ ≤ 2 := by
  obtain ⟨η,hη,hControl⟩ := uniform_normal_control_on_disk (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ Z hZ
  refine ⟨min η 1,lt_min hη zero_lt_one,min_le_right _ _,?_⟩
  intro floor hf ε hε hSmall d hd y hy L he s hs z hz
  have hr := (hd.2.2.2.2.1.2 y hy).1
  let w := (s/d.radius y) • L z
  have hw : w ∈ disk d.γ y Z := orthonormal_linear_scaled_mem_disk d.γ y L he
    s (d.radius y) Z hr hs hZ z hz
  have hEq : d.radius y • w = s • L z := by
    dsimp only [w]
    rw [smul_smul]
    congr 1
    field_simp
  have hPack := hControl floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy w hw
  rw [hEq] at hPack
  exact ⟨⟨metricPair_lt_of_mem_interior_disk d.γ y (s • L z) _
      (hρ.trans_le (le_max_left _ _)) hPack.1.1,hPack.1.2⟩,hPack.2⟩

lemma Admissible.normal_radius_continuousAt {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y) :
    ContinuousAt (fun x => max ρ (d.radius x)) y :=
  continuousAt_const.max ((hd.2.2.2.2.1.1.contDiffAt (hY.mem_nhds hy)).continuousAt)

end ShrinkingSpheres
