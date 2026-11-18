import Proof.UniformNormalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 15
open Set
namespace ShrinkingSpheres

lemma norm_map_bounds_of_half_sub_id (L : X →L[ℝ] X)
    (hSmall : ‖L-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ)) (u : X) :
    ‖u‖ ≤ 2*‖L u‖ ∧ ‖L u‖ ≤ 2*‖u‖ := by
  have hDiff : ‖L u-u‖ ≤ (1/2:ℝ)*‖u‖ := by
    have hd := (L-ContinuousLinearMap.id ℝ X).le_opNorm u
    change ‖L u-u‖ ≤ ‖L-ContinuousLinearMap.id ℝ X‖*‖u‖ at hd
    exact hd.trans (mul_le_mul_of_nonneg_right hSmall (norm_nonneg u))
  have hLower : ‖u‖ ≤ ‖L u‖+‖L u-u‖ := by
    calc
      ‖u‖ = ‖L u-(L u-u)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hUpper : ‖L u‖ ≤ ‖L u-u‖+‖u‖ := by
    simpa only [sub_add_cancel] using norm_add_le (L u-u) u
  constructor <;> nlinarith only [hDiff,hLower,hUpper,norm_nonneg u]

lemma metricPair_pullback_bounds {Ω : Set X} {K : ℝ} {g : MetricField}
    (hg : Elliptic Ω K g) (hK : 0 < K) {x : X} (hx : x ∈ Ω)
    (L : X →L[ℝ] X) (hSmall : ‖L-ContinuousLinearMap.id ℝ X‖ ≤ (1/2:ℝ)) (u : X) :
    ‖u‖^2 ≤ 4*K*metricPair g x (L u) (L u) ∧
      metricPair g x (L u) (L u) ≤ 4*K*‖u‖^2 := by
  obtain ⟨hLo,hHi⟩ := norm_map_bounds_of_half_sub_id L hSmall u
  have hsLo := (sq_le_sq₀ (norm_nonneg u) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg (L u)))).2 hLo
  have hsHi := (sq_le_sq₀ (norm_nonneg (L u)) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (norm_nonneg u))).2 hHi
  have hgLo := ((hg.2 x hx).2 (L u)).1
  have hgHi := ((hg.2 x hx).2 (L u)).2
  have hLo' : ‖L u‖^2 ≤ K*metricPair g x (L u) (L u) := by
    simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul] using mul_le_mul_of_nonneg_left hgLo hK.le
  constructor
  · nlinarith only [hsLo,mul_le_mul_of_nonneg_left hLo' (by norm_num : (0:ℝ) ≤ 4)]
  · nlinarith only [hgHi,mul_le_mul_of_nonneg_left hsHi hK.le]

lemma scaled_unitDisk_mem_disk (g : MetricField) (y w : X) (s : ℝ) (hw : w ∈ disk g y 1) :
    s • w ∈ disk g y s := by
  have hUpper : metricPair g y w w ≤ 1 := by simpa only [disk,one_pow,mem_setOf_eq] using hw
  change metricPair g y (s • w) (s • w) ≤ s^2
  rw [metricPair_smul_left,metricPair_smul_right]
  have hh := mul_le_mul_of_nonneg_left hUpper (sq_nonneg s)
  nlinarith only [hh]

lemma Admissible.endpoint_unitDisk_mem {Y Ω : Set X}
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y : X} (hy : y ∈ Y)
    (w : X) (hw : w ∈ disk d.γ y 1) : d.expMap (y,d.radius y • w) ∈ Ω := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hwd := scaled_unitDisk_mem_disk d.γ y w (d.radius y) hw
  have hv : d.radius y • w ∈ disk d.γ y (max ρ (d.radius y)) :=
    hwd.trans ((sq_le_sq₀ hr.le (hr.le.trans (le_max_right ..))).2 (le_max_right ..))
  exact ((hd.2.1.2 y hy).2.2 (d.radius y • w) hv).1

/-- Uniform ellipticity of both actual metric pullbacks on the entire rescaled
    closed normal ball, with constants determined by the frozen hypotheses. -/
theorem uniform_normal_pullback_bounds {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ w ∈ disk d.γ y 1,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ u : X,
      ‖u‖^2 ≤ 4*K*normalPullbackMetricPair g d.expMap y (d.radius y) w u u ∧
      normalPullbackMetricPair g d.expMap y (d.radius y) w u u ≤ 4*K*‖u‖^2 := by
  obtain ⟨η,hη,hInv⟩ := uniform_normal_inverse_bound hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,hη,?_⟩
  intro floor hf ε hε hSmall d hd y hy w hw g hg u
  have hHalf := (hInv floor hf ε hε hSmall d hd y hy w hw).1
  have hEll : Elliptic Ω K g := by
    simp only [mem_insert_iff,mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hd.1.1
    · exact hd.1.2.1
  have hb := metricPair_pullback_bounds hEll (zero_lt_one.trans_le hK)
    (hd.endpoint_unitDisk_mem hy w hw) (normalVerticalJacobian d.expMap y (d.radius y • w)) hHalf u
  simpa only [normalPullbackMetricPair,normalVerticalJacobian,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] using hb

end ShrinkingSpheres
