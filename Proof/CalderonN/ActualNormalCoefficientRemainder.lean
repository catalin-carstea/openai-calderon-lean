module

public import Proof.CalderonN.ActualNormalCoefficientDomain
public import Proof.CalderonN.NormalRadialTaylorJets

import Proof.CalderonN.EnlargedNormalInverse
import Proof.CalderonN.LocalFlowVariation
import Mathlib.Tactic

/-! A quadratic remainder for the actual normalized first coefficient,
with the base, signed radius and direction independent. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 5800000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

@[expose] def actualNormalVelocityField (d : Data dim) (p : X dim × X dim) : Mat dim :=
  firstNormalVelocityCoefficient d p.1 p.2

@[expose] def actualNormalCoefficientRadialRemainder (d : Data dim)
    (a : NormalCoefficientRadialParameter dim) : Mat dim :=
  normalRadialTaylorRemainder (actualNormalVelocityField d) a

private theorem scaled_disk_of_abs_le_radius {g : MetricField dim} {y w : X dim} {r s L t : ℝ}
    (hr : 0 < r) (hs : |s| ≤ r) (ht : t ∈ Icc (0:ℝ) 1) (hw : w ∈ disk g y L)
    (hNonneg : 0 ≤ metricPair g y w w) :
    (t*s/r) • w ∈ disk g y L := by
  have hRatio : |t*s/r| ≤ 1 := by
    rw [abs_div,abs_mul,abs_of_pos hr,abs_of_nonneg ht.1,div_le_iff₀ hr,one_mul]
    exact (mul_le_of_le_one_left (abs_nonneg s) ht.2).trans hs
  have hSq : (t*s/r)^2 ≤ (1:ℝ)^2 := sq_le_sq.mpr (by simpa only [abs_one] using hRatio)
  have hw' : metricPair g y w w ≤ L^2 := hw
  change metricPair g y ((t*s/r) • w) ((t*s/r) • w) ≤ L^2
  rw [metricPair_smul_left,metricPair_smul_right]
  calc
    _ = (t*s/r)^2*metricPair g y w w := by ring
    _ ≤ 1*metricPair g y w w := mul_le_mul_of_nonneg_right (by simpa only [one_pow] using hSq) hNonneg
    _ ≤ L^2 := by simpa only [one_mul] using hw'

/-- Uniform control of the entire signed segment used to take Taylor
remainders, with a compact bound for the independent direction. -/
theorem uniform_actual_normal_radial_segment {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ, 0 < η ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ y ∈ Y, ∀ s : ℝ, |s| ≤ d.radius y → ∀ w ∈ disk d.γ y L,
        s ∈ Icc (-1:ℝ) 1 ∧ w ∈ closedBall (0:X dim) (K*L) ∧
        ∀ t ∈ Icc (0:ℝ) 1,
          let v := (t*s) • w
          v ∈ disk d.γ y (max ρ (d.radius y)) ∧ metricPair d.γ y v v < (max ρ (d.radius y))^2 ∧
            ‖v‖ ≤ 1 ∧ ‖normalVerticalJacobian d.expMap y v-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) := by
  obtain ⟨η₀,hη₀,hGeometry⟩ := uniform_normal_control_on_disk (Y:=Y)
    hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨min η₀ (min 1 (ρ/(2*(L+1)))),lt_min hη₀ (lt_min zero_lt_one (by positivity)),?_⟩
  intro floor hf ε he hs d hd y hy s hsR w hw
  let r := d.radius y
  have hKp := zero_lt_one.trans_le hK
  have hbg := hd.1
  have hYΩ := hd.2.1.center_mem hy
  have hr : 0 < r := (hd.2.2.2.2.1.2 y hy).1
  have hrε : r ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀
    (hf.trans (hd.2.2.2.2.1.2 y hy).2.1))).trans (hd.2.2.2.2.2 y hy).2
  have hs₁ : |s| ≤ 1 := hsR.trans (hrε.trans (hs.trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hrL : r*L < ρ := by
    have h := (le_div_iff₀ (show 0 < 2*(L+1) by positivity)).mp
      (hrε.trans (hs.trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith only [h,hr,hρ]
  have hWnorm : ‖w‖ ≤ K*L := by
    have hG := ((hbg.1.2 y hYΩ).2 w).1
    have hwQ : metricPair d.γ y w w ≤ L^2 := hw
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    have h := mul_le_mul_of_nonneg_left (hG.trans hwQ) hKp.le
    rw [← mul_assoc,mul_inv_cancel₀ hKp.ne',one_mul] at h
    refine h.trans ?_
    have hK₂ : K ≤ K^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_right hK₂ (sq_nonneg L)).trans_eq (by ring)
  have hGeom (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      let v := (t*s) • w
      v ∈ disk d.γ y (max ρ r) ∧ metricPair d.γ y v v < (max ρ r)^2 ∧ ‖v‖ ≤ 1 ∧
        ‖normalVerticalJacobian d.expMap y v-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) := by
    dsimp only
    let u := (t*s/r) • w
    have hQ := (hbg.1.2 y hYΩ).2 w
    have hPos : 0 ≤ metricPair d.γ y w w := (mul_nonneg (inv_nonneg.mpr hKp.le) (sq_nonneg _)).trans hQ.1
    have hu : u ∈ disk d.γ y L := scaled_disk_of_abs_le_radius hr hsR ht hw hPos
    have huv : r • u = (t*s) • w := by
      rw [show u = (t*s/r) • w from rfl,smul_smul,show r*(t*s/r) = t*s by field_simp]
    have hControl := hGeometry floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy u hu
    rw [huv] at hControl
    have hR : metricPair d.γ y ((t*s) • w) ((t*s) • w) < (max ρ r)^2 := by
      rw [← huv,metricPair_smul_left,metricPair_smul_right]
      have hLq : metricPair d.γ y u u ≤ L^2 := hu
      have h := mul_le_mul_of_nonneg_left hLq (sq_nonneg r)
      have hR' : 0 ≤ r*L := by positivity
      nlinarith only [h,hrL,hR',sq_lt_sq₀ hR' hρ.le |>.2 hrL,
        sq_le_sq₀ hρ.le (hρ.le.trans (le_max_left _ _)) |>.2 (le_max_left ρ r)]
    exact ⟨hR.le,hR,hControl.1.2,hControl.2.2.2.1⟩
  exact ⟨abs_le.mp hs₁,by simpa only [mem_closedBall,dist_zero_right] using hWnorm,hGeom⟩

/-- Enlarging the permitted directions controls a neighborhood of the
physical radius in the independent signed-radius parameter. -/
theorem uniform_actual_normal_radial_segment_enlarged {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ, 0 < η ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      ∀ y ∈ Y, ∀ s : ℝ, |s| ≤ 2*d.radius y → ∀ w ∈ disk d.γ y L,
        s ∈ Icc (-1:ℝ) 1 ∧ w ∈ closedBall (0:X dim) (K*L) ∧
        ∀ t ∈ Icc (0:ℝ) 1,
          let v := (t*s) • w
          v ∈ disk d.γ y (max ρ (d.radius y)) ∧ metricPair d.γ y v v < (max ρ (d.radius y))^2 ∧
            ‖v‖ ≤ 1 ∧ ‖normalVerticalJacobian d.expMap y v-ContinuousLinearMap.id ℝ (X dim)‖ ≤ (1/2:ℝ) := by
  obtain ⟨η,hη,hControl⟩ := uniform_actual_normal_radial_segment (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ
    (2*L) (by positivity)
  refine ⟨min η (1/2),lt_min hη (by norm_num),?_⟩
  intro floor hf ε he hε d hd y hy s hs w hw
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hβ := hf.trans (hd.2.2.2.2.1.2 y hy).2.1
  have hrε : d.radius y ≤ ε := (le_mul_of_one_le_right hr.le (one_le_pow₀ hβ)).trans
    (hd.2.2.2.2.2 y hy).2
  have hs₁ : |s| ≤ 1 := hs.trans (by linarith [hε.trans (min_le_right η (1/2:ℝ))])
  have hs₂ : |s/2| ≤ d.radius y := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hw₂ : (2:ℝ) • w ∈ disk d.γ y (2*L) := by
    change metricPair d.γ y ((2:ℝ) • w) ((2:ℝ) • w) ≤ (2*L)^2
    rw [metricPair_smul_left,metricPair_smul_right]
    have hh : metricPair d.γ y w w ≤ L^2 := hw
    nlinarith only [hh]
  obtain ⟨_,hW,hRay⟩ := hControl floor hf ε he (hε.trans (min_le_left _ _)) d hd y hy (s/2) hs₂ ((2:ℝ) • w) hw₂
  have hW₁ : w ∈ closedBall (0:X dim) (K*L) := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hW
    rw [mem_closedBall,dist_zero_right]
    linarith only [hW]
  refine ⟨abs_le.mp hs₁,hW₁,fun t ht => ?_⟩
  have h := hRay t ht
  dsimp only at h ⊢
  rwa [smul_smul,show t*(s/2)*2 = t*s by ring] at h

theorem uniform_actual_normalCoefficient_radialRemainder
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∀ s : ℝ, |s| ≤ 2*d.radius y → ∀ w ∈ disk d.γ y L,
        LocalSmoothJetBudget (actualNormalCoefficientRadialRemainder d) (y,(s,w)) N C ∧
        actualNormalVelocityField d (y,s • w) =
          actualNormalVelocityField d (y,0)+
            s • fderiv ℝ (actualNormalVelocityField d) (y,0) (0,w)+
            s^2 • actualNormalCoefficientRadialRemainder d (y,(s,w)) := by
  obtain ⟨η,hη,hGeometry⟩ := uniform_actual_normal_radial_segment_enlarged (Y:=Y)
    hΩ (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨CA,hCA,hA⟩ := uniform_actual_firstNormalVelocityCoefficient_jets hY hΩ
    (N+2) (by omega) K ρ c₀ M Cj hK
  obtain ⟨C,hC,hTaylor⟩ := exists_uniform_normalRadialTaylorRemainder_jets
    (E:=Mat dim) hYc (K*L) N CA (zero_le_one.trans hCA)
  refine ⟨η,C,hη,hC,?_⟩
  intro floor hf ε he hs d hd hdFrame y hy s hsR w hw
  obtain ⟨hs₁,hw₁,hGeom⟩ := hGeometry floor hf ε he hs d hd y hy s hsR w hw
  obtain ⟨U,hU,hTube,hF⟩ := smoothNear_actual_firstNormalVelocityCoefficient hΩ (zero_lt_one.trans_le hK) hd
  exact hTaylor _ U hU hF y (subset_closure hy) s hs₁ w hw₁
    (fun t ht => hTube ⟨hy,(hGeom t ht).1,((hGeom t ht).2.2.2).trans_lt (by norm_num)⟩)
    (fun t ht => hA floor ε d hd hdFrame y hy ((t*s) • w) (hGeom t ht).2.1
      (hGeom t ht).2.2.1 (hGeom t ht).2.2.2)

end CalderonN
