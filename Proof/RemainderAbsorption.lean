import Proof.SmoothEnergyRegularity
import Proof.EnergyPositivity
import Proof.PhysicalOutputRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped ContDiff
namespace ShrinkingSpheres

/-- The exact frozen four-term density controls the H¹ mass with the square of the
    admitted profile floor. This is independent of the radius construction. -/
lemma Profile.sobolev_one_density_le {Y : Set X} {g : MetricField} {e : Frame} {r : X → ℝ}
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj) (hfloor : 0 ≤ floor)
    (φ : Field) {y : X} (hy : y ∈ Y) :
    floor^2*(metricDensity g y*sobolevSq g e 1 y (fun w => φ (y,w))) ≤ physicalEnergyDensity g e r φ y := by
  have hb : 0 ≤ beta g r y := Real.sqrt_nonneg _
  have hβ := (hp.2 y hy).2.1
  have hfβ : floor^2 ≤ (beta g r y)^2 := (sq_le_sq₀ hfloor hb).mpr hβ
  have hH : 0 ≤ ∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)) := Finset.sum_nonneg (fun _ _ => fiberSq_nonneg e y _)
  have hHs : 0 ≤ ∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)) := Finset.sum_nonneg (fun _ _ => sobolevSq_nonneg g e _ y _)
  have hhalf := mul_nonneg (inv_nonneg.mpr hb) hHs
  have hthree := mul_nonneg hb (sobolevSq_nonneg g e (3/2) y (fun w => φ (y,w)))
  have hmass := mul_le_mul_of_nonneg_right hfβ (sobolevSq_nonneg g e 1 y (fun w => φ (y,w)))
  have hinside : floor^2*sobolevSq g e 1 y (fun w => φ (y,w)) ≤
      (∑ i,fiberSq e y (fun w => horizontal g φ y w (e y i)))+
        (beta g r y)^2*sobolevSq g e 1 y (fun w => φ (y,w))+
        (beta g r y)⁻¹*(∑ i,sobolevSq g e (1/2) y (fun w => horizontal g φ y w (e y i)))+
        beta g r y*sobolevSq g e (3/2) y (fun w => φ (y,w)) := by linarith
  have hweighted := mul_le_mul_of_nonneg_left hinside (show 0 ≤ metricDensity g y from Real.sqrt_nonneg _)
  simpa only [physicalEnergyDensity,mul_left_comm,mul_assoc] using hweighted

lemma Profile.sobolev_one_mass_le {Y : Set X} (hY : IsOpen Y) {K : ℝ} {g : MetricField}
    (h : Elliptic Y K g) (hK : 0 < K) (e : Frame)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => e x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair g y (e y i) (e y j) = if i = j then 1 else 0)
    {r : X → ℝ} {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y g e r floor c₀ Cj)
    (hfloor : 1 ≤ floor) {φ : Field} (hφ : Test Y g e φ) :
    floor^2*(∫ y in Y,metricDensity g y*sobolevSq g e 1 y (fun w => φ (y,w))) ≤ energySq Y g e r φ := by
  rw [← integral_const_mul,energySq_eq_integral_density]
  apply integral_mono_of_nonneg
    (Eventually.of_forall (fun y => mul_nonneg (sq_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (sobolevSq_nonneg g e _ y _))))
    (hp.integrableOn_physicalEnergyDensity hY h hK e he hframe hfloor hφ)
  filter_upwards [ae_restrict_mem hY.measurableSet] with y hy
  exact hp.sobolev_one_density_le (zero_le_one.trans hfloor) φ hy

/-- An H¹-bounded remainder has exactly the inverse-floor estimate needed by the
    final absorption. The only remaining premise is its actual physical H¹ bound. -/
theorem remainder_norm_le_of_sobolev_one {Y : Set X} (hY : IsOpen Y) {K : ℝ} {d : Data}
    (h : Elliptic Y K d.γ) (hK : 0 < K)
    (he : ∀ i,ContDiffOn ℝ ∞ (fun x => d.frame x i) Y)
    (hframe : ∀ y ∈ Y,∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j) = if i = j then 1 else 0)
    {floor c₀ : ℝ} {Cj : Fin 9 → ℝ} (hp : Profile Y d.γ d.frame d.radius floor c₀ Cj)
    (hfloor : 1 ≤ floor) {φ : Field} (hφ : Test Y d.γ d.frame φ) (J : Output Y d) {C : ℝ} (hC : 0 ≤ C)
    (hJ : ‖J‖^2 ≤ C^2*(∫ y in Y,metricDensity d.γ y*sobolevSq d.γ d.frame 1 y (fun w => φ (y,w)))) :
    ‖J‖ ≤ C/floor*energyNorm Y d φ := by
  have hf : 0 < floor := zero_lt_one.trans_le hfloor
  have hmass := hp.sobolev_one_mass_le hY h hK d.frame he hframe hfloor hφ
  have heq := energyNorm_sq Y d φ
  have hb := mul_le_mul_of_nonneg_left hJ (sq_nonneg floor)
  have hc := mul_le_mul_of_nonneg_left hmass (sq_nonneg C)
  have hsq : (floor*‖J‖)^2 ≤ (C*energyNorm Y d φ)^2 := by nlinarith only [hb,hc,heq]
  have hn := (sq_le_sq₀ (mul_nonneg hf.le (norm_nonneg _)) (mul_nonneg hC (Real.sqrt_nonneg _))).mp hsq
  calc
    ‖J‖ ≤ (C*energyNorm Y d φ)/floor := (le_div_iff₀ hf).mpr (by simpa only [mul_comm,energyNorm] using hn)
    _ = C/floor*energyNorm Y d φ := by ring

end ShrinkingSpheres
