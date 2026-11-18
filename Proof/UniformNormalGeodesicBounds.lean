import Proof.NormalGeodesicTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace ShrinkingSpheres

lemma Background.connection_budget {Ω : Set X} {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ}
    {g g₁ g₂ : MetricField} {e : Frame} (h : Background Ω K M g g₁ g₂ e)
    (hK : 0 < K) (hm : 1 ≤ m) {y : X} (hy : y ∈ Ω) :
    ‖connectionBilinear g y‖ ≤ 243*K*|M ⟨1,by omega⟩| := by
  have hΓ := connectionBilinear_norm_of_entry_bound g y (9*K*|M ⟨1,by omega⟩|) (by positivity)
    (fun k i j => h.1.christoffel_entry_bound hK hy _ (abs_nonneg _)
      (fun a b => (h.reference_fderiv_bound hm hy a b).trans (le_abs_self _)) k i j)
  convert hΓ using 1 <;> ring

/-- An explicit endpoint Taylor constant from exactly the frozen ellipticity and
    first metric jet budget. No frame derivative bound is used. -/
theorem Background.normal_geodesic_quadratic_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {m : ℕ} {M : Fin (m+1) → ℝ} {g g₁ g₂ : MetricField} {e : Frame}
    (h : Background Ω K M g g₁ g₂ e) (hK : 0 < K) (hm : 1 ≤ m)
    {expMap : X × X → X} {R : X → ℝ} (hN : NormalCoordinates Y Ω g expMap R)
    {y : X} (hy : y ∈ Y) (v : X) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖expMap (y,t • v)-y-t • v‖ ≤ 243*K^3*|M ⟨1,by omega⟩| *‖v‖^2*t^2 := by
  have hb := hN.geodesic_quadratic_error_le hΩ h.1 hK
    (show 0 ≤ 243*K*|M ⟨1,by omega⟩| by positivity)
    (fun x hx => h.connection_budget hK hm hx) hy v hv ht
  convert hb using 1 <;> ring

lemma Elliptic.sphere_norm_sq_bound {Ω : Set X} {K : ℝ} {g : MetricField}
    (h : Elliptic Ω K g) (hK : 0 < K) {y : X} (hy : y ∈ Ω) {w : X} (hw : w ∈ sphereAt g y) :
    ‖w‖^2 ≤ K := by
  have hl := ((h.2 y hy).2 w).1
  change metricPair g y w w = 1 at hw
  rw [hw] at hl
  have hh := mul_le_mul_of_nonneg_left hl hK.le
  simpa only [← mul_assoc,mul_inv_cancel₀ hK.ne',one_mul,mul_one] using hh

/-- Uniform quadratic comparison of the actual physical endpoint with its affine
    approximation on every admissible moving sphere. -/
theorem Admissible.endpoint_quadratic_error {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (hm : 1 ≤ m)
    {y : X} (hy : y ∈ Y) (w : X) (hw : w ∈ sphereAt d.γ y) :
    ‖endpoint d.expMap d.radius (y,w)-y-d.radius y • w‖ ≤
      243*K^4*|M ⟨1,by omega⟩| *(d.radius y)^2 := by
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hwd := scaled_unit_mem_disk d.γ y w (d.radius y) hw
  have hv : d.radius y • w ∈ disk d.γ y (max ρ (d.radius y)) :=
    hwd.trans ((sq_le_sq₀ hr.le (hr.le.trans (le_max_right ..))).2 (le_max_right ..))
  have hb := hd.1.normal_geodesic_quadratic_error hΩ hK hm hd.2.1 hy (d.radius y • w) hv
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)
  have hb' : ‖endpoint d.expMap d.radius (y,w)-y-d.radius y • w‖ ≤
      243*K^3*|M ⟨1,by omega⟩| *(d.radius y)^2*‖w‖^2 := by
    simpa only [one_smul,one_pow,mul_one,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_pow,mul_assoc,endpoint] using hb
  have hwBound := hd.1.1.sphere_norm_sq_bound hK (hd.2.1.center_mem hy) hw
  have hh := mul_le_mul_of_nonneg_left hwBound
    (show 0 ≤ 243*K^3*|M ⟨1,by omega⟩| *(d.radius y)^2 by positivity)
  exact hb'.trans (hh.trans_eq (by ring))

end ShrinkingSpheres
