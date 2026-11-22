module

public import Proof.CalderonN.NormalGeodesicBounds
public import Proof.CalderonN.ConnectionOperatorBounds

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Adapted from the checked Proposition 5.3 release, Proof/NormalGeodesicTaylor.lean. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A coordinate acceleration bound with a uniform connection budget. -/
theorem NormalCoordinates.geodesic_acceleration_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K G : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K) (hG : 0 ≤ G)
    (hΓ : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ G)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (deriv (fun s : ℝ => expMap (y,s • v))) t‖ ≤ G*K^2*‖v‖^2 := by
  let V := deriv (fun s : ℝ => expMap (y,s • v)) t
  have hSpeed : ‖V‖ ≤ K*‖v‖ := hN.geodesic_speed_le hΩ hg hK hy v hv ht
  rw [((hN.2 y hy).2.2 v hv).2.2.2.2 t ht,norm_neg,← connectionBilinear_apply]
  have hOp := hΓ _ (hN.path_image hy v hv ht)
  calc
    _ ≤ ‖connectionBilinear g (expMap (y,t • v))‖*‖V‖*‖V‖ :=
      ((connectionBilinear g (expMap (y,t • v)) V).le_opNorm V).trans
        (mul_le_mul_of_nonneg_right ((connectionBilinear g (expMap (y,t • v))).le_opNorm V) (norm_nonneg V))
    _ ≤ G*(K*‖v‖)*(K*‖v‖) := by gcongr
    _ = _ := by ring

/-- The actual velocity differs from its initial value quadratically in the initial
    coordinate speed, with a constant independent of the configuration. -/
theorem NormalCoordinates.geodesic_velocity_error_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K G : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K) (hG : 0 ≤ G)
    (hΓ : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ G)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖deriv (fun s : ℝ => expMap (y,s • v)) t-v‖ ≤ G*K^2*‖v‖^2*t := by
  obtain ⟨U,hU,hI,hReg⟩ := hN.smoothNear_path hy v hv
  have hVel := hReg.deriv_of_isOpen (m:=∞) hU (by simp)
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le (C:=G*K^2*‖v‖^2)
    (fun s hs => (hVel.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp))
    (fun s hs => hN.geodesic_acceleration_le hΩ hg hK hG hΓ hy v hv hs) hzero ht
  simpa only [((hN.2 y hy).2.2 v hv).2.2.2.1,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb

/-- Uniform quadratic Taylor error of the actual normal-coordinate endpoint. This
    uses the frozen geodesic equation throughout the normal disk, rather than a
    separately chosen model endpoint. -/
theorem NormalCoordinates.geodesic_quadratic_error_le {Y Ω : Set (X dim)} (hΩ : IsOpen Ω)
    {K G : ℝ} {g : (MetricField dim)} (hg : Elliptic Ω K g) (hK : 0 < K) (hG : 0 ≤ G)
    (hΓ : ∀ x ∈ Ω,‖connectionBilinear g x‖ ≤ G)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖expMap (y,t • v)-y-t • v‖ ≤ G*K^2*‖v‖^2*t^2 := by
  obtain ⟨U,hU,hI,hReg⟩ := hN.smoothNear_path hy v hv
  let F : ℝ → (X dim) := fun s => expMap (y,s • v)-s • v
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) 1 := fun s hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hFD (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) :
      HasDerivAt F (deriv (fun q : ℝ => expMap (y,q • v)) s-v) s := by
    have hp := ((hReg.contDiffAt (hU.mem_nhds (hI (hsub hs)))).differentiableAt (by simp)).hasDerivAt
    have hscale : HasDerivAt (fun q : ℝ => q • v) v s := by
      convert (hasDerivAt_id s).smul_const v using 1 <;> simp only [Function.id_def,one_smul]
    exact HasDerivAt.sub hp hscale
  have hC : 0 ≤ G*K^2*‖v‖^2 := by positivity
  have hbound (s : ℝ) (hs : s ∈ Icc (0:ℝ) t) : ‖deriv F s‖ ≤ (G*K^2*‖v‖^2)*t := by
    rw [(hFD s hs).deriv]
    exact (hN.geodesic_velocity_error_le hΩ hg hK hG hΓ hy v hv (hsub hs)).trans
      (mul_le_mul_of_nonneg_left hs.2 hC)
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) t := ⟨le_rfl,ht.1⟩
  have hlast : t ∈ Icc (0:ℝ) t := ⟨ht.1,le_rfl⟩
  have hb := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hFD s hs).differentiableAt) hbound hzero hlast
  have hre : expMap (y,t • v)-y-t • v = F t-F 0 := by
    dsimp [F]
    rw [zero_smul,hN.exp_zero hy]
    abel
  rw [hre]
  convert hb using 1 <;> simp only [sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] <;> ring

end CalderonN
