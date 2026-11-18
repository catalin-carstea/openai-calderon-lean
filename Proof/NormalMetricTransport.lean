import Proof.NormalGeodesicTaylor
import Proof.TauEllipticityBridge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace ShrinkingSpheres

/-- Coordinate metric entries transported along the actual reference geodesic.
    The second metric need not have the same geodesics as the reference metric. -/
theorem NormalCoordinates.metric_entry_transport_bound {Y Ω : Set X} (hΩ : IsOpen Ω)
    {K M : ℝ} {γ g : MetricField} (hγ : Elliptic Ω K γ) (hK : 0 < K) (hM : 0 ≤ M)
    (hSmooth : ∀ i j,ContDiffOn ℝ ∞ (fun x => g x i j) Ω)
    (hD : ∀ x ∈ Ω,∀ i j,‖fderiv ℝ (fun z => g z i j) x‖ ≤ M)
    {expMap : X × X → X} {R : X → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : X} (hy : y ∈ Y)
    (v : X) (hv : v ∈ disk γ y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (i j : I) :
    |g (expMap (y,t • v)) i j-g y i j| ≤ M*K*‖v‖*t := by
  obtain ⟨U,hU,hI,hReg⟩ := hN.smoothNear_path hy v hv
  let F : ℝ → ℝ := fun s => g (expMap (y,s • v)) i j
  have hFD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt F (fderiv ℝ (fun z => g z i j) (expMap (y,s • v))
        (deriv (fun q : ℝ => expMap (y,q • v)) s)) s := by
    have hPos := hN.path_image hy v hv hs
    have hG := ((hSmooth i j).contDiffAt (hΩ.mem_nhds hPos)).differentiableAt (by simp)
    have hPath := (hReg.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp)
    exact hG.hasFDerivAt.comp_hasDerivAt s hPath.hasDerivAt
  have hBound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖deriv F s‖ ≤ M*K*‖v‖ := by
    rw [(hFD s hs).deriv]
    calc
      _ ≤ ‖fderiv ℝ (fun z => g z i j) (expMap (y,s • v))‖*
          ‖deriv (fun q : ℝ => expMap (y,q • v)) s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M*(K*‖v‖) := mul_le_mul (hD _ (hN.path_image hy v hv hs) i j)
        (hN.geodesic_speed_le hΩ hγ hK hy v hv hs) (norm_nonneg _) hM
      _ = _ := by ring
  have hzero : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hFD s hs).differentiableAt) hBound hzero ht
  simpa only [F,zero_smul,hN.exp_zero hy,Real.norm_eq_abs,sub_zero,abs_of_nonneg ht.1] using hb

end ShrinkingSpheres
