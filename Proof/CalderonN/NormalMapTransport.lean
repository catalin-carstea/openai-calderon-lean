module

public import Proof.CalderonN.NormalGeodesicBounds
import Proof.CalderonN.NormalGeodesicPhase
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Adapted from `NormalMapTransport` in the checked Proposition 5.3 release. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 15
open Set
open scoped ContDiff
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A first-jet bound controls transport of any background map along the actual
    normal geodesic, without a convexity assumption on the coordinate region. -/
theorem NormalCoordinates.map_transport_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {K D : ℝ} {γ : (MetricField dim)}
    (hγ : Elliptic Ω K γ) (hK : 0 < K) (hD : 0 ≤ D)
    (F : (X dim) → E) (hSmooth : ContDiffOn ℝ ∞ F Ω)
    (hDF : ∀ x ∈ Ω,‖fderiv ℝ F x‖ ≤ D)
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω γ expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk γ y (R y)) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖F (expMap (y,t • v))-F y‖ ≤ D*K*‖v‖*t := by
  obtain ⟨U,hU,hI,hReg⟩ := hN.smoothNear_path hy v hv
  let G : ℝ → E := fun s => F (expMap (y,s • v))
  have hGD (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      HasDerivAt G (fderiv ℝ F (expMap (y,s • v))
        (deriv (fun q : ℝ => expMap (y,q • v)) s)) s := by
    have hF := (hSmooth.contDiffAt (hΩ.mem_nhds (hN.path_image hy v hv hs))).differentiableAt (by simp)
    have hPath := (hReg.contDiffAt (hU.mem_nhds (hI hs))).differentiableAt (by simp)
    exact hF.hasFDerivAt.comp_hasDerivAt s hPath.hasDerivAt
  have hBound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : ‖deriv G s‖ ≤ D*K*‖v‖ := by
    rw [(hGD s hs).deriv]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      ((mul_le_mul (hDF _ (hN.path_image hy v hv hs))
        (hN.geodesic_speed_le hΩ hγ hK hy v hv hs) (norm_nonneg _) hD).trans_eq (by ring))
  have hz : (0:ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> norm_num
  have hb := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hGD s hs).differentiableAt) hBound hz ht
  simpa only [G,zero_smul,hN.exp_zero hy,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using hb

end CalderonN
