module

public import Proof.CalderonN.NormalEndpointJets
import Mathlib.Analysis.Calculus.Deriv.Mul

import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped ContDiff Topology
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

lemma second_deriv_linear_ray {F : (X dim) × (X dim) → (X dim)} {U : Set ((X dim) × (X dim))} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (y v : (X dim)) (hy : (y,(0:(X dim))) ∈ U) :
    deriv (deriv (fun t : ℝ => F (y,t • v))) 0 =
      fderiv ℝ (fderiv ℝ F) (y,0) (0,v) (0,v) := by
  have hcurve (t : ℝ) : HasDerivAt (fun s : ℝ => (y,s • v)) ((0:(X dim)),v) t := by
    convert (hasDerivAt_const t y).prodMk ((hasDerivAt_id t).smul_const v) using 1 <;>
      simp only [Function.id_def,one_smul]
  have hc : Continuous (fun t : ℝ => (y,t • v)) := continuous_const.prodMk (continuous_id.smul continuous_const)
  have hnear : ∀ᶠ t in 𝓝 (0:ℝ),(y,t • v) ∈ U := by
    have hy' : (fun t : ℝ => (y,t • v)) 0 ∈ U := by simpa only [zero_smul] using hy
    exact hc.continuousAt.eventually (hU.mem_nhds hy')
  have heq : deriv (fun t : ℝ => F (y,t • v)) =ᶠ[𝓝 (0:ℝ)]
      (fun t : ℝ => fderiv ℝ F (y,t • v) (0,v)) := by
    filter_upwards [hnear] with t ht
    have hd := ((hF.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)).hasFDerivAt
    simpa only [Function.comp_def] using (hd.comp_hasDerivAt t (hcurve t)).deriv
  have hD := ((hF.fderiv_of_isOpen (m:=∞) hU (by simp)).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have hD' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (y,0)) (y,(0:ℝ) • v) := by
    simpa only [zero_smul] using hD.hasFDerivAt
  have hdd := (hD'.comp_hasDerivAt 0 (hcurve 0)).clm_apply (hasDerivAt_const (0:ℝ) ((0:(X dim)),v))
  have hval : deriv (fun t : ℝ => fderiv ℝ F (y,t • v) (0,v)) 0 =
      fderiv ℝ (fderiv ℝ F) (y,0) (0,v) (0,v) := by
    simpa only [Function.comp_def,zero_smul,map_zero,add_zero] using hdd.deriv
  exact heq.deriv_eq.trans hval

/-- The diagonal vertical second jet is forced by the actual geodesic equation. -/
theorem NormalCoordinates.second_vertical_diagonal_on_disk {Y Ω : Set (X dim)} {g : (MetricField dim)}
    {expMap : (X dim) × (X dim) → (X dim)} {R : (X dim) → ℝ}
    (hN : NormalCoordinates Y Ω g expMap R) {y : (X dim)} (hy : y ∈ Y)
    (v : (X dim)) (hv : v ∈ disk g y (R y)) :
    fderiv ℝ (fderiv ℝ expMap) (y,0) (0,v) (0,v) = -connection g y v v := by
  obtain ⟨U,hU,hTube,hReg⟩ := hN.1
  have hRay := second_deriv_linear_ray hU hReg y v (hTube ⟨hy,zero_mem_disk g y (R y)⟩)
  have hGeo := (hN.2 y hy).2.2 v hv
  have hODE := hGeo.2.2.2.2 0 (by constructor <;> norm_num)
  rw [hGeo.2.2.1,hGeo.2.2.2.1] at hODE
  exact hRay.symm.trans hODE

end CalderonN
