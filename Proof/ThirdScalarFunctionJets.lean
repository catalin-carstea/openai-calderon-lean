import Proof.ScalarInverseSecondJet
import Proof.ExpJetBounds
import Proof.ThirdDerivativeProductBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

/-- A third logarithmic jet bound from actual denominator and scalar jets. -/
theorem norm_third_fderiv_log_le {Ω : Set X} (hΩ : IsOpen Ω) (f : X → ℝ)
    (hf : ContDiffOn ℝ ∞ f Ω) (hpos : ∀ y ∈ Ω,0 < f y) {x : X} (hx : x ∈ Ω)
    (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (_hM3 : 0 ≤ M3)
    (hD : ‖fderiv ℝ f x‖ ≤ M1) (hDD : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M2)
    (hDDD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ M3) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => Real.log (f y)))) x‖ ≤
      (f x)⁻¹*M3+3*(f x)⁻¹^2*M1*M2+2*(f x)⁻¹^3*M1^3 := by
  have hInvNonneg : 0 ≤ (f x)⁻¹ := (inv_pos.mpr (hpos x hx)).le
  have hfx := hf.contDiffAt (hΩ.mem_nhds hx)
  have hInv : ContDiffOn ℝ ∞ (fun y => (f y)⁻¹) Ω := hf.inv (fun y hy => (hpos y hy).ne')
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) Ω := hf.fderiv_of_isOpen (m:=∞) hΩ (by simp)
  have hEq : fderiv ℝ (fun y => Real.log (f y)) =ᶠ[𝓝 x] (fun y => (f y)⁻¹ • fderiv ℝ f y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact ((hf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.log (hpos y hy).ne' |>.fderiv
  rw [hEq.fderiv.fderiv_eq]
  have hI1 := norm_fderiv_scalar_inverse_le f x (hfx.differentiableAt (by simp)) (hpos x hx) M1 hD
  have hI2 := norm_second_fderiv_scalar_inverse_le f x hfx (hpos x hx) M1 M2 hM1 hM2 hD hDD
  have hb := norm_second_fderiv_smul_at hΩ hInv hDf hx
  rw [abs_of_pos (inv_pos.mpr (hpos x hx))] at hb
  exact hb.trans ((show (f x)⁻¹*‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖+
    2*‖fderiv ℝ (fun y => (f y)⁻¹) x‖*‖fderiv ℝ (fderiv ℝ f) x‖+
    ‖fderiv ℝ (fderiv ℝ (fun y => (f y)⁻¹)) x‖*‖fderiv ℝ f x‖ ≤
    (f x)⁻¹*M3+2*((f x)⁻¹^2*M1)*M2+((f x)⁻¹^2*M2+2*(f x)⁻¹^3*M1^2)*M1 by
      gcongr).trans_eq (by ring))

/-- The third exponential jet uses the same first-derivative product identity
    and the already checked first/second exponential bounds. -/
theorem norm_third_fderiv_exp_comp_le {Ω : Set X} (hΩ : IsOpen Ω) (f : X → ℝ)
    (hf : ContDiffOn ℝ ∞ f Ω) {x : X} (hx : x ∈ Ω)
    (M1 M2 M3 : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (_hM3 : 0 ≤ M3)
    (hD : ‖fderiv ℝ f x‖ ≤ M1) (hDD : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M2)
    (hDDD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ ≤ M3) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => Real.exp (f y)))) x‖ ≤
      Real.exp (f x)*(M3+3*M1*M2+M1^3) := by
  have hfx := hf.contDiffAt (hΩ.mem_nhds hx)
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ f) Ω := hf.fderiv_of_isOpen (m:=∞) hΩ (by simp)
  have hEq : fderiv ℝ (fun y => Real.exp (f y)) =ᶠ[𝓝 x] (fun y => Real.exp (f y) • fderiv ℝ f y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact ((hf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt.exp |>.fderiv
  rw [hEq.fderiv.fderiv_eq]
  have hE1 := norm_fderiv_exp_comp_le f x (hfx.differentiableAt (by simp)) M1 hD
  have hE2 := norm_second_fderiv_exp_comp_le f x hfx M1 M2 hM1 hM2 hD hDD
  have hb := norm_second_fderiv_smul_at hΩ hf.exp hDf hx
  rw [abs_of_pos (Real.exp_pos _)] at hb
  exact hb.trans ((show Real.exp (f x)*‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖+
    2*‖fderiv ℝ (fun y => Real.exp (f y)) x‖*‖fderiv ℝ (fderiv ℝ f) x‖+
    ‖fderiv ℝ (fderiv ℝ (fun y => Real.exp (f y))) x‖*‖fderiv ℝ f x‖ ≤
    Real.exp (f x)*M3+2*(Real.exp (f x)*M1)*M2+(Real.exp (f x)*(M2+M1^2))*M1 by
      gcongr).trans_eq (by ring))

end ShrinkingSpheres
