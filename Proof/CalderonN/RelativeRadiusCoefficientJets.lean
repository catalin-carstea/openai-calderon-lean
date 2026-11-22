module

public import Proof.CalderonN.NormalizedCoefficientRemainderC2

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- Relative-radius parameter, centered at the actual radius. -/
@[expose] def relativeRadiusCoefficient (d : Data dim) (y : X dim) (t : ℝ) (w : X dim) : Mat dim :=
  firstNormalVelocityCoefficient d y ((d.radius y*(1+t)) • frameVector d.frame y w)

private theorem relativeRadiusCoefficient_deriv_eq (d : Data dim) (y z : X dim)
    (hR : ContDiffAt ℝ ∞ (normalizedFirstCoefficientRemainder d y) z) :
    deriv (fun t => relativeRadiusCoefficient d y t z) 0 =
      (d.radius y*firstDensityCenterLinear d y z) • (1 : Mat dim) +
        fderiv ℝ (normalizedFirstCoefficientRemainder d y) z z := by
  let R := normalizedFirstCoefficientRemainder d y
  let ell := firstDensityCenterLinear d y
  let r := d.radius y
  have hR' : HasFDerivAt R (fderiv ℝ R z) ((1+(0:ℝ)) • z) := by
    simpa only [add_zero,one_smul] using (hR.differentiableAt (by simp)).hasFDerivAt
  have hs : HasDerivAt (fun t : ℝ => (1+t) • z) z 0 := by
    have := (((hasDerivAt_id (0:ℝ)).const_add 1).smul_const z)
    simpa only [id_eq,one_smul] using this
  have hDeriv := hR'.comp_hasDerivAt 0 hs
  let A := r • ell.smulRight (1 : Mat dim)
  have hAffine := A.hasFDerivAt.comp_hasDerivAt 0 hs
  have hEq : (fun t => relativeRadiusCoefficient d y t z) =
      fun t => 1 + A ((1+t) • z) + R ((1+t) • z) := by
    funext t
    have he (s : ℝ) : frameVector d.frame y (s • z) = s • frameVector d.frame y z := by
      rw [← frameVectorLinear_apply,map_smul,frameVectorLinear_apply]
    let c := (r * ell ((1+t) • z)) • (1 : Mat dim)
    have hA : A ((1+t) • z) = c := by
      change r • (ell ((1+t) • z) • (1 : Mat dim)) = c
      rw [smul_smul]
    have hRem : R ((1+t) • z) = relativeRadiusCoefficient d y t z - (1+c) := by
      change firstNormalVelocityCoefficient d y (r • frameVector d.frame y ((1+t) • z)) -
        (1 + r * ell ((1+t) • z)) • (1 : Mat dim) = _
      rw [he,smul_smul,add_smul,one_smul]
      rfl
    rw [hA,hRem,add_sub_cancel]
  rw [hEq]
  have h := (hAffine.const_add (1 : Mat dim)).add hDeriv
  change HasDerivAt (fun t => 1 + A ((1+t) • z) + R ((1+t) • z)) _ 0 at h
  rw [h.deriv]
  simp only [A,smul_apply,ContinuousLinearMap.smulRight_apply,smul_smul,r,ell,R]

/-- The derivative in relative radius of the genuine normalized coefficient
has the same affine first term. Its remainder is quadratic in the actual
radius in both value and first spatial derivative. -/
theorem uniform_relativeRadius_coefficient_jet (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η Q : ℝ, 0 < η ∧ 0 ≤ Q ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      let R := fun z => deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
        (d.radius y*firstDensityCenterLinear d y z) • (1 : Mat dim)
      ∀ z ∈ ball (0 : X dim) 2,
        ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ Q*(d.radius y)^2 ∧
        ‖fderiv ℝ R z‖ ≤ Q*(d.radius y)^2 := by
  obtain ⟨η,Q,hη,hQ,h⟩ := uniform_normalized_coefficient_remainder_C2 (Y := Y) hn hΩ hm
    K ρ c₀ M Cj hK hρ 2 (by norm_num)
  refine ⟨η,3*Q,hη,by positivity,?_⟩
  intro floor hf ε hε hεη d hd y hy
  let U := ball (0 : X dim) 2
  let v := normalizedFirstCoefficientRemainder d y
  let R := fun z => deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
    (d.radius y*firstDensityCenterLinear d y z) • (1 : Mat dim)
  have hJ (z : X dim) (hz : z ∈ U) :=
    h floor hf ε hε hεη d hd y hy z (ball_subset_closedBall hz)
  have hEq (z : X dim) (hz : z ∈ U) : R z = fderiv ℝ v z z := by
    change deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
      (d.radius y*firstDensityCenterLinear d y z) • (1 : Mat dim) = _
    rw [relativeRadiusCoefficient_deriv_eq d y z (hJ z hz).1,add_sub_cancel_left]
  change ∀ z ∈ U, ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ 3*Q*(d.radius y)^2 ∧
    ‖fderiv ℝ R z‖ ≤ 3*Q*(d.radius y)^2
  intro z hz
  have hzN : ‖z‖ ≤ 2 := (mem_ball_zero_iff.mp hz).le
  have hv := ((hJ z hz).1.fderiv_right (m := ∞) (by simp))
  have hC : ContDiffAt ℝ ∞ (fun w => fderiv ℝ v w w) z :=
    hv.clm_apply contDiffAt_id
  have hNear : R =ᶠ[nhds z] fun w => fderiv ℝ v w w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hEq w hw
  refine ⟨hC.congr_of_eventuallyEq hNear,?_,?_⟩
  · rw [hEq z hz]
    refine ((fderiv ℝ v z).le_opNorm z).trans
      ((mul_le_mul (hJ z hz).2.2.1 hzN (norm_nonneg _) (by positivity)).trans ?_)
    nlinarith only [mul_nonneg hQ (sq_nonneg (d.radius y))]
  · rw [hNear.fderiv_eq]
    have hv' : ContDiffAt ℝ ∞ (fderiv ℝ v) z := hv
    have hFD : HasFDerivAt (fun w => fderiv ℝ v w w) _ z :=
      (hv'.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_id z)
    rw [hFD.fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply]
    have h₁ : ‖fderiv ℝ v z u‖ ≤ Q*(d.radius y)^2*‖u‖ :=
      ((fderiv ℝ v z).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hJ z hz).2.2.1 (norm_nonneg _))
    have h₂ : ‖fderiv ℝ (fderiv ℝ v) z u z‖ ≤ Q*(d.radius y)^2*‖u‖*2 :=
      (ContinuousLinearMap.le_opNorm₂ _ _ _).trans (by gcongr; exact (hJ z hz).2.2.2.1)
    exact ((norm_add_le _ _).trans (add_le_add h₁ h₂)).trans_eq (by ring)

end CalderonN
