import Proof.MixedParameterRadialTaylorBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ConnectionError

theorem norm_sub_affine_le_quadratic_of_second_deriv_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ℝ → V) (hg : ContDiff ℝ ∞ g) (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hBound : ∀ t : ℝ,|t| ≤ δ → ‖deriv (deriv g) t‖ ≤ B)
    (r : ℝ) (hr : |r| ≤ δ) : ‖g r-g 0-r • deriv g 0‖ ≤ B*r^2 := by
  let f : ℝ → V := fun t => g t-g 0-t • deriv g 0
  have hf : ContDiff ℝ ∞ f := (hg.sub contDiff_const).sub (contDiff_id.smul contDiff_const)
  have hd (t : ℝ) : HasDerivAt f (deriv g t-deriv g 0) t := by
    change HasDerivAt ((g-(fun _ : ℝ => g 0))-(fun s : ℝ => s • deriv g 0))
      (deriv g t-deriv g 0) t
    simpa only [Function.id_def,sub_zero,one_smul] using
      (((hg.differentiable (by simp) t).hasDerivAt.sub (hasDerivAt_const t (g 0))).sub
        ((hasDerivAt_id t).smul_const (deriv g 0)))
  have hf0 : HasDerivAt f 0 0 := by simpa only [sub_self] using hd 0
  have hDF : deriv f = fun t => deriv g t-deriv g 0 := funext (fun t => (hd t).deriv)
  have hDG : ContDiff ℝ ∞ (deriv g) := by apply ContDiff.deriv';simpa using hg
  have hDD (t : ℝ) (ht : |t| ≤ δ) : ‖deriv (deriv f) t‖ ≤ B := by
    rw [hDF]
    have hh := ((hDG.differentiable (by simp) t).hasDerivAt.sub (hasDerivAt_const t (deriv g 0))).deriv
    simp only [sub_zero] at hh
    change ‖deriv (deriv g-(fun _ => deriv g 0)) t‖ ≤ B
    rw [hh]
    exact hBound t ht
  have hh := norm_sub_le_quadratic_of_second_deriv_le f hf δ B hδ hB hf0 hDD r hr
  simpa only [f,sub_self,zero_smul,sub_zero] using hh

/-- Taylor each parameter jet of the coefficient itself. The affine radial
    model has zero second radial derivative, so only joint order n+2 is
    needed, regardless of the complexity of the first radial model. -/
theorem norm_parameterJetField_sub_affine_of_joint_bound
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : P × ℝ → V) (hF : ContDiff ℝ ∞ F) (p : P) (n : ℕ)
    (δ B : ℝ) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hBound : ∀ t : ℝ,|t| ≤ δ → ‖iteratedFDeriv ℝ (n+2) F (p,t)‖ ≤ B)
    (r : ℝ) (hr : |r| ≤ δ) :
    ‖parameterJetField n F (p,r)-parameterJetField n F (p,0)-
      r • parameterJetField n (radialFirstDerivative F) (p,0)‖ ≤ B*r^2 := by
  let g : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => P) V :=
    fun t => parameterJetField n F (p,t)
  have hg : ContDiff ℝ ∞ g :=
    (contDiff_parameterJetField n F hF).comp (contDiff_const.prodMk contDiff_id)
  have hDD (t : ℝ) (ht : |t| ≤ δ) : ‖deriv (deriv g) t‖ ≤ B := by
    rw [show g = (fun s => parameterJetField n F (p,s)) from rfl,
      deriv_deriv_radialSlice (parameterJetField n F) (contDiff_parameterJetField n F hF) p t]
    exact (norm_radialSecond_parameterJetField_le n F hF (p,t)).trans (hBound t ht)
  have hFirst : deriv g 0 = parameterJetField n (radialFirstDerivative F) (p,0) := by
    rw [show g = (fun s => parameterJetField n F (p,s)) from rfl,
      deriv_radialSlice (parameterJetField n F) (contDiff_parameterJetField n F hF) p 0,
      radialFirstDerivative_parameterJetField n F hF]
  have hh := norm_sub_affine_le_quadratic_of_second_deriv_le g hg δ B hδ hB hDD r hr
  rwa [hFirst] at hh

end ShrinkingSpheres
