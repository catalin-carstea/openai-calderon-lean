module

public import Proof.CalderonN.GaussRadialTraceAdjoint
public import Proof.CalderonN.AdmittedMovingTraceAdjoint

import Mathlib.Tactic

/-! The physical moving-trace adjoint is exactly the flat-sphere
rotation term plus the weighted radial response with Gauss datum. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace
namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_admitted_normalizedBallMetric_smooth
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ) :
    ∃ U : Set (X dim), IsOpen U ∧ closedBall (0 : X dim) 1 ⊆ U ∧
      SmoothMetric U (normalizedBallMetric d.g₁ d.expMap d.frame y (d.radius y)) := by
  have h0 : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) (0 : X dim → ℝ) := by
    refine ⟨⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩,fun x _ => ?_⟩
    have hZero (k : I dim) : coordDeriv k (0 : X dim → ℝ) = 0 := by
      funext z
      simp [coordDeriv]
    simp [laplace,hZero,coordDeriv]
  obtain ⟨U,hU,hC,hg,_,_⟩ := harmonicOnBall_admitted_normalChart hΩ hd hK hy hrρ h0
  exact ⟨U,hU,hC,hg⟩

theorem admitted_gauss_radial_trace_adjoint
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ}
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : 2*d.radius y < ρ)
    (i : I dim) {v : Field dim} (hv : smoothNear v (bundle Y d.γ)) :
    let r := d.radius y
    let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
    let V (z : X dim) := scaledNormalTraceVelocity d.γ d.expMap d.frame y r
      (fderiv ℝ d.radius y (axis i)) z (axis i)
    let W := firstNormalRadialWeight d y r
    let ψ (z : X dim) := v (y,frameVector d.frame y z)
    ∃ bR bI : X dim → ℝ,
      FixedBallSolution g (fun z => (ψ z).re*⟪z,V z⟫_ℝ/W z) bR ∧
      FixedBallSolution g (fun z => (ψ z).im*⟪z,V z⟫_ℝ/W z) bI ∧
      ∀ z ∈ standardSphere dim,
        (r : ℂ)*adjointField d.adjoint i v (y,frameVector d.frame y z) =
          ⟨W z*fderiv ℝ bR z z -
            ∑ j,∑ k,sphereRotationDerivative j k (fun x => (ψ x).re*(x j*V x k)) z,
           W z*fderiv ℝ bI z z -
            ∑ j,∑ k,sphereRotationDerivative j k (fun x => (ψ x).im*(x j*V x k)) z⟩ := by
  dsimp only
  let r := d.radius y
  let g := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let V (z : X dim) := scaledNormalTraceVelocity d.γ d.expMap d.frame y r
    (fderiv ℝ d.radius y (axis i)) z (axis i)
  let W := firstNormalRadialWeight d y r
  let c := firstMetricDensityFactor d.γ d.g₁ y
  let ζ (z : X dim) := (y,frameVector d.frame y z)
  let ψ := v ∘ ζ
  have hc : 0 < c := firstMetricDensityFactor_pos _ _ _
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hr' : r < ρ := by dsimp [r] at *; linarith only [hr,hrρ]
  have hW : EqOn (ballConormalVector g) (fun z => (c*W z) • z) (standardSphere dim) :=
    fun _ hz => admitted_normalBallConormalVector_eq hn hΩ hd hK hy hr' hz
  obtain ⟨U,hU,hCU,hg⟩ := exists_admitted_normalizedBallMetric_smooth hΩ hd hK hy hrρ
  obtain ⟨U',hU',hCU',hV,_⟩ := exists_admitted_scaledVelocity_smooth hd hy hrρ (axis i)
    (fderiv ℝ d.radius y (axis i))
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hζ : ContDiff ℝ ∞ ζ := by
    simp only [ζ,← frameVectorLinear_apply]
    exact contDiff_const.prodMk (frameVectorLinear d.frame y).contDiff
  have hv₀ := hv
  obtain ⟨Z,hZ,hBZ,hvZ⟩ := hv
  let S := ((U ∩ U') ∩ (ζ ⁻¹' Z)) ∩ ({0}ᶜ : Set (X dim))
  have hS : IsOpen S := ((hU.inter hU').inter (hZ.preimage hζ.continuous)).inter
    isClosed_singleton.isOpen_compl
  have hSU : S ⊆ U := fun _ h => h.1.1.1
  have hSS : standardSphere dim ⊆ S := by
    intro z hz
    have hB := sphere_subset_closedBall hz
    refine ⟨⟨⟨hCU hB,hCU' hB⟩,hBZ ⟨hy,frameVector_mem_sphere d.γ d.frame y he ⟨z,hz⟩⟩⟩,?_⟩
    intro h
    change z = 0 at h
    simpa [standardSphere,h] using hz
  have hS₀ : (0 : X dim) ∉ S := fun h => h.2 rfl
  have hψ : ContDiffOn ℝ ∞ ψ S := hvZ.comp hζ.contDiffOn (fun _ h => h.1.2)
  have hVS : ContDiffOn ℝ ∞ V S := hV.mono fun _ h => h.1.1.2
  have hKappa : ContDiffOn ℝ ∞ (fun z : X dim => ⟪z,ballConormalVector g z⟫_ℝ) S :=
    contDiffOn_id.inner ℝ ((contDiffOn_ballConormalVector hg).mono hSU)
  have hKappa₀ (z : X dim) (hz : z ∈ S) : 0 < ⟪z,ballConormalVector g z⟫_ℝ :=
    ballConormalVector_inner_pos (hg.2 z (hSU hz)) (fun h => hS₀ (h ▸ hz))
  have hSol {f : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
      ∃ b, FixedBallSolution g (fun z => f z*⟪z,V z⟫_ℝ/W z) b := by
    let F (z : X dim) := c*(f z*⟪z,V z⟫_ℝ/⟪z,ballConormalVector g z⟫_ℝ)
    have hF : ContDiffOn ℝ ∞ F S := contDiffOn_const.mul
      ((hf.mul (contDiffOn_id.inner ℝ hVS)).div hKappa fun z hz => (hKappa₀ z hz).ne')
    have hE : EqOn F (fun z => f z*⟪z,V z⟫_ℝ/W z) (standardSphere dim) := by
      intro z hz
      have hn := mem_sphere_zero_iff_norm.mp hz
      have hI : ⟪z,z⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,hn,one_pow]
      change c*(f z*⟪z,V z⟫_ℝ/⟪z,ballConormalVector g z⟫_ℝ) = _
      rw [hW hz,real_inner_smul_right,hI,mul_one]
      simp only [div_eq_mul_inv,mul_inv]
      have hcancel := mul_inv_cancel₀ hc.ne'
      calc
        _ = (c*c⁻¹)*(f z*⟪z,V z⟫_ℝ*(W z)⁻¹) := by ring
        _ = _ := by rw [hcancel,one_mul]
    let b := fixedBallPoisson g F
    have hb : FixedBallSolution g F b := fixedBallPoisson_solution hU hCU hg ⟨S,hS,hSS,hF⟩
    exact ⟨b,hb.1,hb.2.1.trans hE,hb.2.2⟩
  have hR : ContDiffOn ℝ ∞ (fun z => (ψ z).re) S := Complex.reCLM.contDiff.comp_contDiffOn hψ
  have hI : ContDiffOn ℝ ∞ (fun z => (ψ z).im) S := Complex.imCLM.contDiff.comp_contDiffOn hψ
  obtain ⟨bR,hbR⟩ := hSol hR
  obtain ⟨bI,hbI⟩ := hSol hI
  refine ⟨bR,bI,hbR,hbI,fun z hz => ?_⟩
  rw [← framedScaledMovingAdjoint_eq_actual hY hΩ hd hK hy hrρ i hv₀ ⟨z,hz⟩]
  apply Complex.ext
  · exact parametricBallVelocityAdjoint_gauss_radial_response (0:ℝ) hU hS hCU hSS hSU hS₀
      (g := fun p => g p.2) (V := fun p => V p.2) (ψ := fun p => (ψ p.2).re)
      hg hVS hR c hc.ne' W (fun _ hw => hW hw) hbR hz
  · exact parametricBallVelocityAdjoint_gauss_radial_response (0:ℝ) hU hS hCU hSS hSU hS₀
      (g := fun p => g p.2) (V := fun p => V p.2) (ψ := fun p => (ψ p.2).im)
      hg hVS hI c hc.ne' W (fun _ hw => hW hw) hbI hz

end CalderonN
