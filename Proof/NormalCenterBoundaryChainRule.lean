import Proof.UniformNormalCenterVelocity
import Proof.MovingRadius

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
namespace ShrinkingSpheres

lemma fderiv_ballPullback_apply (expMap : X × X → X) (r u : X → ℝ) (y w a : X)
    (he : DifferentiableAt ℝ expMap (y,r y • w))
    (hu : DifferentiableAt ℝ u (endpoint expMap r (y,w))) :
    fderiv ℝ (ballPullback expMap r y u) w a =
      fderiv ℝ u (endpoint expMap r (y,w)) (normalVerticalJacobian expMap y (r y • w) (r y • a)) := by
  have hScale := (hasFDerivAt_const (𝕜:=ℝ) y w).prodMk ((hasFDerivAt_id (𝕜:=ℝ) w).const_smul (r y))
  have hd := hu.hasFDerivAt.comp w (he.hasFDerivAt.comp w hScale)
  have hh := congrArg (fun L : X →L[ℝ] ℝ => L a) hd.fderiv
  exact hh

lemma horizontal_fixed_normal_endpoint (g : MetricField) (expMap : X × X → X)
    (r u : X → ℝ) (y w a : X)
    (he : DifferentiableAt ℝ expMap (y,r y • w))
    (hu : DifferentiableAt ℝ u (endpoint expMap r (y,w))) :
    horizontal g (fun p => u (endpoint expMap (fun _ => r y) p)) y w a =
      fderiv ℝ u (endpoint expMap r (y,w)) (normalParallelCenterJacobian g expMap y (r y • w) a) := by
  rw [horizontal_endpoint g expMap (fun _ => r y) u y w a (differentiableAt_const _) he hu]
  rw [normalParallelCenterJacobian_apply]
  have hGamma : connection g y a (r y • w) = r y • connection g y a w := by
    rw [← connectionBilinear_apply,← connectionBilinear_apply,map_smul]
  have hConst : fderiv ℝ (fun _ : X => r y) y = (0 : X →L[ℝ] ℝ) :=
    (hasFDerivAt_const (𝕜:=ℝ) (r y) y).fderiv
  rw [hConst]
  simp only [ContinuousLinearMap.zero_apply,zero_smul,add_zero,hGamma,smul_neg]
  rfl

/-- The actual moving trace chain rule separates the ambient Euclidean action,
    logarithmic-radius radial derivative and the quadratic Jacobi coefficient.
    All three terms act on the same physical harmonic pullback. -/
theorem Admissible.horizontal_normal_pullback_decomposition {Y Ω : Set X} (hY : IsOpen Y)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) {y w : X} (hy : y ∈ Y)
    (hw : w ∈ sphereAt d.γ y) (a : X) (u : X → ℝ)
    (hu : HarmonicOnBall d.g₁ (closedBallImage d.γ d.expMap d.radius y) u) :
    horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y w a =
      (d.radius y)⁻¹*fderiv ℝ (ballPullback d.expMap d.radius y u) w a+
      fderiv ℝ (fun x => Real.log (d.radius x)) y a*radialTrace d.expMap d.radius y w u+
      (d.radius y)⁻¹*fderiv ℝ (ballPullback d.expMap d.radius y u) w
        ((normalizedParallelCenterJacobian d.γ d.expMap y (d.radius y • w)-ContinuousLinearMap.id ℝ X) a) := by
  obtain ⟨hr,he,huDiff⟩ := dirichlet_differentiability Y Ω hY hd y w hy hw u hu
  have hrPos := (hd.2.2.2.2.1.2 y hy).1
  have hUnit : metricPair d.γ y w w = 1 := hw
  have hwDisk : w ∈ disk d.γ y 1 := by
    change metricPair d.γ y w w ≤ 1^2
    change metricPair d.γ y w w = 1 at hw
    rw [hw];norm_num
  have hvDisk : d.radius y • w ∈ disk d.γ y (max ρ (d.radius y)) := by
    change metricPair d.γ y (d.radius y • w) (d.radius y • w) ≤ (max ρ (d.radius y))^2
    rw [metricPair_smul_left,metricPair_smul_right,hUnit]
    have hSqR : (d.radius y)^2 ≤ (max ρ (d.radius y))^2 :=
      (sq_le_sq₀ hrPos.le (hrPos.le.trans (le_max_right _ _))).2 (le_max_right _ _)
    nlinarith only [hSqR]
  let J := normalVerticalJacobian d.expMap y (d.radius y • w)
  let C := normalParallelCenterJacobian d.γ d.expMap y (d.radius y • w)
  let N := normalizedParallelCenterJacobian d.γ d.expMap y (d.radius y • w)
  let F := fderiv ℝ (ballPullback d.expMap d.radius y u) w
  have hInv := hd.2.1.normalVerticalJacobian_isInvertible hy (d.radius y • w) hvDisk
  have hRescaled : F ((d.radius y)⁻¹ • N a) =
      fderiv ℝ u (endpoint d.expMap d.radius (y,w)) (C a) := by
    rw [fderiv_ballPullback_apply d.expMap d.radius u y w _ he huDiff]
    have hVec : J (d.radius y • ((d.radius y)⁻¹ • N a)) = C a := by
      rw [smul_smul,mul_inv_cancel₀ hrPos.ne',one_smul]
      exact hInv.self_apply_inverse (C a)
    exact congrArg (fderiv ℝ u (endpoint d.expMap d.radius (y,w))) hVec
  have hFixed := horizontal_fixed_normal_endpoint d.γ d.expMap d.radius u y w a he huDiff
  have hSplit := horizontal_endpoint_split d.γ d.expMap d.radius u y w a hr hrPos.ne' he huDiff
  rw [hFixed,← hRescaled] at hSplit
  have hN : N a = a+(N-ContinuousLinearMap.id ℝ X) a := by
    change N a = a+(N a-a);abel
  rw [map_smul,hN,map_add] at hSplit
  change horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y w a = _ at hSplit
  change horizontal d.γ (fun p => u (endpoint d.expMap d.radius p)) y w a =
    (d.radius y)⁻¹*F a+_+(d.radius y)⁻¹*F ((N-ContinuousLinearMap.id ℝ X) a)
  rw [hSplit]
  simp only [smul_eq_mul]
  ring

/-- The quadratic center error becomes an O(radius) coefficient after rescaling
    the actual first-order boundary action. -/
theorem uniform_rescaled_normal_center_error {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η CG : ℝ,0 < η ∧ 0 ≤ CG ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,∀ w ∈ disk d.γ y 1,
      ‖(d.radius y)⁻¹ • (normalizedParallelCenterJacobian d.γ d.expMap y (d.radius y • w)-
        ContinuousLinearMap.id ℝ X)‖ ≤ CG*d.radius y := by
  obtain ⟨η,CG,hη,hCG,hControl⟩ := uniform_normal_parallel_center_velocity
    (Y:=Y) hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,CG,hη,hCG,?_⟩
  intro floor hf ε hε hSmall d hd y hy w hw
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have hb := hControl floor hf ε hε hSmall d hd y hy w hw
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  calc
    _ ≤ (d.radius y)⁻¹*(CG*(d.radius y)^2) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hr.le)
    _ = _ := by field_simp

end ShrinkingSpheres
