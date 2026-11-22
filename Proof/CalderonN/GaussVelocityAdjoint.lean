module

public import Proof.CalderonN.AdmittedNormalBallPullback
public import Proof.CalderonN.BallBoundaryAdjoint

import Proof.CalderonN.FlatAngularAdjoint
import Proof.CalderonN.NormalMapDerivativeTaylor
import Mathlib.Tactic

/-! Gauss' lemma turns the metric conormal into a positive scalar times
the Euclidean radial derivative. The radial part cancels from the
rotational integration-by-parts term. -/

public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise InnerProductSpace
namespace CalderonN

open OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem admitted_normalBallConormalVector_eq
    (hn : 2 ≤ dim) {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X dim} (hy : y ∈ Y) (hrρ : d.radius y < ρ) {z : X dim} (hz : z ∈ standardSphere dim) :
    ballConormalVector (normalizedBallMetric d.g₁ d.expMap d.frame y (d.radius y)) z =
      (firstMetricDensityFactor d.γ d.g₁ y * firstNormalRadialWeight d y (d.radius y) z) • z := by
  let r := d.radius y
  let m := normalizedBallMetric d.g₁ d.expMap d.frame y r
  let v := r • frameVector d.frame y z
  let D := (normalVerticalJacobian d.expMap y v).comp (frameVectorLinear d.frame y)
  let c := firstMetricDensityFactor d.γ d.g₁ y
  have hr := (hd.2.2.2.2.1.2 y hy).1
  have he := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hVel : v ∈ interior (disk d.γ y (max ρ r)) := by
    apply mem_interior_disk_of_metricPair_lt
    change metricPair d.γ y (r • frameVector d.frame y z) (r • frameVector d.frame y z) < _
    have hz₁ : ‖z‖ = 1 := by simpa only [standardSphere,mem_sphere,dist_zero_right] using hz
    rw [metricPair_scaled_frameVector d.γ d.frame y he,hz₁,one_pow,mul_one]
    exact (sq_lt_sq₀ hr.le (hr.le.trans (le_max_right _ _))).2 (hrρ.trans_le (le_max_left _ _))
  have hL : frameVectorL (d.frame y) = frameVectorLinear d.frame y := by
    ext1 w
    rw [frameVectorL_apply_frame,frameVectorLinear_apply]
  have hD : normalizedBallDerivative d.expMap d.frame y r z = D := by
    unfold normalizedBallDerivative
    rw [hL]
    have h := (hd.2.1.hasFDerivAt_velocity_slice hy v (interior_subset hVel)).fderiv
    change fderiv ℝ (fun v => d.expMap (y,v)) (r • frameVector d.frame y z) = _ at h
    rw [h]
  have hm : m z = pullbackMetricMatrix (d.g₁ (d.expMap (y,v)),D) := by
    unfold m normalizedBallMetric pullbackMetricMatrix normalBallChartMap
    rw [hD]
  have hS (i j : I dim) : divergenceCoeff m z i j = c*firstNormalVelocityCoefficient d y v i j := by
    change divergenceCoeff m z i j = c*((c⁻¹ • pullbackDivergenceMatrix (d.g₁ (d.expMap (y,v)),D)) i j)
    rw [pullbackDivergenceMatrix,← hm,Matrix.smul_apply,smul_eq_mul,← mul_assoc,
      mul_inv_cancel₀ (firstMetricDensityFactor_pos _ _ _).ne',one_mul]
    rfl
  ext j
  change (∑ i, z i * divergenceCoeff m z i j) =
    (c*firstNormalRadialWeight d y r z) * z j
  simp_rw [hS,show ∀ i : I dim, z i * (c*firstNormalVelocityCoefficient d y v i j) =
      c*(z i*firstNormalVelocityCoefficient d y v i j) from fun i => by ring,← Finset.mul_sum]
  rw [hd.actualNormalCoeff_radial_row hn hΩ hK hy hr.ne' z hVel j]
  ring

private theorem sum_rotation_of_symmetric_zero (F : I dim → I dim → X dim → ℝ)
    (h : ∀ i j, F i j = F j i) (z : X dim) :
    ∑ i,∑ j,sphereRotationDerivative i j (F i j) z = 0 := by
  let S := ∑ i,∑ j,sphereRotationDerivative i j (F i j) z
  have hNeg : S = -S := by
    conv_lhs => rw [show S = ∑ i,∑ j,sphereRotationDerivative i j (F i j) z from rfl,Finset.sum_comm]
    rw [show -S = ∑ i,∑ j,-sphereRotationDerivative i j (F i j) z from by
      dsimp only [S]; simp only [Finset.sum_neg_distrib]]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [h j i,sphereRotationDerivative,sphereRotationDerivative]
    have hR : rotationVector j i z = -rotationVector i j z := by
      unfold rotationVector
      exact (neg_sub _ _).symm
    rw [hR,map_neg]
  linarith only [hNeg]

theorem ballVelocityAdjoint_gauss_formula
    {U : Set (X dim)} (hU : IsOpen U) (hSU : standardSphere dim ⊆ U)
    (hU₀ : (0 : X dim) ∉ U) {g : MetricField dim} (hg : SmoothMetric U g)
    {V : X dim → X dim} (hV : ContDiffOn ℝ ∞ V U)
    {ψ : X dim → ℝ} (hψ : ContDiffOn ℝ ∞ ψ U)
    (κ : X dim → ℝ)
    (hκ : EqOn (ballConormalVector g) (fun z => κ z • z) (standardSphere dim))
    (b : X dim → ℝ) {z : X dim} (hz : z ∈ standardSphere dim) :
    ballVelocityAdjoint g V ψ b z =
      κ z*fderiv ℝ b z z -
        ∑ i,∑ j,sphereRotationDerivative i j (fun x => ψ x*(x i*V x j)) z := by
  let c (x : X dim) := ⟪x,V x⟫_ℝ
  have hc : ContDiffOn ℝ ∞ c U := contDiffOn_id.inner ℝ hV
  have hCone : ContDiffOn ℝ ∞ (ballConormalVector g) U := contDiffOn_ballConormalVector hg
  have hComponent : ContDiffOn ℝ ∞ (fun z => conormalComponent g z (V z)) U :=
    hc.div (contDiffOn_id.inner ℝ hCone)
      (fun z hz => (ballConormalVector_inner_pos (hg.2 z hz) (fun h => hU₀ (h ▸ hz))).ne')
  have hTang : ContDiffOn ℝ ∞ (fun z => tangentialComponent g z (V z)) U :=
    hV.sub (hComponent.smul hCone)
  have ht (z : X dim) (hz : z ∈ standardSphere dim) :
      tangentialComponent g z (V z) = V z-c z • z := by
    have hz₁ := mem_sphere_zero_iff_norm.mp hz
    have hInner : ⟪z,z⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq,hz₁,one_pow]
    have hκ₀ : κ z ≠ 0 := by
      have h := ballConormalVector_inner_pos (hg.2 z (hSU hz))
        (fun h => hU₀ (h ▸ hSU hz))
      rw [hκ hz,real_inner_smul_right,hInner,mul_one] at h
      exact h.ne'
    rw [tangentialComponent,conormalComponent,hκ hz,real_inner_smul_right,hInner,mul_one,
      smul_smul,div_mul_cancel₀ _ hκ₀]
  have hRot (i j : I dim) :
      sphereRotationDerivative i j (fun x => ψ x*(x i*tangentialComponent g x (V x) j)) z =
        sphereRotationDerivative i j (fun x => ψ x*(x i*V x j)) z -
          sphereRotationDerivative i j (fun x => ψ x*c x*(x i*x j)) z := by
    have proj (k : I dim) : ContDiffOn ℝ ∞ (fun x : X dim => x k) U :=
      (EuclideanSpace.proj (𝕜:=ℝ) k).contDiff.contDiffOn
    have hOne : ContDiffOn ℝ ∞ (fun x => ψ x*(x i*tangentialComponent g x (V x) j)) U :=
      hψ.mul ((proj i).mul ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp_contDiffOn hTang))
    have hTwo₁ : ContDiffOn ℝ ∞ (fun x => ψ x*(x i*V x j)) U :=
      hψ.mul ((proj i).mul ((EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.comp_contDiffOn hV))
    have hTwo₂ := (hψ.mul hc).mul ((proj i).mul (proj j))
    have hTwo := hTwo₁.sub hTwo₂
    have hE : EqOn (fun x => ψ x*(x i*tangentialComponent g x (V x) j))
        (fun x => ψ x*(x i*V x j)-ψ x*c x*(x i*x j)) (standardSphere dim) := by
      intro w hw
      change ψ w*(w i*tangentialComponent g w (V w) j) = _
      rw [ht w hw]
      simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
      ring
    rw [sphereRotationDerivative_congr_of_eqOn_sphere hz
      ((hOne.contDiffAt (hU.mem_nhds (hSU hz))).differentiableAt (by simp))
      ((hTwo.contDiffAt (hU.mem_nhds (hSU hz))).differentiableAt (by simp)) hE i j]
    have hSub := fderiv_fun_sub ((hTwo₁.contDiffAt (hU.mem_nhds (hSU hz))).differentiableAt (by simp))
      ((hTwo₂.contDiffAt (hU.mem_nhds (hSU hz))).differentiableAt (by simp))
    unfold sphereRotationDerivative
    change fderiv ℝ (fun x => ψ x*(x i*V x j)-ψ x*c x*(x i*x j)) z (rotationVector i j z) = _
    rw [hSub,sub_apply]
  rw [ballVelocityAdjoint,ballConormal_eq_fderiv_conormalVector,hκ hz,map_smul,smul_eq_mul]
  simp_rw [hRot,Finset.sum_sub_distrib,
    sum_rotation_of_symmetric_zero (fun i j x => ψ x*c x*(x i*x j))
      (fun i j => funext fun x => by rw [mul_comm (x i) (x j)]) z,sub_zero]

end CalderonN
