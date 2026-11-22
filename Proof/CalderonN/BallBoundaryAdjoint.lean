module

public import Proof.CalderonN.ConormalDecomposition
public import Proof.CalderonN.NormalFluxDensity

import Proof.CalderonN.EllipticCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Adapted from `BallBoundaryAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Filter Set Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

open OAI.AnisotropicCalderon.SmoothSphereRotation

private theorem exists_global_extension_on_sphere {S : Set (X dim)}
    (hS : IsOpen S) (hSS : (standardSphere dim) ⊆ S)
    {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
    ∃ f₀ : (X dim) → ℝ, ContDiff ℝ ∞ f₀ ∧ ∀ w ∈ (standardSphere dim), f₀ =ᶠ[𝓝 w] f := by
  obtain ⟨χ,hχ,_,hχS,hχW⟩ := Elliptic.exists_plateau_cutoff hS
    (isCompact_sphere (0 : (X dim)) 1) hSS
  let f₀ := fun w => χ w * f w
  refine ⟨f₀,contDiff_iff_contDiffAt.mpr (fun x => ?_),?_⟩
  · by_cases hx : x ∈ S
    · exact hχ.contDiffAt.mul (hf.contDiffAt (hS.mem_nhds hx))
    · have hxn : x ∈ (tsupport χ)ᶜ := fun h => hx (hχS h)
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hxn] with z hz
      simp only [f₀,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  · intro w hw
    exact (hχW w hw).mono (fun _ h => by simp [f₀,h])

private theorem sphere_rotationSkew_of_smoothNear
    {S U : Set (X dim)} (hS : IsOpen S) (hU : IsOpen U)
    (hSS : (standardSphere dim) ⊆ S) (hSU : (standardSphere dim) ⊆ U)
    {f u : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hu : ContDiffOn ℝ ∞ u U) (i j : (I dim)) :
    (∫ w : ↥(standardSphere dim), sphereRotationDerivative i j f w * u w ∂(sphereProbability dim)) =
      -(∫ w : ↥(standardSphere dim), f w * sphereRotationDerivative i j u w ∂(sphereProbability dim)) := by
  obtain ⟨F,hF,hFE⟩ := exists_global_extension_on_sphere hS hSS hf
  obtain ⟨U',hU',hUE⟩ := exists_global_extension_on_sphere hU hSU hu
  have h := integral_sphereRotationDerivative_skew i j F U' hF hU'
  change (∫ w : ↥(standardSphere dim), sphereRotationDerivative i j F w * U' w ∂(sphereProbability dim)) =
    -(∫ w : ↥(standardSphere dim), F w * sphereRotationDerivative i j U' w ∂(sphereProbability dim)) at h
  have hEq (w : ↥(standardSphere dim)) : F w = f w ∧ U' w = u w ∧
      sphereRotationDerivative i j F w = sphereRotationDerivative i j f w ∧
      sphereRotationDerivative i j U' w = sphereRotationDerivative i j u w := by
    have hF' := hFE w w.property
    have hU' := hUE w w.property
    exact ⟨hF'.eq_of_nhds,hU'.eq_of_nhds,
      congrArg (fun d : (X dim) →L[ℝ] ℝ => d (rotationVector i j w)) hF'.fderiv_eq,
      congrArg (fun d : (X dim) →L[ℝ] ℝ => d (rotationVector i j w)) hU'.fderiv_eq⟩
  calc
    _ = ∫ w : ↥(standardSphere dim), sphereRotationDerivative i j F w * U' w ∂(sphereProbability dim) := by
      exact integral_congr_ae (Eventually.of_forall (fun w =>
        congrArg₂ (· * ·) (hEq w).2.2.1.symm (hEq w).2.1.symm))
    _ = _ := h
    _ = _ := by
      congr 1
      exact integral_congr_ae (Eventually.of_forall (fun w =>
        congrArg₂ (· * ·) (hEq w).1 (hEq w).2.2.2))

private theorem continuousOn_sphere_integrable {f : (X dim) → ℝ}
    (hf : ContinuousOn f (standardSphere dim)) :
    Integrable (fun w : ↥(standardSphere dim) => f w) (sphereProbability dim) := by
  let : CompactSpace ↥(standardSphere dim) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (X dim)) 1)
  exact (hf.comp_continuous continuous_subtype_val (fun w => w.property)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Green transpose on the unit sphere, using the same probability
measure as the moving trace coefficients. -/
theorem integral_ballConormal_symm {U : Set (X dim)} (hU : IsOpen U)
    (hBU : closedBall (0 : (X dim)) 1 ⊆ U)
    {g : (MetricField dim)} (hg : SmoothMetric U g) {u b : (X dim) → ℝ}
    (hu : ContDiffOn ℝ ∞ u U) (hb : ContDiffOn ℝ ∞ b U)
    (hLapU : ∀ x ∈ ball (0 : (X dim)) 1, laplace g u x = 0)
    (hLapB : ∀ x ∈ ball (0 : (X dim)) 1, laplace g b x = 0) :
    (∫ w : ↥(standardSphere dim), b w * ballConormal g u w ∂(sphereProbability dim)) =
      ∫ w : ↥(standardSphere dim), u w * ballConormal g b w ∂(sphereProbability dim) := by
  have hZ := unitSphereFlux_wronskian_eq_zero_of_harmonic hU hBU hg hu hb hLapU hLapB
  let F (w : ↥(standardSphere dim)) := b w * ballConormal g u w - u w * ballConormal g b w
  have hZ' : (∫ w : ↥(standardSphere dim), F w ∂(chartSurfaceMeasure dim)) = 0 := by
    rw [← hZ]
    apply integral_congr_ae
    filter_upwards with w
    change F w = ⟪(w : (X dim)),wronskianFlux g u b w⟫_ℝ
    have he : wronskianFlux g u b w = b w • metricFluxVector g u w - u w • metricFluxVector g b w := by
      ext i
      simp only [wronskianFlux,metricFluxVector,PiLp.toLp_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    rw [he,inner_sub_right,real_inner_smul_right,real_inner_smul_right]
    rfl
  have hZn := (integral_unitSphereArea_mul_probability F).trans hZ'
  rw [integral_const_mul] at hZn
  have hSub : (standardSphere dim) ⊆ U := sphere_subset_closedBall.trans hBU
  have hI₁ : Integrable (fun w : ↥(standardSphere dim) => b w * ballConormal g u w) (sphereProbability dim) :=
    continuousOn_sphere_integrable ((hb.continuousOn.mul (continuousOn_ballConormal hU hg hu)).mono hSub)
  have hI₂ : Integrable (fun w : ↥(standardSphere dim) => u w * ballConormal g b w) (sphereProbability dim) :=
    continuousOn_sphere_integrable ((hu.continuousOn.mul (continuousOn_ballConormal hU hg hb)).mono hSub)
  have hDiff : (∫ w : ↥(standardSphere dim), b w * ballConormal g u w -
      u w * ballConormal g b w ∂(sphereProbability dim)) = 0 :=
    (mul_eq_zero.mp hZn).resolve_left unitSphereArea_pos.ne'
  rw [integral_sub hI₁ hI₂] at hDiff
  exact sub_eq_zero.mp hDiff

/-- Angular expression for the adjoint of a fixed-ball velocity. The
harmonic function (b) carries the conormal-weighted boundary data. -/
@[expose] def ballVelocityAdjoint (g : (MetricField dim)) (V : (X dim) → (X dim)) (ψ b : (X dim) → ℝ) (w : (X dim)) : ℝ :=
  ballConormal g b w -
    ∑ i, ∑ j, sphereRotationDerivative i j
      (fun z => ψ z * (z i * tangentialComponent g z (V z) j)) w

set_option maxHeartbeats 1200000 in
theorem integral_ballVelocityAdjoint
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : (X dim)) 1 ⊆ U) (hSS : (standardSphere dim) ⊆ S) (hSU : S ⊆ U)
    (hS₀ : (0 : (X dim)) ∉ S) {g : (MetricField dim)} (hg : SmoothMetric U g)
    {u b ψ : (X dim) → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hb : ContDiffOn ℝ ∞ b U)
    (hLapU : ∀ x ∈ ball (0 : (X dim)) 1, laplace g u x = 0)
    (hLapB : ∀ x ∈ ball (0 : (X dim)) 1, laplace g b x = 0)
    (hψ : ContDiffOn ℝ ∞ ψ S) {V : (X dim) → (X dim)} (hV : ContDiffOn ℝ ∞ V S)
    (hBdy : EqOn b (fun w => ψ w * conormalComponent g w (V w)) (standardSphere dim)) :
    (∫ w : ↥(standardSphere dim), ballVelocityAdjoint g V ψ b w * u w ∂(sphereProbability dim)) =
      ∫ w : ↥(standardSphere dim), ψ w * fderiv ℝ u w (V w) ∂(sphereProbability dim) := by
  have hWS : (standardSphere dim) ⊆ U := hSS.trans hSU
  have hC := (contDiffOn_ballConormalVector hg).mono hSU
  have hPos (w : (X dim)) (hw : w ∈ S) : 0 < ⟪w,ballConormalVector g w⟫_ℝ :=
    ballConormalVector_inner_pos (hg.2 w (hSU hw)) (fun hz => hS₀ (hz ▸ hw))
  have hN : ContDiffOn ℝ ∞ (fun w => conormalComponent g w (V w)) S :=
    (contDiffOn_id.inner ℝ hV).div (contDiffOn_id.inner ℝ hC) (fun w hw => (hPos w hw).ne')
  have hT : ContDiffOn ℝ ∞ (fun w => tangentialComponent g w (V w)) S :=
    hV.sub (hN.smul hC)
  let a (i j : (I dim)) (w : (X dim)) := ψ w * (w i * tangentialComponent g w (V w) j)
  have ha (i j : (I dim)) : ContDiffOn ℝ ∞ (a i j) S :=
    hψ.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn hT))
  have hR {W : Set (X dim)} (hW : IsOpen W) {f : (X dim) → ℝ} (hf : ContDiffOn ℝ ∞ f W) (i j : (I dim)) :
      ContinuousOn (sphereRotationDerivative i j f) W := by
    have hv : ContDiff ℝ ∞ (rotationVector i j) := by
      exact ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.smul contDiff_const).sub
        ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.smul contDiff_const)
    exact ((hf.fderiv_of_isOpen (m := ∞) hW (by simp)).clm_apply hv.contDiffOn).continuousOn
  let L (i j : (I dim)) (w : (X dim)) := sphereRotationDerivative i j (a i j) w * u w
  let R (i j : (I dim)) (w : (X dim)) := a i j w * sphereRotationDerivative i j u w
  have hL (i j : (I dim)) : Integrable (fun w : ↥(standardSphere dim) => L i j w) (sphereProbability dim) :=
    continuousOn_sphere_integrable (((hR hS (ha i j) i j).mono hSS).mul (hu.continuousOn.mono hWS))
  have hR' (i j : (I dim)) : Integrable (fun w : ↥(standardSphere dim) => R i j w) (sphereProbability dim) :=
    continuousOn_sphere_integrable (((ha i j).continuousOn.mono hSS).mul ((hR hU hu i j).mono hWS))
  have ht (i j : (I dim)) : (∫ w : ↥(standardSphere dim), L i j w ∂(sphereProbability dim)) =
      -(∫ w : ↥(standardSphere dim), R i j w ∂(sphereProbability dim)) :=
    sphere_rotationSkew_of_smoothNear hS hU hSS hWS (ha i j) hu i j
  have hC₁ : Integrable (fun w : ↥(standardSphere dim) => ballConormal g b w * u w) (sphereProbability dim) :=
    continuousOn_sphere_integrable
    (((continuousOn_ballConormal hU hg hb).mul hu.continuousOn).mono hWS)
  have hC₂ : Integrable (fun w : ↥(standardSphere dim) => b w * ballConormal g u w) (sphereProbability dim) :=
    continuousOn_sphere_integrable
    ((hb.continuousOn.mul (continuousOn_ballConormal hU hg hu)).mono hWS)
  have hCeq :
      (∫ w : ↥(standardSphere dim), ballConormal g b w * u w ∂(sphereProbability dim)) =
        ∫ w : ↥(standardSphere dim), b w * ballConormal g u w ∂(sphereProbability dim) := by
    simpa only [mul_comm (ballConormal g b _) (u _)] using
      (integral_ballConormal_symm hU hBU hg hu hb hLapU hLapB).symm
  have hEval (w : ↥(standardSphere dim)) : ψ w * fderiv ℝ u w (V w) =
      b w * ballConormal g u w + ∑ i, ∑ j, R i j w := by
    rw [fderiv_eq_conormal_add_rotations (hg.2 w (hWS w.property)) w.property, mul_add]
    simp only [R,a,Finset.mul_sum,← mul_assoc,hBdy w.property]
  simp_rw [hEval,ballVelocityAdjoint,sub_mul,Finset.sum_mul]
  change (∫ w : ↥(standardSphere dim), ballConormal g b w * u w - ∑ i, ∑ j, L i j w ∂(sphereProbability dim)) = _
  rw [integral_sub hC₁ (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hL i j))),
    integral_add hC₂ (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hR' i j))),
    hCeq,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hL i j)),
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hR' i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hL _ j),integral_finsetSum _ (fun j _ => hR' _ j),ht,
    Finset.sum_neg_distrib,sub_neg_eq_add]

end CalderonN
