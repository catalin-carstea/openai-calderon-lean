module

public import Proof.Manuscript.PhysicalRadialAdjoint
public import Proof.Manuscript.NormalizedConformalGauss
public import Proof.Manuscript.MovingTraceSymbols

public import Proof.CalderonN.FlatBallPolynomials
import Proof.CalderonN.NormalizedVelocityAtZero
import Proof.CalderonN.FixedBallPoissonCongruence
import Proof.CalderonN.DilationHarmonic
import Proof.CalderonN.HarmonicL2Space
import Mathlib.Tactic

public section

noncomputable section

open Set Metric CalderonN
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [NeZero dim] [Nontrivial (Fin dim)] in
/-- The pointwise conormal vector depends on the metric at its center of evaluation. -/
theorem ballConormalVector_congr_at
    {g M : MetricField dim} {z : X dim} (he : g z = M z) :
    ballConormalVector g z = ballConormalVector M z := by
  ext j
  simp only [ballConormalVector,PiLp.toLp_apply,divergenceCoeff,chartVolume,he]

/-- The normalized Gauss response for a flat scalar metric on the ball is
M-independent, since its Poisson equation and radial weight are Euclidean. -/
theorem radialBallVelocityAdjoint_eq_flatAngularVelocityAdjoint
    {M : MetricField dim} {t : ℝ} (ht : 0 < t) {V : X dim → X dim}
    {W : X dim → ℝ} {φ : X dim → ℂ} {U S : Set (X dim)}
    (hU : IsOpen U) (hS : IsOpen S) (hBU : closedBall (0 : X dim) 1 ⊆ U)
    (hSS : standardSphere dim ⊆ S) (hS₀ : (0 : X dim) ∉ S) (hM : SmoothMetric U M)
    (hEq : EqOn (flatBallMetric t) M (closedBall (0 : X dim) 1))
    (hV : ContDiffOn ℝ ∞ V S) (hW : ContDiffOn ℝ ∞ W S) (hW₀ : ∀ z ∈ S, W z ≠ 0)
    (hWflat : EqOn W 1 (standardSphere dim)) (hφ : ContDiffOn ℝ ∞ φ S)
    {z : X dim} (hz : z ∈ standardSphere dim) :
    radialBallVelocityAdjoint M V W φ z = flatAngularVelocityAdjoint V φ z := by
  let g₀ : MetricField dim := fun _ => 1
  have hg₀ : flatBallMetric (dim := dim) 1 = g₀ := by simp [g₀,flatBallMetric]
  have hInner : ContDiffOn ℝ ∞ (fun x => ⟪x,V x⟫_ℝ) S := contDiffOn_id.inner ℝ hV
  have hR : ContDiffOn ℝ ∞ (fun x => (φ x).re) S := Complex.reCLM.contDiff.comp_contDiffOn hφ
  have hI : ContDiffOn ℝ ∞ (fun x => (φ x).im) S := Complex.imCLM.contDiff.comp_contDiffOn hφ
  have hFlat : EqOn (ballConormalVector g₀) (fun x => (1 * (1 : ℝ)) • x) (standardSphere dim) := by
    intro x _
    rw [← hg₀,ballConormalVector_flat (by norm_num : (0 : ℝ) < 1)]
    simp
  have hResp {f : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
      FixedBallSolution g₀ (fun x => f x * ⟪x,V x⟫_ℝ / 1)
        (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x)) := by
    let b := fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x)
    have hMsol : FixedBallSolution M (fun x => f x * ⟪x,V x⟫_ℝ / W x) b :=
      fixedBallPoisson_solution hU hBU hM ⟨S,hS,hSS,(hf.mul hInner).div hW hW₀⟩
    have hFsol := FixedBallSolution.congr_metric_on_closedBall hMsol hEq
    refine ⟨hFsol.1,fun x hx => ?_,fun x hx => ?_⟩
    · change b x = f x * ⟪x,V x⟫_ℝ / 1
      have hWx : W x = 1 := hWflat hx
      rw [← hWx]
      exact hFsol.2.1 hx
    · have hLap := hFsol.2.2 x hx
      rw [laplace_flatBallMetric ht] at hLap
      rw [← hg₀,laplace_flatBallMetric (by norm_num : (0 : ℝ) < 1)]
      rw [(mul_eq_zero.mp hLap).resolve_left (inv_ne_zero (pow_ne_zero _ ht.ne')),mul_zero]
  have hReal {f : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
      parametricBallVelocityAdjoint (fun _ : ℝ × X dim => (1 : Mat dim)) (fun q => V q.2)
        (fun q => f q.2) (0,z) =
      1 * fderiv ℝ (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x)) z z -
        ∑ j, ∑ k, sphereRotationDerivative j k (fun x => f x * (x j * V x k)) z :=
    parametricBallVelocityAdjoint_gauss_radial_response (0 : ℝ) isOpen_univ hS (subset_univ _)
      hSS (subset_univ _) hS₀
      (by change SmoothMetric univ g₀; rw [← hg₀]; exact smoothMetric_flatBallMetric (by norm_num))
      hV hf 1 one_ne_zero
      (fun _ => 1) hFlat (hResp hf) hz
  apply Complex.ext
  · change W z * _ - _ = _
    rw [hWflat hz]
    exact (hReal hR).symm
  · change W z * _ - _ = _
    rw [hWflat hz]
    exact (hReal hI).symm

/-- At zero radius the normalized Poisson metric is scalar Euclidean and
its scaled physical velocity is the exact affine frame velocity. -/
theorem radialBallVelocityAdjoint_normalized_zero
    {Y Ω : Set (X dim)} (hY : IsOpen Y)
    {γ g : MetricField dim} {E : X dim × X dim → X dim} {e : Frame dim} {ρ : X dim → ℝ}
    (hE : ContDiff ℝ ∞ E) (hN : NormalCoordinates Y Ω γ E ρ)
    {y : X dim} (hy : y ∈ Y)
    (he : ∀ j k, metricPair γ y (e y j) (e y k) = if j=k then 1 else 0)
    {c : ℝ} (hc : 0 < c) (hγ : γ y = c • g y) (b : ℝ) (i : I dim)
    {M : MetricField dim} {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : X dim) 1 ⊆ U) (hSS : standardSphere dim ⊆ S)
    (hSU : S ⊆ U) (hS₀ : (0 : X dim) ∉ S) (hM : SmoothMetric U M)
    (hEq : EqOn (normalizedBallMetric g E e y 0) M (closedBall (0 : X dim) 1))
    {φ : X dim → ℂ} (hφ : ContDiffOn ℝ ∞ φ S) {z : X dim} (hz : z ∈ standardSphere dim) :
    let t := Real.sqrt c⁻¹
    let a := frameCoordinates γ y (e y) (axis i)
    radialBallVelocityAdjoint M (fun x => scaledNormalTraceVelocity γ E e y 0 b x (axis i))
      (sphereGaussWeight M (t^(dim-2))) φ z = flatAngularVelocityAdjoint (fun x => a+b • x) φ z := by
  dsimp only
  let a := frameCoordinates γ y (e y) (axis i)
  let t := Real.sqrt c⁻¹
  have ht : 0 < t := Real.sqrt_pos.mpr (inv_pos.mpr hc)
  have hFlat : EqOn (flatBallMetric t) M (closedBall (0 : X dim) 1) := by
    intro w hw
    rw [← hEq hw,normalizedBallMetric_zero_of_conformal hE hN hy he hc hγ]
    change t^2 • (1 : Mat dim) = c⁻¹ • (1 : Mat dim)
    rw [show t^2 = c⁻¹ from Real.sq_sqrt (inv_nonneg.mpr hc.le)]
  let W := sphereGaussWeight M (t^(dim-2))
  have ht₀ : 0 < t^(dim-2) := pow_pos ht _
  have hWflat : EqOn W 1 (standardSphere dim) := by
    intro x hx
    have hC := ballConormalVector_congr_at (hFlat (sphere_subset_closedBall hx))
    change ⟪x,ballConormalVector M x⟫_ℝ / t^(dim-2) = 1
    rw [← hC,ballConormalVector_flat ht, real_inner_smul_right,real_inner_self_eq_norm_sq,
      mem_sphere_zero_iff_norm.mp hx,one_pow,mul_one,div_self ht₀.ne']
  have hvEq : (fun x => scaledNormalTraceVelocity γ E e y 0 b x (axis i)) =
      fun x => a+b • x := by
    funext x
    exact scaledNormalTraceVelocity_zero hY hE hN hy he b x (axis i)
  have hv : ContDiffOn ℝ ∞ (fun x : X dim => a+b • x) S :=
    ((contDiff_const (c := a)).add (b • ContinuousLinearMap.id ℝ (X dim)).contDiff).contDiffOn
  rw [hvEq]
  exact radialBallVelocityAdjoint_eq_flatAngularVelocityAdjoint ht hU hS hBU hSS hS₀ hM hFlat hv
    ((sphereGaussWeight_contDiffOn hM _).mono hSU)
    (fun x hx => (sphereGaussWeight_pos ht₀ (hM.2 x (hSU hx)) (fun e => hS₀ (e ▸ hx))).ne')
    hWflat hφ hz

set_option maxHeartbeats 4000000 in
/-- The actual flat velocity adjoint is affine-linear in the independent
slope parameter, with precisely the translation and radial operators used
in the moving-trace statement. -/
theorem flatAngularVelocityAdjoint_affine
    (a : X dim) (b : ℝ) {φ : X dim → ℂ} (hφ : smoothNear φ (standardSphere dim))
    {z : X dim} (hz : z ∈ standardSphere dim) :
    flatAngularVelocityAdjoint (fun x => a+b • x) φ z =
      flatAngularVelocityAdjoint (fun _ => a) φ z + b • flatAngularVelocityAdjoint id φ z := by
  let M : MetricField dim := fun _ => 1
  let V₀ : X dim → X dim := fun _ => a
  let V₁ : X dim → X dim := id
  let V : X dim → X dim := fun x => a+b • x
  have hM : SmoothMetric univ M := by simpa [M,flatBallMetric] using
    (smoothMetric_flatBallMetric (dim := dim) (by norm_num : (0 : ℝ) < 1))
  have hV₀ : ContDiff ℝ ∞ V₀ := contDiff_const
  have hV₁ : ContDiff ℝ ∞ V₁ := contDiff_id
  have hV : ContDiff ℝ ∞ V :=
    ((contDiff_const (c := a)).add (b • ContinuousLinearMap.id ℝ (X dim)).contDiff)
  obtain ⟨D,hD,hDS,hφD⟩ := hφ
  let S : Set (X dim) := D ∩ {0}ᶜ
  have hS : IsOpen S := hD.inter isClosed_singleton.isOpen_compl
  have hSS : standardSphere dim ⊆ S := fun x hx =>
    ⟨hDS hx,norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hx).trans_ne one_ne_zero)⟩
  have hS₀ : (0 : X dim) ∉ S := fun hz => hz.2 rfl
  have hφS := hφD.mono (show S ⊆ D from inter_subset_left)
  have hIn {X : X dim → X dim} (hX : ContDiff ℝ ∞ X) :
      radialBallVelocityAdjoint M X 1 φ z = flatAngularVelocityAdjoint X φ z := by
    apply radialBallVelocityAdjoint_eq_flatAngularVelocityAdjoint (t := 1) (by norm_num)
      isOpen_univ hS (subset_univ _) hSS hS₀ hM ?_ hX.contDiffOn contDiffOn_const
      (fun _ _ => one_ne_zero) (fun _ _ => rfl) hφS hz
    intro x _
    simp [M,flatBallMetric]
  rw [← hIn hV,← hIn hV₀,← hIn hV₁]
  have hScalar {f : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) :
      (fderiv ℝ (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / 1)) z z -
        ∑ j, ∑ k, sphereRotationDerivative j k (fun x => f x * (x j * V x k)) z) =
      (fderiv ℝ (fixedBallPoisson M (fun x => f x * ⟪x,V₀ x⟫_ℝ / 1)) z z -
        ∑ j, ∑ k, sphereRotationDerivative j k (fun x => f x * (x j * V₀ x k)) z) + b *
      (fderiv ℝ (fixedBallPoisson M (fun x => f x * ⟪x,V₁ x⟫_ℝ / 1)) z z -
        ∑ j, ∑ k, sphereRotationDerivative j k (fun x => f x * (x j * V₁ x k)) z) := by
    let d (L : X dim → X dim) (x : X dim) := f x * ⟪x,L x⟫_ℝ / 1
    let u₀ := fixedBallPoisson M (d V₀)
    let u₁ := fixedBallPoisson M (d V₁)
    have hPoisson {L : X dim → X dim} (hL : ContDiff ℝ ∞ L) :
        FixedBallSolution M (d L) (fixedBallPoisson M (d L)) :=
      fixedBallPoisson_solution isOpen_univ (subset_univ _) hM
        ⟨S,hS,hSS,(hf.mul (contDiffOn_id.inner ℝ hL.contDiffOn)).div_const 1⟩
    have h₀ : FixedBallSolution M (d V₀) u₀ := hPoisson hV₀
    have h₁ : FixedBallSolution M (d V₁) u₁ := hPoisson hV₁
    have hSum : FixedBallSolution M (fun x => d V₀ x + b * d V₁ x) (fun x => u₀ x + b * u₁ x) := by
      refine ⟨h₀.1.add (contDiff_const.mul h₁.1),fun x hx => ?_,fun x hx => ?_⟩
      · change u₀ x + b * u₁ x = d V₀ x + b * d V₁ x
        rw [h₀.2.1 hx,h₁.2.1 hx]
      · have hNeg := h₁.const_mul (-b)
        rw [show (fun z => u₀ z + b * u₁ z) = (fun z => u₀ z - (-b) * u₁ z) by funext x; ring,
          laplace_sub isOpen_univ M h₀.1.contDiffOn hNeg.1.contDiffOn (mem_univ x),
          h₀.2.2 x hx,hNeg.2.2 x hx,sub_zero]
    have hd : EqOn (d V) (fun x => d V₀ x + b * d V₁ x) (standardSphere dim) := by
      intro x _
      simp only [d,V,V₀,V₁,id_eq,inner_add_right,real_inner_smul_right,div_one]
      ring
    have hDer := congrArg (fun A : X dim →L[ℝ] ℝ => A z)
      (fixedBallPoisson_fderiv_eq_of_solution isOpen_univ (subset_univ _) hM hSum hd (sphere_subset_closedBall hz))
    have hDu₀ : DifferentiableAt ℝ u₀ z := h₀.1.differentiable (by simp) z
    have hDu₁ : DifferentiableAt ℝ u₁ z := h₁.1.differentiable (by simp) z
    have hDer' : fderiv ℝ (fixedBallPoisson M (d V)) z z =
        fderiv ℝ u₀ z z + b * fderiv ℝ u₁ z z := by
      simpa only [fderiv_fun_add hDu₀ (hDu₁.const_mul b),fderiv_const_mul hDu₁,add_apply,smul_apply,smul_eq_mul]
        using hDer
    let F (L : X dim → X dim) (j k : I dim) (x : X dim) := f x * (x j * L x k)
    have hRot (j k : I dim) : sphereRotationDerivative j k (F V j k) z =
        sphereRotationDerivative j k (F V₀ j k) z + b * sphereRotationDerivative j k (F V₁ j k) z := by
      have hEq : F V j k = fun x => F V₀ j k x + b * F V₁ j k x := by
        funext x
        simp only [F,V,V₀,V₁,id_eq,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
        ring
      have hDiff {L : X dim → X dim} (hL : ContDiff ℝ ∞ L) : DifferentiableAt ℝ (F L j k) z := by
        have hfz := (hf.contDiffAt (hS.mem_nhds (hSS hz))).differentiableAt (by simp)
        exact hfz.mul ((EuclideanSpace.proj (𝕜 := ℝ) j).differentiableAt.mul
          ((EuclideanSpace.proj (𝕜 := ℝ) k).differentiableAt.comp z (hL.differentiable (by simp) z)))
      simp only [hEq,sphereRotationDerivative,fderiv_fun_add (hDiff hV₀) ((hDiff hV₁).const_mul b),
        fderiv_const_mul (hDiff hV₁),add_apply,smul_apply,smul_eq_mul]
    change fderiv ℝ (fixedBallPoisson M (d V)) z z -
        (∑ j, ∑ k, sphereRotationDerivative j k (F V j k) z) = _
    simp_rw [hDer',hRot,Finset.sum_add_distrib,← Finset.mul_sum]
    change _ = (fderiv ℝ u₀ z z - _) + b * (fderiv ℝ u₁ z z - _)
    ring
  rw [Complex.real_smul]
  apply Complex.ext
  · simp only [radialBallVelocityAdjoint,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Pi.one_apply,one_mul,zero_mul,sub_zero]
    exact hScalar (f := fun x => (φ x).re) (Complex.reCLM.contDiff.comp_contDiffOn hφS)
  · simp only [radialBallVelocityAdjoint,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Pi.one_apply,one_mul,zero_mul,add_zero]
    exact hScalar (f := fun x => (φ x).im) (Complex.imCLM.contDiff.comp_contDiffOn hφS)

end CalderonPaper
