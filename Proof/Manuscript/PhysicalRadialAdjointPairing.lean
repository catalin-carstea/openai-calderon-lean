module

public import Proof.Manuscript.PhysicalRadialAdjoint

import Proof.CalderonN.Moments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric MeasureTheory CalderonN
open scoped ContDiff InnerProductSpace

namespace CalderonPaper

open OAI.AnisotropicCalderon.SmoothSphereRotation

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The complex fixed-ball solution uses the two literal real Poisson
solutions. -/
@[expose] def complexFixedBallPoisson (M : MetricField dim) (g : X dim → ℂ) (z : X dim) : ℂ :=
  ⟨fixedBallPoisson M (fun x => (g x).re) z,fixedBallPoisson M (fun x => (g x).im) z⟩

theorem fderiv_complexFixedBallPoisson_apply
    {M : MetricField dim} {g : X dim → ℂ} (z v : X dim)
    (hR : DifferentiableAt ℝ (fixedBallPoisson M (fun x => (g x).re)) z)
    (hI : DifferentiableAt ℝ (fixedBallPoisson M (fun x => (g x).im)) z) :
    fderiv ℝ (complexFixedBallPoisson M g) z v =
      ⟨fderiv ℝ (fixedBallPoisson M (fun x => (g x).re)) z v,
       fderiv ℝ (fixedBallPoisson M (fun x => (g x).im)) z v⟩ := by
  let A := fixedBallPoisson M (fun x => (g x).re)
  let B := fixedBallPoisson M (fun x => (g x).im)
  let L : ℝ →L[ℝ] ℂ := Complex.ofRealCLM
  let R : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM
  have hEq : complexFixedBallPoisson M g = fun x => L (A x) + R (B x) := by
    funext x
    apply Complex.ext <;> simp [complexFixedBallPoisson,L,R,A,B,Complex.mul_re,Complex.mul_im]
  have hD := ((L.hasFDerivAt.comp z hR.hasFDerivAt).add
    (R.hasFDerivAt.comp z hI.hasFDerivAt)).fderiv
  have hD' : fderiv ℝ (fun x => L (A x) + R (B x)) z =
      L.comp (fderiv ℝ A z) + R.comp (fderiv ℝ B z) := hD
  rw [hEq,hD']
  apply Complex.ext <;> simp [L,R,A,B,Complex.mul_re,Complex.mul_im]

private def realRadialBallAdjoint (M : MetricField dim) (V : X dim → X dim)
    (W f : X dim → ℝ) (z : X dim) : ℝ :=
  W z * fderiv ℝ (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x)) z z -
    ∑ j, ∑ k, sphereRotationDerivative j k (fun x => f x * (x j * V x k)) z

omit [NeZero dim] [Nontrivial (Fin dim)] in
private theorem contDiffOn_realRadialBallAdjoint
    {M : MetricField dim} {V : X dim → X dim} {W f : X dim → ℝ} {S : Set (X dim)}
    (hS : IsOpen S) (hV : ContDiffOn ℝ ∞ V S) (hW : ContDiffOn ℝ ∞ W S)
    (hf : ContDiffOn ℝ ∞ f S)
    (hb : ContDiff ℝ ∞ (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x))) :
    ContDiffOn ℝ ∞ (realRadialBallAdjoint M V W f) S := by
  have hB : ContDiffOn ℝ ∞ (fun z : X dim =>
      fderiv ℝ (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x)) z z) S :=
    ((hb.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id).contDiffOn
  have hR (j k : I dim) : ContDiffOn ℝ ∞ (sphereRotationDerivative j k
      (fun x => f x * (x j * V x k))) S := by
    have hT : ContDiffOn ℝ ∞ (fun x => f x * (x j * V x k)) S := hf.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffOn.mul
        ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp_contDiffOn hV))
    have hVec : ContDiff ℝ ∞ (rotationVector j k : X dim → X dim) := by
      unfold rotationVector
      exact (((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.smul contDiff_const)).sub
        (((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.smul contDiff_const))
    exact (hT.fderiv_of_isOpen (m := ∞) hS (by simp)).clm_apply hVec.contDiffOn
  exact (hW.mul hB).sub (ContDiffOn.sum fun j _ => ContDiffOn.sum fun k _ => hR j k)

set_option maxHeartbeats 7000000 in
/-- Complex bilinear pairing for the actual Gauss radial adjoint. The four
real pairs use the released exact fixed-ball adjoint identity. -/
theorem integral_radialBallVelocityAdjoint_mul
    {M : MetricField dim} {V : X dim → X dim} {W : X dim → ℝ} {φ g : X dim → ℂ}
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hBU : closedBall (0 : X dim) 1 ⊆ U) (hSS : standardSphere dim ⊆ S)
    (hSU : S ⊆ U) (hS₀ : (0 : X dim) ∉ S) (hM : SmoothMetric U M)
    (hV : ContDiffOn ℝ ∞ V S) (hW : ContDiffOn ℝ ∞ W S) (hW₀ : ∀ z ∈ S, W z ≠ 0)
    {c : ℝ} (hc : c ≠ 0)
    (hRad : EqOn (ballConormalVector M) (fun z => (c * W z) • z) (standardSphere dim))
    (hφ : ContDiffOn ℝ ∞ φ S) (hg : ContDiffOn ℝ ∞ g S) :
    (∫ z : ↥(standardSphere dim), radialBallVelocityAdjoint M V W φ z * g z ∂sphereProbability dim) =
      ∫ z : ↥(standardSphere dim), φ z * fderiv ℝ (complexFixedBallPoisson M g) z (V z)
        ∂sphereProbability dim := by
  let σ := sphereProbability dim
  have : CompactSpace ↥(standardSphere dim) := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  let φR := fun x => (φ x).re
  let φI := fun x => (φ x).im
  let gR := fun x => (g x).re
  let gI := fun x => (g x).im
  let uR := fixedBallPoisson M gR
  let uI := fixedBallPoisson M gI
  let A := realRadialBallAdjoint M V W φR
  let B := realRadialBallAdjoint M V W φI
  let dR (x : X dim) := fderiv ℝ uR x (V x)
  let dI (x : X dim) := fderiv ℝ uI x (V x)
  have hφR : ContDiffOn ℝ ∞ φR S := Complex.reCLM.contDiff.comp_contDiffOn hφ
  have hφI : ContDiffOn ℝ ∞ φI S := Complex.imCLM.contDiff.comp_contDiffOn hφ
  have hgR : ContDiffOn ℝ ∞ gR S := Complex.reCLM.contDiff.comp_contDiffOn hg
  have hgI : ContDiffOn ℝ ∞ gI S := Complex.imCLM.contDiff.comp_contDiffOn hg
  have huR : FixedBallSolution M gR uR := fixedBallPoisson_solution hU hBU hM ⟨S,hS,hSS,hgR⟩
  have huI : FixedBallSolution M gI uI := fixedBallPoisson_solution hU hBU hM ⟨S,hS,hSS,hgI⟩
  have hInner : ContDiffOn ℝ ∞ (fun x => ⟪x,V x⟫_ℝ) S := contDiffOn_id.inner ℝ hV
  have hBnd (f : X dim → ℝ) (hf : ContDiffOn ℝ ∞ f S) :
      FixedBallSolution M (fun x => f x * ⟪x,V x⟫_ℝ / W x)
        (fixedBallPoisson M (fun x => f x * ⟪x,V x⟫_ℝ / W x)) :=
    fixedBallPoisson_solution hU hBU hM ⟨S,hS,hSS,(hf.mul hInner).div hW hW₀⟩
  have hPair {f a u : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hu : FixedBallSolution M a u) :
      (∫ z : ↥(standardSphere dim), realRadialBallAdjoint M V W f z * a z ∂σ) =
        ∫ z : ↥(standardSphere dim), f z * fderiv ℝ u z (V z) ∂σ := by
    let G (q : ℝ × X dim) := M q.2
    let Z (q : ℝ × X dim) := V q.2
    let ψ (q : ℝ × X dim) := f q.2
    have hEq (z : ↥(standardSphere dim)) :
        parametricBallVelocityAdjoint G Z ψ (0,z) = realRadialBallAdjoint M V W f z :=
      parametricBallVelocityAdjoint_gauss_radial_response (0 : ℝ) hU hS hBU hSS hSU hS₀
        hM hV hf c hc W hRad (hBnd f hf) z.property
    have hP := integral_parametricBallVelocityAdjoint (0 : ℝ) hU hS hBU hSS hSU hS₀
      (g := G) (V := Z) (ψ := ψ) hM hV hf hu.1.contDiffOn hu.2.2
    calc
      _ = ∫ z : ↥(standardSphere dim), parametricBallVelocityAdjoint G Z ψ (0,z) * u z ∂σ := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          change realRadialBallAdjoint M V W f z * a z = parametricBallVelocityAdjoint G Z ψ (0,z) * u z
          rw [hEq z,hu.2.1 z.property]
      _ = _ := hP
  have hA : ContDiffOn ℝ ∞ A S := contDiffOn_realRadialBallAdjoint hS hV hW hφR (hBnd _ hφR).1
  have hB : ContDiffOn ℝ ∞ B S := contDiffOn_realRadialBallAdjoint hS hV hW hφI (hBnd _ hφI).1
  have hdR : ContDiffOn ℝ ∞ dR S := ((huR.1.fderiv_right (m := ∞) (by simp)).contDiffOn).clm_apply hV
  have hdI : ContDiffOn ℝ ∞ dI S := ((huI.1.fderiv_right (m := ∞) (by simp)).contDiffOn).clm_apply hV
  have hContinuous {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : X dim → F}
      (hf : ContDiffOn ℝ ∞ f S) : Continuous (fun z : ↥(standardSphere dim) => f z) :=
    continuousOn_univ.mp (hf.continuousOn.comp continuous_subtype_val.continuousOn
      (fun z _ => hSS z.property))
  have hMk {f a : ↥(standardSphere dim) → ℝ} (hf : Continuous f) (ha : Continuous a) :
      Continuous (fun z => (⟨f z,a z⟩ : ℂ)) := by
    convert (Complex.continuous_ofReal.comp hf).add
      (continuous_const.mul (Complex.continuous_ofReal.comp ha)) using 1
    funext z
    change (⟨f z,a z⟩ : ℂ) = (f z : ℂ) + Complex.I * (a z : ℂ)
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hDer (z : X dim) : fderiv ℝ (complexFixedBallPoisson M g) z (V z) = ⟨dR z,dI z⟩ :=
    fderiv_complexFixedBallPoisson_apply z (V z) (huR.1.differentiable (by simp) z)
      (huI.1.differentiable (by simp) z)
  have hLi : Integrable (fun z : ↥(standardSphere dim) => radialBallVelocityAdjoint M V W φ z * g z) σ :=
    ((hMk (hContinuous hA) (hContinuous hB)).mul (hContinuous hg)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hRi : Integrable (fun z : ↥(standardSphere dim) =>
      φ z * fderiv ℝ (complexFixedBallPoisson M g) z (V z)) σ := by
    simp_rw [hDer]
    exact ((hContinuous hφ).mul (hMk (hContinuous hdR) (hContinuous hdI))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hInt {f a : X dim → ℝ} (hf : ContDiffOn ℝ ∞ f S) (ha : ContDiffOn ℝ ∞ a S) :
      Integrable (fun z : ↥(standardSphere dim) => f z * a z) σ :=
    ((hContinuous hf).mul (hContinuous ha)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · change (RCLike.re : ℂ → ℝ) _ = (RCLike.re : ℂ → ℝ) _
    rw [← integral_re hLi,← integral_re hRi]
    simp_rw [hDer,RCLike.re_eq_complex_re,Complex.mul_re]
    change (∫ z : ↥(standardSphere dim), A z * gR z - B z * gI z ∂σ) =
      ∫ z : ↥(standardSphere dim), φR z * dR z - φI z * dI z ∂σ
    rw [integral_sub (hInt hA hgR) (hInt hB hgI),integral_sub (hInt hφR hdR) (hInt hφI hdI),
      hPair hφR huR,hPair hφI huI]
  · change (RCLike.im : ℂ → ℝ) _ = (RCLike.im : ℂ → ℝ) _
    rw [← integral_im hLi,← integral_im hRi]
    simp_rw [hDer,RCLike.im_eq_complex_im,Complex.mul_im]
    change (∫ z : ↥(standardSphere dim), A z * gI z + B z * gR z ∂σ) =
      ∫ z : ↥(standardSphere dim), φR z * dI z + φI z * dR z ∂σ
    rw [integral_add (hInt hA hgI) (hInt hB hgR),integral_add (hInt hφR hdI) (hInt hφI hdR),
      hPair hφR huI,hPair hφI huR]

end CalderonPaper
