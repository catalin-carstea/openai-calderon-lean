module

public import Proof.Manuscript.MovingTrace.ComplexPoissonCorrection
public import Proof.Manuscript.PhysicalRadialAdjointPairing
public import Proof.CalderonN.FlatAngularAdjoint
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 4800000
set_option backward.isDefEq.respectTransparency false

open CalderonN CalderonN.BallDirichlet Set Filter Metric MeasureTheory
open OAI.AnisotropicCalderon.SmoothSphereRotation
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
local notation "Z" => X dim
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The exact radial velocity adjoint on an open geometry set. The
surrounding annulus is a domain for the differential boundary data. -/
structure SmoothRadialVelocity (G : BallPoissonTube P dim) where
  U : Set P
  openU : IsOpen U
  subset : U ⊆ G.V
  S : Set Z
  openS : IsOpen S
  sphere_mem : standardSphere dim ⊆ S
  tube_mem : U ×ˢ S ⊆ G.U
  origin_off : (0 : Z) ∉ S
  velocity : P × Z → Z
  weight : P × Z → ℝ
  smoothV : ContDiffOn ℝ ∞ velocity (U ×ˢ S)
  smoothW : ContDiffOn ℝ ∞ weight (U ×ˢ S)
  weight_ne_zero : ∀ q ∈ U ×ˢ S, weight q ≠ 0
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  radial : ∀ p ∈ U, EqOn (ballConormalVector (fun z => G.g (p,z)))
    (fun z => (scale * weight (p,z)) • z) (standardSphere dim)

namespace SmoothRadialVelocity

variable {G : BallPoissonTube P dim} (A : SmoothRadialVelocity G)

def operator (p : P) : SphereOperator dim :=
  radialBallVelocityAdjoint (fun z => G.g (p,z)) (fun z => A.velocity (p,z)) (fun z => A.weight (p,z))

def normalInput (φ : Z → ℂ) (p : P) (z : Z) : ℂ :=
  φ z * ((⟪z,A.velocity (p,z)⟫_ℝ / A.weight (p,z) : ℝ) : ℂ)

def rotationWeight (i j : I dim) (q : P × Z) : ℂ := ((q.2 i * A.velocity q j : ℝ) : ℂ)

theorem normalInput_contDiffOn {p : P} (hp : p ∈ A.U)
    {S : Set Z} (hS : S ⊆ A.S) {φ : Z → ℂ} (hφ : ContDiffOn ℝ ∞ φ S) :
    ContDiffOn ℝ ∞ (A.normalInput φ p) S := by
  have hV := A.smoothV.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun z hz => (show (p,z) ∈ A.U ×ˢ A.S from ⟨hp,hS hz⟩))
  have hW := A.smoothW.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun z hz => (show (p,z) ∈ A.U ×ˢ A.S from ⟨hp,hS hz⟩))
  exact hφ.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((contDiffOn_id.inner ℝ hV).div hW (fun z hz => A.weight_ne_zero (p,z) ⟨hp,hS hz⟩)))

theorem rotationWeight_contDiffOn (i j : I dim) :
    ContDiffOn ℝ ∞ (A.rotationWeight i j) (A.U ×ˢ A.S) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).contDiffOn.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn A.smoothV))

theorem metric_smooth_at_p {p : P} (hp : p ∈ A.U) :
    SmoothMetric ((Prod.mk p) ⁻¹' G.U) (fun z => G.g (p,z)) := by
  exact ⟨fun i j => (G.smoothG i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ hx => hx),fun x hx => G.posG _ hx⟩

theorem closedBall_subset_metric_room {p : P} (hp : p ∈ A.U) :
    closedBall (0:Z) 1 ⊆ (Prod.mk p) ⁻¹' G.U :=
  fun z hz => G.contains ⟨A.subset hp,hz⟩

theorem complexFixedBallPoisson_contDiff {p : P} (hp : p ∈ A.U)
    {φ : Z → ℂ} (hφ : smoothNear φ (standardSphere dim)) :
    ContDiff ℝ ∞ (complexFixedBallPoisson (fun z => G.g (p,z)) φ) := by
  obtain ⟨S,hS,hSS,hφS⟩ := hφ
  have hO : IsOpen ((Prod.mk p) ⁻¹' G.U) := G.openU.preimage (continuous_const.prodMk continuous_id)
  have hB := A.closedBall_subset_metric_room hp
  have hM := A.metric_smooth_at_p hp
  have hR := fixedBallPoisson_solution hO hB hM
    ⟨S,hS,hSS,Complex.reCLM.contDiff.comp_contDiffOn hφS⟩
  have hI := fixedBallPoisson_solution hO hB hM
    ⟨S,hS,hSS,Complex.imCLM.contDiff.comp_contDiffOn hφS⟩
  exact Complex.equivRealProdCLM.symm.contDiff.comp (hR.1.prodMk hI.1)

theorem operator_eq_complex_formula {p : P} (hp : p ∈ A.U)
    {φ : Z → ℂ} {S : Set Z} (hS : IsOpen S) (hSS : standardSphere dim ⊆ S)
    (hSA : S ⊆ A.S) (hφ : ContDiffOn ℝ ∞ φ S) {z : Z} (hz : z ∈ S) :
    A.operator p φ z =
      (A.weight (p,z) : ℂ) * fderiv ℝ (complexFixedBallPoisson (fun x => G.g (p,x))
        (A.normalInput φ p)) z z -
      ∑ i, ∑ j, fderiv ℝ (fun x => φ x * A.rotationWeight i j (p,x)) z (rotationVector i j z) := by
  let M := fun x => G.g (p,x)
  let d := A.normalInput φ p
  have hd := A.normalInput_contDiffOn hp hSA hφ
  have hO : IsOpen ((Prod.mk p) ⁻¹' G.U) := G.openU.preimage (continuous_const.prodMk continuous_id)
  have hB := A.closedBall_subset_metric_room hp
  have hM := A.metric_smooth_at_p hp
  have hR := fixedBallPoisson_solution hO hB hM
    ⟨S,hS,hSS,Complex.reCLM.contDiff.comp_contDiffOn hd⟩
  have hI := fixedBallPoisson_solution hO hB hM
    ⟨S,hS,hSS,Complex.imCLM.contDiff.comp_contDiffOn hd⟩
  have hD := fderiv_complexFixedBallPoisson_apply (M := M) (g := d) z z
    (hR.1.differentiable (by simp) z) (hI.1.differentiable (by simp) z)
  have hRe : (fun x => (d x).re) = fun x => (φ x).re * ⟪x,A.velocity (p,x)⟫_ℝ / A.weight (p,x) := by
    funext x
    simp [d,normalInput,Complex.mul_re,mul_div_assoc]
  have hIm : (fun x => (d x).im) = fun x => (φ x).im * ⟪x,A.velocity (p,x)⟫_ℝ / A.weight (p,x) := by
    funext x
    simp [d,normalInput,Complex.mul_im,mul_div_assoc,mul_comm]
  have hRot (i j : I dim) : DifferentiableAt ℝ (fun x => φ x * A.rotationWeight i j (p,x)) z := by
    refine ((hφ.mul ((A.rotationWeight_contDiffOn i j).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun x hx => ?_))).contDiffAt (hS.mem_nhds hz)).differentiableAt (by simp)
    exact ⟨hp,hSA hx⟩
  have hRJ (R : ℂ →L[ℝ] ℝ) (i j : I dim) :
      R (fderiv ℝ (fun x => φ x * A.rotationWeight i j (p,x)) z (rotationVector i j z)) =
        sphereRotationDerivative i j (R ∘ (fun x => φ x * A.rotationWeight i j (p,x))) z := by
    have h := (R.hasFDerivAt.comp z (hRot i j).hasFDerivAt).fderiv
    rw [sphereRotationDerivative,h]
    rfl
  have hRH (i j : I dim) : Complex.reCLM ∘ (fun x => φ x * A.rotationWeight i j (p,x)) =
      (fun x => (φ x).re * (x i * A.velocity (p,x) j)) := by
    funext x
    simp [rotationWeight,Complex.mul_re]
  have hIH (i j : I dim) : Complex.imCLM ∘ (fun x => φ x * A.rotationWeight i j (p,x)) =
      (fun x => (φ x).im * (x i * A.velocity (p,x) j)) := by
    funext x
    simp [rotationWeight,Complex.mul_im,mul_comm]
  change _ = (A.weight (p,z) : ℂ) * fderiv ℝ (complexFixedBallPoisson M d) z z - _
  rw [hD,hRe,hIm]
  apply Complex.ext
  · simp only [operator,radialBallVelocityAdjoint,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact ((hRJ Complex.reCLM i j).trans (congrArg (fun a => sphereRotationDerivative i j a z) (hRH i j))).symm
  · simp only [operator,radialBallVelocityAdjoint,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,zero_mul,add_zero,Complex.im_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact ((hRJ Complex.imCLM i j).trans (congrArg (fun a => sphereRotationDerivative i j a z) (hIH i j))).symm

theorem operator_contDiffOn {p : P} (hp : p ∈ A.U)
    {φ : Z → ℂ} {S : Set Z} (hS : IsOpen S) (hSS : standardSphere dim ⊆ S)
    (hSA : S ⊆ A.S) (hφ : ContDiffOn ℝ ∞ φ S) :
    ContDiffOn ℝ ∞ (A.operator p φ) S := by
  have hd := A.normalInput_contDiffOn hp hSA hφ
  have hP := A.complexFixedBallPoisson_contDiff hp ⟨S,hS,hSS,hd⟩
  have hW := A.smoothW.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun z hz => (show (p,z) ∈ A.U ×ˢ A.S from ⟨hp,hSA hz⟩))
  have hN := (Complex.ofRealCLM.contDiff.comp_contDiffOn hW).mul
    ((hP.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_id).contDiffOn
  have hR (i j : I dim) : ContDiffOn ℝ ∞ (fun z =>
      fderiv ℝ (fun x => φ x * A.rotationWeight i j (p,x)) z (rotationVector i j z)) S := by
    have hC := (A.rotationWeight_contDiffOn i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun z hz => (show (p,z) ∈ A.U ×ˢ A.S from ⟨hp,hSA hz⟩))
    exact ((hφ.mul hC).fderiv_of_isOpen (m := ∞) hS (by simp)).clm_apply
      (contDiff_rotationVector i j).contDiffOn
  exact (hN.sub (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => hR i j)).congr
    (fun z hz => A.operator_eq_complex_formula hp hS hSS hSA hφ hz)

end SmoothRadialVelocity
end CalderonPaper
