module

public import Proof.Manuscript.MovingTrace.VelocityChartPlaneDatum
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

noncomputable section
set_option maxHeartbeats 3700000
set_option backward.isDefEq.respectTransparency false

open CalderonN Set Metric Filter MeasureTheory
open OAI.AnisotropicCalderon.SmoothSphereRotation
open scoped ContDiff Topology InnerProductSpace

namespace CalderonPaper

variable {n : ℕ} [Nontrivial (Fin (n+1))]
local notation "Z" => X (n+1)
local notation "S" => standardSphere (n+1)
local notation "E" => X n
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
local notation "Q" => P × E

local instance : Fact (Module.finrank ℝ Z = (n + 1) - 1 + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]; omega⟩

namespace SignedPoissonCollar

variable {G : BallPoissonTube P (n+1)} (C : SignedPoissonCollar G)

/-- The principal coefficient has a zero radius jet if the normalized
principal square root and the physical scaled velocity do. -/
theorem velocityPrincipalSymbol_first_zero
    (A : SmoothRadialVelocity G) (χ ζ : E → ℂ) (p : ℝ → P) (x ξ : E)
    (hκ : HasDerivAt (fun r => C.coefficients.kappa ((p r,‖ξ‖⁻¹ • ξ),x)) 0 0)
    (hV : HasDerivAt (fun r => A.velocity (p r,angularPoint C.pole x)) 0 0) :
    HasDerivAt (fun r => C.velocityPrincipalSymbol A χ ζ (p r,x) ξ) 0 0 := by
  let w := angularPoint C.pole x
  let ν := ‖ξ‖⁻¹ • ξ
  let R (i j : I (n+1)) := fderiv ℝ (fun z => (polarReadout C.pole z).1)
    w (rotationVector i j w)
  have hκ' := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hκ
  have hκ'' : HasDerivAt (fun r => (C.coefficients.kappa ((p r,ν),x) : ℂ)) 0 0 := by
    simpa only [map_zero,Function.comp_def,Complex.ofRealCLM_apply,ν] using hκ'
  have hDots : HasDerivAt (fun r => ⟪w,A.velocity (p r,w)⟫_ℝ) 0 0 := by
    simpa only [map_zero,Function.comp_def,innerSL_apply_apply,w] using (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt 0 hV
  have hDot : HasDerivAt (fun r => (⟪w,A.velocity (p r,w)⟫_ℝ : ℂ)) 0 0 := by
    simpa only [map_zero,Function.comp_def,Complex.ofRealCLM_apply] using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hDots
  have hRot (i j : I (n+1)) : HasDerivAt
      (fun r => C.localRotationHigh i j (fun q => ζ q.2) (rotationCoeff A.velocity i j) (p r,x) ν) 0 0 := by
    have hD := (EuclideanSpace.proj (𝕜 := ℝ) j : Z →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hV
    have hDv : HasDerivAt (fun r => A.velocity (p r,w) j) 0 0 := by
      have hProj (z : Z) : EuclideanSpace.proj (𝕜 := ℝ) j z = z j := rfl
      simpa only [map_zero,Function.comp_def,hProj,PiLp.zero_apply,w] using hD
    have hReal : HasDerivAt (fun r => w i * A.velocity (p r,w) j) 0 0 := by
      simpa only [mul_zero] using hDv.const_mul (w i)
    have hCast : HasDerivAt (fun r => ((w i * A.velocity (p r,w) j : ℝ) : ℂ)) 0 0 := by
      simpa only [map_zero,Function.comp_def,Complex.ofRealCLM_apply] using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hReal
    have hRead := C.polarReadout_angularPoint x
    have h := (hCast.const_mul (ζ x)).const_mul
      (Complex.I * ((2*Real.pi*⟪ν,R i j⟫_ℝ : ℝ) : ℂ))
    simpa only [localRotationHigh,localRotationAmplitude,rotationCoeff,w,hRead,ν,R,mul_zero] using h
  have hSum : HasDerivAt (fun r => ∑ i, ∑ j, C.localRotationHigh i j (fun q => ζ q.2)
      (rotationCoeff A.velocity i j) (p r,x) ν) 0 0 := by
    have hInner (i : I (n+1)) : HasDerivAt (fun r => ∑ j, C.localRotationHigh i j
        (fun q => ζ q.2) (rotationCoeff A.velocity i j) (p r,x) ν) 0 0 := by
      simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hRot i j)
    simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hInner i)
  have hProd : HasDerivAt (fun r =>
      (C.coefficients.kappa ((p r,ν),x) : ℂ) * ζ x * (⟪w,A.velocity (p r,w)⟫_ℝ : ℂ)) 0 0 := by
    have h := (hκ''.mul_const (ζ x)).mul hDot
    simp only [mul_zero,zero_mul,add_zero] at h
    convert h using 1
  simpa only [velocityPrincipalSymbol,ν,w,Pi.sub_apply,mul_zero,sub_zero] using
    (((hProd.const_mul (χ x)).sub (hSum.const_mul (χ x))).const_mul (‖ξ‖ : ℂ))

end SignedPoissonCollar
end CalderonPaper
