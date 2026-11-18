import Proof.SpherePartialRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

/-- A genuine physical product output has exactly the squared norm of
its actual real and imaginary sphere-L2 components. Only the representative
equalities on the original domain are required. -/
lemma norm_product_output_of_fibre_components {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y)
    (P : Lp ℂ 2 ((outputBaseMeasure Y g).prod sphereProbability))
    (F : X × UnitSphere → ℂ) (hPF : P =ᵐ[(outputBaseMeasure Y g).prod sphereProbability] F)
    (U V : X → SphereL2)
    (hRe : ∀ y ∈ Y,U y =ᵐ[sphereProbability] (fun v => (F (y,v)).re))
    (hIm : ∀ y ∈ Y,V y =ᵐ[sphereProbability] (fun v => (F (y,v)).im)) :
    ‖P‖^2=∫ y in Y,metricDensity g y*(‖U y‖^2+‖V y‖^2) := by
  have hFm : MemLp F 2 ((outputBaseMeasure Y g).prod sphereProbability) := (Lp.memLp P).ae_eq hPF
  have hOutput : hFm.toLp F=P := by
    apply Lp.ext
    exact hFm.coeFn_toLp.trans hPF.symm
  rw [←hOutput,norm_sq_output_product hY hρ F hFm]
  apply setIntegral_congr_fun hY.measurableSet
  intro y hy
  exact congrArg (fun z => metricDensity g y*z)
    (integral_complex_norm_sq_components (fun v => F (y,v)) (U y) (V y) (hRe y hy) (hIm y hy))

lemma norm_product_output_sub_of_fibre_components {Y : Set X} (hY : IsOpen Y) {g : MetricField}
    (hρ : ContinuousOn (metricDensity g) Y)
    (P Q : Lp ℂ 2 ((outputBaseMeasure Y g).prod sphereProbability))
    (F G : X × UnitSphere → ℂ)
    (hPF : P =ᵐ[(outputBaseMeasure Y g).prod sphereProbability] F)
    (hQG : Q =ᵐ[(outputBaseMeasure Y g).prod sphereProbability] G)
    (U V U' V' : X → SphereL2)
    (hRe : ∀ y ∈ Y,U y =ᵐ[sphereProbability] (fun v => (F (y,v)).re))
    (hIm : ∀ y ∈ Y,V y =ᵐ[sphereProbability] (fun v => (F (y,v)).im))
    (hRe' : ∀ y ∈ Y,U' y =ᵐ[sphereProbability] (fun v => (G (y,v)).re))
    (hIm' : ∀ y ∈ Y,V' y =ᵐ[sphereProbability] (fun v => (G (y,v)).im)) :
    ‖P-Q‖^2=∫ y in Y,metricDensity g y*(‖U y-U' y‖^2+‖V y-V' y‖^2) := by
  have hFG : P-Q =ᵐ[(outputBaseMeasure Y g).prod sphereProbability] (fun z => F z-G z) := by
    filter_upwards [Lp.coeFn_sub P Q,hPF,hQG] with z hz hp hq
    simp only [Pi.sub_apply] at hz
    exact hz.trans (congrArg₂ Sub.sub hp hq)
  apply norm_product_output_of_fibre_components hY hρ (P-Q) (fun z => F z-G z) hFG
    (fun y => U y-U' y) (fun y => V y-V' y)
  · intro y hy
    filter_upwards [Lp.coeFn_sub (U y) (U' y),hRe y hy,hRe' y hy] with v hv hr hr'
    simp only [Pi.sub_apply] at hv
    rw [Complex.sub_re]
    exact hv.trans (congrArg₂ (fun a b : ℝ => a-b) hr hr')
  · intro y hy
    filter_upwards [Lp.coeFn_sub (V y) (V' y),hIm y hy,hIm' y hy] with v hv hr hr'
    simp only [Pi.sub_apply] at hv
    rw [Complex.sub_im]
    exact hv.trans (congrArg₂ (fun a b : ℝ => a-b) hr hr')

end ShrinkingSpheres
