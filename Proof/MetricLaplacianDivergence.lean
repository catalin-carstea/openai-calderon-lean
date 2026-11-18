import Proof.LocalMetricPullbackDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology Gradient Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.MetricOperator
open OAI.AnisotropicCalderon.ConnectionError

/-- The archived coordinate connection and the frozen Christoffel convention agree. -/
lemma metricChristoffel_eq_christoffel (g : MetricField) (x : X)
    (hDG : ∀ i j,DifferentiableAt ℝ (fun y => g y i j) x)
    (hPos : ∀ y,(g y).PosDef) (i j k : I) :
    MetricVolume.metricChristoffel g x i j k = christoffel g x k i j := by
  have hSwap (a b : I) : (fun y => g y a b) = (fun y => g y b a) := by
    funext y
    have hh := congrArg (fun A : Mat => A b a) (hPos y).isHermitian
    simpa only [Matrix.conjTranspose_apply,star_trivial] using hh
  rw [MetricVolume.metricChristoffel_eq g x hDG i j k]
  change (1/2:ℝ)*(∑ c,(g x)⁻¹ k c*(coordDeriv i (fun y => g y c j) x+
    coordDeriv j (fun y => g y c i) x-coordDeriv c (fun y => g y j i) x)) = christoffel g x k i j
  calc
    _ = (1/2:ℝ)*(∑ c,(g x)⁻¹ k c*(coordDeriv i (fun y => g y c j) x+
        coordDeriv j (fun y => g y i c) x-coordDeriv c (fun y => g y i j) x)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [hSwap c i,hSwap j i]
    _ = _ := by unfold christoffel; ring

/-- The frozen coordinate Laplacian depends only on the actual metric and function germs. -/
lemma laplace_congr_germ {g h : MetricField} {u v : X → ℝ} {x : X}
    (hG : g =ᶠ[𝓝 x] h) (hU : u =ᶠ[𝓝 x] v) : laplace g u x = laplace h v x := by
  have hG0 := hG.eq_of_nhds
  have hDU (a : I) : coordDeriv a u =ᶠ[𝓝 x] coordDeriv a v :=
    (hU.fderiv (𝕜:=ℝ)).mono (fun y hy => congrArg (fun L : X →L[ℝ] ℝ => L (axis a)) hy)
  have hD2U (a b : I) : coordDeriv a (coordDeriv b u) x = coordDeriv a (coordDeriv b v) x :=
    congrArg (fun L : X →L[ℝ] ℝ => L (axis a)) (hDU b).fderiv_eq
  have hDG (a b c : I) : coordDeriv c (fun y => g y a b) x = coordDeriv c (fun y => h y a b) x := by
    have hh : (fun y => g y a b) =ᶠ[𝓝 x] (fun y => h y a b) := hG.mono (fun y hy => congrArg (fun A : Mat => A a b) hy)
    exact congrArg (fun L : X →L[ℝ] ℝ => L (axis c)) hh.fderiv_eq
  have hΓ (k i j : I) : christoffel g x k i j = christoffel h x k i j := by
    simp only [christoffel,hG0,hDG]
  simp only [laplace,hG0,hΓ,hD2U,fun a => (hDU a).eq_of_nhds]

lemma source_coordinateHessian_eq (g : MetricField) (u : X → ℝ) (x : X)
    (hDG : ∀ i j,DifferentiableAt ℝ (fun y => g y i j) x)
    (hPos : ∀ y,(g y).PosDef) (hD2 : DifferentiableAt ℝ (fderiv ℝ u) x) (i j : I) :
    RadiusProfile.coordinateHessian u
      (fun a b => coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x a b) x (axis i) (axis j) =
      coordDeriv i (coordDeriv j u) x-∑ k,christoffel g x k i j*coordDeriv k u x := by
  have hCore : RadiusProfile.coordinateHessian u
      (fun a b => coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x a b) x (axis i) (axis j) =
      fderiv ℝ (fderiv ℝ u) x (axis i) (axis j)-
        ∑ k,MetricVolume.metricChristoffel g x i j k*fderiv ℝ u x (axis k) := by
    unfold RadiusProfile.coordinateHessian
    rw [MetricVolume.covector_coordinate_sum (fderiv ℝ u x)]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    unfold MetricVolume.metricChristoffel
    simp only [coordinateConnectionField_apply,
      MetricVolume.inverseMetricField_eq_matrix_inverse_of_posDef g x (hPos x),axis,MetricVolume.coordinateVector]
  rw [hCore]
  change fderiv ℝ (fderiv ℝ u) x (axis i) (axis j)-
    ∑ k,MetricVolume.metricChristoffel g x i j k*fderiv ℝ u x (axis k) =
    fderiv ℝ (coordDeriv j u) x (axis i)-∑ k,christoffel g x k i j*fderiv ℝ u x (axis k)
  rw [fderiv_coordDeriv_apply u x j hD2 (axis i)]
  simp only [metricChristoffel_eq_christoffel g x hDG hPos]

lemma global_flux_divergence_eq_density_laplace (g : MetricField) (u : X → ℝ) (x : X)
    (hDG : ∀ i j,DifferentiableAt ℝ (fun y => g y i j) x)
    (hPos : ∀ y,(g y).PosDef) (hD2 : DifferentiableAt ℝ (fderiv ℝ u) x) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x = metricDensity g x*laplace g u x := by
  have hFlux : metricDivergenceFlux g u =
      fun y => vol g y • matrixOperatorMap ((g y)⁻¹) (gradient u y) := by
    funext y
    simp only [metricDivergenceFlux,principalCoefficient,map_smul,_root_.smul_apply]
  have hDiv : coordinateFluxDivergence (metricDivergenceFlux g u) x =
      AngularPolynomial.densityWeightedDivergence (EuclideanSpace.basisFun (Fin 3) ℝ)
        (vol g) (fun y => matrixOperatorMap ((g y)⁻¹) (gradient u y)) x := by
    rw [hFlux]
    unfold coordinateFluxDivergence AngularPolynomial.densityWeightedDivergence
    simp only [EuclideanSpace.basisFun_apply,EuclideanSpace.inner_single_right,one_mul,conj_trivial,
      NormalCoordinatesFrame.coordinateVector,PiLp.smul_apply,smul_eq_mul]
  rw [hDiv,MetricVolume.densityWeightedDivergence_eq_metricHessian_trace g u x hDG hPos hD2]
  change vol g x*(∑ i,∑ j,(g x)⁻¹ i j*
    RadiusProfile.coordinateHessian u
      (fun a b => coordinateConnectionField (inverseMetricField (metricOperatorField g))
        (metricOperatorField g) x a b) x (axis i) (axis j)) = vol g x*laplace g u x
  simp only [source_coordinateHessian_eq g u x hDG hPos hD2,laplace]

/-- Divergence and the frozen Laplace–Beltrami convention agree on the actual
    local metric domain, with no global metric assumption. -/
theorem Elliptic.flux_divergence_eq_density_laplace {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (u : X → ℝ) {x : X} (hx : x ∈ Ω) (hD2 : DifferentiableAt ℝ (fderiv ℝ u) x) :
    coordinateFluxDivergence (metricDivergenceFlux g u) x = metricDensity g x*laplace g u x := by
  obtain ⟨G,hG,hPos,hGN⟩ := hg.exists_positive_global_germ hΩ hK hx
  have hGlobal := global_flux_divergence_eq_density_laplace G u x
    (fun i j => (hG i j).differentiable (by simp) x) hPos hD2
  have hDiv := coordinateFluxDivergence_congr_germ (metricDivergenceFlux_congr_germ (u:=u) (v:=u) hGN Filter.EventuallyEq.rfl)
  have hLap := laplace_congr_germ (u:=u) (v:=u) hGN Filter.EventuallyEq.rfl
  have hDensity : metricDensity G x = metricDensity g x := by
    change Real.sqrt (G x).det = Real.sqrt (g x).det
    rw [hGN.eq_of_nhds]
  exact hDiv.symm.trans (hGlobal.trans (by rw [hDensity,hLap]))

end ShrinkingSpheres
