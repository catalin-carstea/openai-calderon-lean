import Proof.PositiveMetricExtension
import Proof.Archive.MetricPullbackDivergence
import Proof.Archive.FiniteDimensionalLocalSmoothExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 15
open Set Filter Function
open scoped ContDiff Gradient Topology Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.MetricOperator
open OAI.AnisotropicCalderon.ConnectionError

lemma metricDivergenceFlux_congr_germ {g h : MetricField} {u v : X → ℝ} {x : X}
    (hg : g =ᶠ[𝓝 x] h) (hu : u =ᶠ[𝓝 x] v) :
    metricDivergenceFlux g u =ᶠ[𝓝 x] metricDivergenceFlux h v := by
  filter_upwards [hg,hu.gradient] with y hy hDy
  change matrixOperatorMap (Real.sqrt (g y).det • (g y)⁻¹) (gradient u y) =
    matrixOperatorMap (Real.sqrt (h y).det • (h y)⁻¹) (gradient v y)
  rw [hy,hDy]

lemma coordinateFluxDivergence_congr_germ {Z W : X → X} {x : X} (hZ : Z =ᶠ[𝓝 x] W) :
    coordinateFluxDivergence Z x = coordinateFluxDivergence W x := by
  unfold coordinateFluxDivergence
  apply Finset.sum_congr rfl
  intro i hi
  have hEq : (fun y => Z y i) =ᶠ[𝓝 x] (fun y => W y i) := hZ.mono (fun y hy => congrArg (fun z : X => z i) hy)
  exact congrArg (fun D : X →L[ℝ] ℝ => D (NormalCoordinatesFrame.coordinateVector i)) hEq.fderiv_eq

/-- The supplied global Piola formula applies to the actual local metric and local
    smooth chart, using genuine smooth germs without extending the mathematical domain. -/
theorem Elliptic.pullback_flux_divergence_local {Ω : Set X} (hΩ : IsOpen Ω)
    {K : ℝ} {g : MetricField} (hg : Elliptic Ω K g) (hK : 0 < K)
    (F : X → X) (u : X → ℝ) (S T : Set X) (hS : IsOpen S) (hT : IsOpen T)
    (hF : ContDiffOn ℝ ∞ F S) (hu : ContDiffOn ℝ ∞ u T)
    (x : X) (hx : x ∈ S) (hFx : F x ∈ T) (hFxΩ : F x ∈ Ω)
    (hJ : IsUnit (coordinateJacobianMatrix F x).det) :
    coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric g F) (u ∘ F)) x =
      |(coordinateJacobianMatrix F x).det| *coordinateFluxDivergence (metricDivergenceFlux g u) (F x) := by
  obtain ⟨G,hG,hGpos,hGN⟩ := hg.exists_positive_global_germ hΩ hK hFxΩ
  have hxS : ({x} : Set X) ⊆ S := by simpa only [singleton_subset_iff] using hx
  have hxT : ({F x} : Set X) ⊆ T := by simpa only [singleton_subset_iff] using hFx
  obtain ⟨Fhat,hFhat,_,hNearF⟩ := DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
    ({x} : Set X) S isCompact_singleton hS hxS F hF
  obtain ⟨uhat,huhat,_,hNearu⟩ := DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
    ({F x} : Set X) T isCompact_singleton hT hxT u hu
  have hFN : Fhat =ᶠ[𝓝 x] F := hNearF x (mem_singleton x)
  have huN : uhat =ᶠ[𝓝 (F x)] u := hNearu (F x) (mem_singleton (F x))
  have hFvalue : Fhat x = F x := hFN.eq_of_nhds
  have hPath : Tendsto Fhat (𝓝 x) (𝓝 (F x)) := by
    rw [← hFvalue]
    exact hFhat.continuous.continuousAt.tendsto
  have hComp : uhat ∘ Fhat =ᶠ[𝓝 x] u ∘ F :=
    (huN.comp_tendsto hPath).trans (hFN.mono (fun z hz => congrArg u hz))
  have hPB : pullbackMetric G Fhat =ᶠ[𝓝 x] pullbackMetric g F := by
    filter_upwards [hFN,hFN.fderiv (𝕜:=ℝ),hGN.comp_tendsto hPath] with z hz hDz hGz
    dsimp only [Function.comp_def] at hGz
    rw [hz] at hGz
    simp only [pullbackMetric,metricOperatorField,hDz,hGz,hz]
  have hFlux := metricDivergenceFlux_congr_germ hPB hComp
  have hDiv := coordinateFluxDivergence_congr_germ hFlux
  have hJac : coordinateJacobianMatrix Fhat x = coordinateJacobianMatrix F x := by
    rw [coordinateJacobianMatrix_eq_operatorMatrixMap,coordinateJacobianMatrix_eq_operatorMatrixMap,hFN.fderiv_eq]
  have hJhat : IsUnit (coordinateJacobianMatrix Fhat x).det := by rw [hJac]; exact hJ
  have hRHS := coordinateFluxDivergence_congr_germ (metricDivergenceFlux_congr_germ hGN huN)
  calc
    _ = coordinateFluxDivergence (metricDivergenceFlux (pullbackMetric G Fhat) (uhat ∘ Fhat)) x := hDiv.symm
    _ = |(coordinateJacobianMatrix Fhat x).det| *coordinateFluxDivergence (metricDivergenceFlux G uhat) (Fhat x) :=
      coordinateFluxDivergence_metricDivergenceFlux_pullbackMetric G hG hGpos Fhat uhat hFhat huhat x hJhat
    _ = _ := by rw [hJac,hFvalue,hRHS]

end ShrinkingSpheres
