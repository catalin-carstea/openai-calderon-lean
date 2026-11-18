import Proof.Archive.MixedRadialJetCalculus
import Proof.Archive.FiniteDimensionalLocalSmoothExtension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped ContDiff Topology
open OAI.AnisotropicCalderon.ConnectionError
namespace ShrinkingSpheres

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_global_smooth_germ_of_open (F : P → V) {U : Set P}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {x : P} (hx : x ∈ U) :
    ∃ G : P → V, ContDiff ℝ ∞ G ∧ G =ᶠ[𝓝 x] F := by
  obtain ⟨G,hG,_,he⟩ :=
    OAI.AnisotropicCalderon.DirichletFamily.exists_contDiff_eq_near_compact_of_contDiffOn
      ({x}:Set P) U (isCompact_singleton) hU (by simpa) F hF
  exact ⟨G,hG,he x (by simp)⟩

theorem parameterJetField_congr_nhds (n : ℕ) {F G : P × ℝ → V} {x : P × ℝ}
    (he : F =ᶠ[𝓝 x] G) :
    parameterJetField n F =ᶠ[𝓝 x] parameterJetField n G := by
  filter_upwards [he.iteratedFDeriv ℝ n] with q hq
  exact congrArg (fun A => A.compContinuousLinearMap
    (fun _ : Fin n => ContinuousLinearMap.inl ℝ P ℝ)) hq

theorem radialFirstDerivative_congr_nhds {F G : P × ℝ → V} {x : P × ℝ}
    (he : F =ᶠ[𝓝 x] G) :
    radialFirstDerivative F =ᶠ[𝓝 x] radialFirstDerivative G := by
  filter_upwards [he.fderiv (𝕜:=ℝ)] with q hq
  exact congrArg (fun A : (P × ℝ) →L[ℝ] V => A (0,1)) hq

theorem parameterJetField_eq_iteratedFDeriv_of_open (n : ℕ) (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) :
    parameterJetField n F (p,t) = iteratedFDeriv ℝ n (fun q => F (q,t)) p := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hSlice : (fun q => G (q,t)) =ᶠ[𝓝 p] (fun q => F (q,t)) :=
    he.comp_tendsto ((continuousAt_id.prodMk continuousAt_const).tendsto)
  rw [← (parameterJetField_congr_nhds n he).eq_of_nhds,
    parameterJetField_eq_iteratedFDeriv n G hG p t]
  exact (hSlice.iteratedFDeriv ℝ n).eq_of_nhds

theorem contDiffAt_parameterJetField_of_open (n : ℕ) (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    {x : P × ℝ} (hx : x ∈ U) :
    ContDiffAt ℝ ∞ (parameterJetField n F) x := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hx
  exact (contDiff_parameterJetField n G hG).contDiffAt.congr_of_eventuallyEq
    (parameterJetField_congr_nhds n he).symm

/-- Mixed time/parameter differentiation is local on an explicit smooth open
    domain. No global extension contributes any quantitative bound. -/
theorem hasDerivAt_parameterJetField_of_open (n : ℕ) (F : P × ℝ → V)
    {U : Set (P × ℝ)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (p : P) (t : ℝ) (hp : (p,t) ∈ U) :
    HasDerivAt (fun s => parameterJetField n F (p,s))
      (iteratedFDeriv ℝ n (fun q => radialFirstDerivative F (q,t)) p) t := by
  obtain ⟨G,hG,he⟩ := exists_global_smooth_germ_of_open F hU hF hp
  have hJ := parameterJetField_congr_nhds n he
  have hSlice : (fun s => parameterJetField n G (p,s)) =ᶠ[𝓝 t]
      (fun s => parameterJetField n F (p,s)) :=
    hJ.comp_tendsto ((continuousAt_const.prodMk continuousAt_id).tendsto)
  have hRad : (fun q => radialFirstDerivative G (q,t)) =ᶠ[𝓝 p]
      (fun q => radialFirstDerivative F (q,t)) :=
    (radialFirstDerivative_congr_nhds he).comp_tendsto
      ((continuousAt_id.prodMk continuousAt_const).tendsto)
  have hd := hasDerivAt_radialSlice (parameterJetField n G)
    (contDiff_parameterJetField n G hG) p t
  rw [radialFirstDerivative_parameterJetField n G hG,
    parameterJetField_eq_iteratedFDeriv n _ (contDiff_radialFirstDerivative G hG) p t,
    (hRad.iteratedFDeriv ℝ n).eq_of_nhds] at hd
  exact hd.congr_of_eventuallyEq hSlice.symm

end ShrinkingSpheres
