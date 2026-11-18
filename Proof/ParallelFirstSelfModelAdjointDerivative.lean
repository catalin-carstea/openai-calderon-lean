import Proof.ParallelFirstSelfModelAdjointJet
import Proof.StrongHalfCovariantAdjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres.ParallelEnergy
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The transpose of the SAME model strong-half jet is the LITERAL
covariant derivative of ANY coherent selected model adjoint HIGH endpoint. -/
lemma principal_model_adjoint_covariant_eq_first_jet
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    {d : Data} (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (b i : I) {y : X} (hy : y ∈ Y)
    (AH : X → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ))
    (hLS : ContDiffAt ℝ ∞ (fun x => principalModelCoordinateHalfL d x b) y)
    (hForward : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp
      (principalModelCoordinateHigherL d y b)=
      (principalModelCoordinateHalfL d y b).comp (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)))
    (hAH : (sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)).comp (AH y)=
      (principalModelCoordinateHalfL d y b).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num))) :
    halfOperatorCovariantDerivativeL d (fun x => (principalModelCoordinateHalfL d x b).adjoint) AH y (axis i)=
      (principalModelCoordinateFirstHalfJet d b i y).adjoint.comp
        (sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)) := by
  have hCS := (hd.principalModelCoordinateCoarse_smooth hY hΩ hK b i).1
  have hLow : ∀ᶠ x in 𝓝 y,(sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (principalModelCoordinateCoarseL d b x)=
      (principalModelCoordinateHalfL d x b).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
    filter_upwards [hY.mem_nhds hy] with x hx
    exact hd.principalModelCoordinate_coarse_low_compatible hY hx b
  have hStrong := halfOperatorCovariantDerivativeL_eq_strong_extension
    (principalModelCoordinateCoarseL d b) (fun x => principalModelCoordinateHalfL d x b)
    (fun x => principalModelCoordinateHigherL d x b)
    (principalModelCoordinateFirstCoarseJet d b i y) (principalModelCoordinateFirstHalfJet d b i y)
    ((hCS.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    (hLS.differentiableAt (by simp)) hLow (principalModelCoordinate_coarse_high_compatible d y b)
    (hd.principalModelCoordinate_coarse_covariant_graphs hY hΩ hK hy b i i).1
    (principalModelCoordinateFirstHalfJet_coarse d b i y)
  exact half_covariant_adjoint_strong_extension d (fun x => principalModelCoordinateHalfL d x b)
    (fun x => principalModelCoordinateHigherL d x b) AH hLS (axis i) hForward hAH
    (principalModelCoordinateFirstHalfJet d b i y) hStrong

end ShrinkingSpheres.ParallelEnergy
