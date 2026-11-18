import Proof.UniformActualRadialAngularAdjointData
import Proof.ActualRadialTaylorEndpoints
import Proof.DegreeCommutatorFromDistributionGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- The actual physical radial Taylor error has a uniform gained degree
    commutator on the balanced half endpoints. No endpoint or angular graph
    premise is assumed: the native elliptic and geometric producers supply it. -/
theorem uniform_actual_radial_taylor_degree_commutator {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 CA0 CD : ℝ,0 < η ∧ 0 ≤ C0 ∧ 0 ≤ CA0 ∧ 0 ≤ CD ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      ∃ S : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)),
      RealizesActualMidpointRadialError d y R ∧
      (∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ) ∧
      let P := R-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))
      ‖P‖ ≤ C0*(d.radius y)^2 ∧
      ‖radialAdjointTaylorRemainderL Ra (firstRadialCorrectionL d y) (d.radius y)‖ ≤ CA0*(d.radius y)^2 ∧
      ‖S‖ ≤ CD*(d.radius y)^2 ∧
      ∀ k l : ℕ,∀ z : harmonicSphereSubspace l,
        sphereSobolevCoefficientL (-(1/2:ℝ)) k (S (sphereSobolevSingleL (1/2:ℝ) l z)) =
          ((k:ℝ)-(l:ℝ)) • coarsePhysicalHarmonicBlock P k l z := by
  obtain ⟨η,C0,CA0,CC,CCA,hη,hC0,hCA0,hCC,hCCA,hData⟩ :=
    uniform_actual_radial_angular_adjoint_data hY hΩ hm K ρ c₀ M Cj hK hρ
  refine ⟨η,C0,CA0,(6*Real.sqrt 2)*(CC+CCA),hη,hC0,hCA0,by positivity,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨a,ha,F,R,Ra,hPoint,hCoercive,hStrong,hNormal,hReal,hPair,hRestrict,hP,hPa,hAngles⟩ :=
    hData floor hf ε hε hSmall d hd y hy
  let q := firstDensityLogCovector d y
  let r := d.radius y
  let P := R-r • (radialCorrectionCovectorL q).comp (sphereSobolevInclusionL 1 0 (by norm_num))
  have hPDef : R-d.radius y • (firstRadialCorrectionL d y).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)) = P := by
    rw [firstRadialCorrectionL_eq_covector]
  rw [hPDef] at hP hAngles
  choose C Ca hCN hCaN hCG hCaG hDual using hAngles
  obtain ⟨S,hSN,hSHigh,hSBlock⟩ := exists_half_degree_commutator_of_distribution_graphs
    (actualHighRadialTaylorL F q r) (actualLowRadialTaylorL a ha F q r) P
    (actual_radial_taylor_high_mid_compatible F R q r hRestrict)
    (actual_radial_taylor_covector_endpoints_compatible ha hCoercive F hPoint hStrong hNormal q r)
    (fun ij => C ij.1 ij.2) (fun ij => Ca ij.1 ij.2)
    (CC*r^2) (CCA*r^2) (by positivity) (by positivity)
    (fun ij => hCN ij.1 ij.2) (fun ij => hCaN ij.1 ij.2)
    (fun ij => hDual ij.1 ij.2) (fun ij => hCG ij.1 ij.2)
  refine ⟨R,Ra,S,hReal,hPair,(congrArg norm hPDef).le.trans hP,hPa,?_,?_⟩
  · exact hSN.trans_eq (by dsimp only [r];ring)
  · rw [hPDef]
    exact hSBlock

end ShrinkingSpheres
