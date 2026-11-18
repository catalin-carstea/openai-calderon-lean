import Proof.NormalFrameTaylorAdjointDerivative
import Proof.UniformNormalFrameForwardAdjointTaylorJets
import Proof.NormalFrameRotatedAdjointPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.SphereHarmonic
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace

/-- Actual common radial response, true adjoint, compatible native endpoint
    coefficient data, and their SAME gained angular commutators with true
    probability-sphere adjunction. All constants precede the admitted data. -/
theorem uniform_actual_radial_angular_adjoint_data {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C0 CA0 CC CCA : ℝ,0 < η ∧ 0 ≤ C0 ∧ 0 ≤ CA0 ∧ 0 ≤ CC ∧ 0 ≤ CCA ∧
      ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∃ a : X → Mat,∃ ha : MemLp (fun z => TauCeti.PDE.energyIntegrand (a z) 0 0) ⊤ ((volume:Measure X).restrict ballOpens),
      ∃ F : SmoothCoefficientMatrix 2,∃ R Ra : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
      (∀ z ∈ (ballOpens:Set X),coefficientMatrixField 2 F z = a z) ∧
      IsCoercive (TauCeti.PDE.energyFormH1L0 ha) ∧
      (strongDirichletOperator fixedSobolevCalculus 0 F).IsInvertible ∧
      (negativeBoundaryCoefficientMulL (normalCoefficientJet F)).IsInvertible ∧
      RealizesActualMidpointRadialError d y R ∧
      (∀ u v,⟪(R+sphereSobolevDegreeL) u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
        ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ra v⟫_ℝ) ∧
      R.comp (sphereSobolevInclusionL (3/2:ℝ) 1 (by norm_num)) =
        (sphereSobolevInclusionL (1/2:ℝ) 0 (by norm_num)).comp (actualHighRadialErrorL F) ∧
      let P := R-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))
      let Pa := radialAdjointTaylorRemainderL Ra (firstRadialCorrectionL d y) (d.radius y)
      ‖P‖ ≤ C0*(d.radius y)^2 ∧ ‖Pa‖ ≤ CA0*(d.radius y)^2 ∧
      ∀ i j : I,∃ C Ca : SphereSobolev 1 →L[ℝ] SphereSobolev 0,
        ‖C‖ ≤ CC*(d.radius y)^2 ∧ ‖Ca‖ ≤ CCA*(d.radius y)^2 ∧
        (∀ f : SphereSobolev 2,sphereSobolevRotationL 0 i j (P (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
          sphereSobolevInclusionL 0 (-1) (by norm_num)
            (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+P (sphereSobolevRotationL 2 i j f))) ∧
        (∀ f : SphereSobolev 2,sphereSobolevRotationL 0 i j (Pa (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
          sphereSobolevInclusionL 0 (-1) (by norm_num)
            (Ca (sphereSobolevInclusionL 2 1 (by norm_num) f)+Pa (sphereSobolevRotationL 2 i j f))) ∧
        ∀ u v : SphereSobolev 1,⟪C u,sphereSobolevInclusionL 1 0 (by norm_num) v⟫_ℝ =
          ⟪sphereSobolevInclusionL 1 0 (by norm_num) u,Ca v⟫_ℝ := by
  obtain ⟨η0,C0,CC,CD,CB,CA0,CAD,CCA,hη0,hC0,hCC,hCD,hCB,hCA0,hCAD,hCCA,hData⟩ :=
    uniform_normalFrame_forward_adjoint_taylor_jets hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨ηP,hηP,hPairRot⟩ := uniform_normalFrame_rotated_radial_adjoint_pairing (Y:=Y) hΩ (by omega)
    K ρ c₀ M Cj hK hρ
  refine ⟨min η0 ηP,C0,CA0,CC,CCA,lt_min hη0 hηP,hC0,hCA0,hCC,hCCA,?_⟩
  intro floor hf ε hε hSmall d hd y hy
  obtain ⟨A,hA,S,hS,hz,V,hV,hpV,hCenter,hRep,R,hR,hH,hActual,hStrong,hCoercive,hNormal,hRestrict,hJetF,hAngleF,
    W,hW,hpW,hSubW,hDa,hHa,hOne,hB,hPa,hJetA,hAngleA,hPair⟩ :=
    hData floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy
  let p0 : NormalFrameParameter := (y,(d.radius y,frameVectorLinear d.frame y))
  let Da := commonSupportRadialAdjointFamily A hA S hS hz R
  let F := commonSupportMatrixFamily 2 A hA S hS hz p0
  let a := fun z => A (p0,z)
  let ha := commonSupportEnergyMemLp A hA p0
  let P := R p0-d.radius y • (firstRadialCorrectionL d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))
  let Pa := radialAdjointTaylorRemainderL (Da p0) (firstRadialCorrectionL d y) (d.radius y)
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hyΩ := hd.2.1.center_mem hy
  have hHF : normalFrameRadialTaylorFamily d R p0 = P :=
    hd.1.normalFrameRadialTaylorFamily_actual hΩ hKpos hyΩ R
  have hHA : normalFrameRadialAdjointTaylorFamily d Da p0 = Pa :=
    hd.1.normalFrameRadialAdjointTaylorFamily_actual hΩ hKpos hyΩ Da
  refine ⟨a,ha,F,R p0,Da p0,?_,hCoercive p0 hpV,hStrong p0 hpV,hNormal p0 hpV,
    hActual y hpV,hPair y hpW,hRestrict p0 hpV,?_,?_,?_⟩
  · intro z hzB
    exact congrFun (coefficientMatrixField_commonSupportMatrixFamily 2 A hA S hS hz p0) z
  · exact (congrArg norm hHF).symm.le.trans hAngleF.1
  · exact (congrArg norm hHA).symm.le.trans hPa
  · intro i j
    let c := normalFrameRotationCurve d.frame d.radius y i j
    let C := deriv (fun t => normalFrameRadialTaylorFamily d R (c t)) 0
    let Ca := deriv (fun t => normalFrameRadialAdjointTaylorFamily d Da (c t)) 0
    have hCF := hAngleF.2 i j
    have hCA := hAngleA i j
    refine ⟨C,Ca,hCF.1,hCA.1,?_,?_,?_⟩
    · intro f
      have h := hCF.2 f
      change sphereSobolevRotationL 0 i j
          (normalFrameRadialTaylorFamily d R p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (C (sphereSobolevInclusionL 2 1 (by norm_num) f)+
            normalFrameRadialTaylorFamily d R p0 (sphereSobolevRotationL 2 i j f)) at h
      rw [hHF] at h
      exact h
    · intro f
      have h := hCA.2 f
      change sphereSobolevRotationL 0 i j
          (normalFrameRadialAdjointTaylorFamily d Da p0 (sphereSobolevInclusionL 2 1 (by norm_num) f)) =
        sphereSobolevInclusionL 0 (-1) (by norm_num)
          (Ca (sphereSobolevInclusionL 2 1 (by norm_num) f)+
            normalFrameRadialAdjointTaylorFamily d Da p0 (sphereSobolevRotationL 2 i j f)) at h
      rw [hHA] at h
      exact h
    · have hCurve := hasDerivAt_normalFrameRotationCurve d.frame d.radius y i j
      have h0V : c 0 ∈ V := by simpa only [c,normalFrameRotationCurve_zero] using hpV
      have h0W : c 0 ∈ W := by simpa only [c,normalFrameRotationCurve_zero] using hpW
      have hFd : DifferentiableAt ℝ (fun t => normalFrameRadialTaylorFamily d R (c t)) 0 :=
        ((hH.contDiffAt (hV.mem_nhds h0V)).differentiableAt (by simp)).comp 0 hCurve.differentiableAt
      have hAd : DifferentiableAt ℝ (fun t => normalFrameRadialAdjointTaylorFamily d Da (c t)) 0 :=
        ((hHa.contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)).comp 0 hCurve.differentiableAt
      have hNear : ∀ᶠ t : ℝ in 𝓝 0,c t ∈ W := hCurve.continuousAt.eventually (hW.mem_nhds h0W)
      apply normalFrame_taylor_curve_derivative_adjoint d R Da c hFd hAd
      filter_upwards [hNear] with t ht
      exact hPairRot floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy A hA S hS hz
        V hpV hRep R hCoercive hStrong hNormal hRestrict i j t (hSubW ht)

end ShrinkingSpheres
