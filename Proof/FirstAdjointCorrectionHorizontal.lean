import Proof.CorrectionCovariantAlgebra
import Proof.CoordinateFrameCommutator
import Proof.CanonicalRadialCommutator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open OAI.AnisotropicCalderon.SphereHarmonic

/-- The actual canonical first correction as one operator family. -/
def firstFrameAdjointCorrectionL (d : Data) (y : X) (j : I) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (firstRadialCorrectionL d y).adjoint.comp (coordinateMultiplierSobolevL 0 j)+
    scaledFrameLogRadius d.radius d.frame j y • (firstRadialCorrectionL d y).adjoint

theorem firstFrameAdjointCorrectionL_zero (d : Data) (y : X) (j : I) :
    firstAdjointCorrectionSobolevL 0 (firstDensityLogCovector d y)
      (scaledFrameLogRadius d.radius d.frame j y) j = firstFrameAdjointCorrectionL d y j := by
  simp only [firstAdjointCorrectionSobolevL,radialCorrectionAdjointSobolevL_zero,
    firstFrameAdjointCorrectionL,firstRadialCorrectionL_eq_covector]

theorem firstFrameAdjointCorrectionL_actual (Q : SmoothCoefficientJets 2)
    (hQ : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (d : Data) (y : X) (j : I) :
    firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q j) (firstRadialCorrectionL d y)
      (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) =
        firstFrameAdjointCorrectionL d y j := by
  have hB := congrArg (fun B : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    firstBoundaryAdjointCorrectionL (coordinateBoundaryCoefficients Q j) B (d.radius y)
      (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j))) (firstRadialCorrectionL_eq_covector d y)
  exact hB.trans ((firstBoundaryAdjointCorrectionL_eq_sobolev_zero Q hQ (firstDensityLogCovector d y)
    (d.radius y) (fderiv ℝ (fun x => Real.log (d.radius x)) y (d.frame y j)) j).trans
      (firstFrameAdjointCorrectionL_zero d y j))

theorem firstFrameAdjointCorrectionL_coarse (d : Data) (y : X) (j : I) (u : SphereSobolev 1) :
    sphereSobolevInclusionL 1 0 (by norm_num) (firstFrameAdjointCorrectionSobolevL d y j u) =
      firstFrameAdjointCorrectionL d y j (sphereSobolevInclusionL 1 0 (by norm_num) u) :=
  (firstAdjointCorrectionSobolevL_coarse (firstDensityLogCovector d y)
    (scaledFrameLogRadius d.radius d.frame j y) j u).trans
      (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
        T (sphereSobolevInclusionL 1 0 (by norm_num) u)) (firstFrameAdjointCorrectionL_zero d y j))

theorem degree_firstFrameAdjointCorrection_commutator (d : Data) (y : X) (j : I) :
    sphereSobolevDegreeL.comp (firstFrameAdjointCorrectionSobolevL d y j)-
      (firstFrameAdjointCorrectionL d y j).comp sphereSobolevDegreeL =
        (firstAdjointCorrectionDegreeCommutatorL (firstDensityLogCovector d y)
          (scaledFrameLogRadius d.radius d.frame j y) j).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  have h := degree_firstAdjointCorrection_commutator (firstDensityLogCovector d y)
    (scaledFrameLogRadius d.radius d.frame j y) j
  have hReplace := congrArg (fun Q0 : SphereSobolev 0 →L[ℝ] SphereSobolev 0 =>
    sphereSobolevDegreeL.comp (firstFrameAdjointCorrectionSobolevL d y j)-Q0.comp sphereSobolevDegreeL)
      (firstFrameAdjointCorrectionL_zero d y j)
  exact hReplace.symm.trans h

theorem Admissible.contDiffOn_firstFrameAdjointCorrectionL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (j : I) :
    ContDiffOn ℝ ∞ (fun y => firstFrameAdjointCorrectionL d y j) Y := by
  have hSub : Y ⊆ Ω := fun y hy => hd.2.1.center_mem hy
  let Adj : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ (fun y => (firstRadialCorrectionL d y).adjoint) Y :=
    Adj.contDiff.comp_contDiffOn ((hd.1.firstRadialCorrectionL_smooth hΩ hK).mono hSub)
  have ht := contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun y hy => (hd.2.2.2.2.1.2 y hy).1.ne')
    (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub) j
  exact (hB.clm_comp contDiffOn_const).add (ht.smul hB)

theorem Admissible.fderiv_firstFrameAdjointCorrectionL {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a : X) (j : I) :
    fderiv ℝ (fun x => firstFrameAdjointCorrectionL d x j) y a =
      (fderiv ℝ (fun x => (firstRadialCorrectionL d x).adjoint) y a).comp (coordinateMultiplierSobolevL 0 j)+
      scaledFrameLogRadius d.radius d.frame j y • fderiv ℝ (fun x => (firstRadialCorrectionL d x).adjoint) y a+
      fderiv ℝ (scaledFrameLogRadius d.radius d.frame j) y a • (firstRadialCorrectionL d y).adjoint := by
  have hSub : Y ⊆ Ω := fun x hx => hd.2.1.center_mem hx
  let Adj : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) →L[ℝ] (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
    (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
      (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap
  have hB : ContDiffOn ℝ ∞ (fun x => (firstRadialCorrectionL d x).adjoint) Y :=
    Adj.contDiff.comp_contDiffOn ((hd.1.firstRadialCorrectionL_smooth hΩ hK).mono hSub)
  have ht := contDiffOn_scaledFrameLogRadius hY hd.2.2.2.2.1.1
    (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')
    (fun i => (hd.1.2.2.2.2.2.2.1 i).mono hSub) j
  exact fderiv_operator_comp_add_smul (fun x => (firstRadialCorrectionL d x).adjoint)
    (scaledFrameLogRadius d.radius d.frame j) (coordinateMultiplierSobolevL 0 j) y a
    ((hB.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))
    ((ht.contDiffAt (hY.mem_nhds hy)).differentiableAt (by simp))

def firstFrameAdjointHorizontalCommutatorL (d : Data) (y a : X) (j : I) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  (fderiv ℝ (fun x => firstFrameAdjointCorrectionL d x j) y a).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
    (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a)).comp
      (firstFrameAdjointCorrectionSobolevL d y j)-
    (firstFrameAdjointCorrectionL d y j).comp (angularConnectionL (frameConnectionCoefficient d.γ d.frame y a))-
    (∑ k : I,frameConnectionCoefficient d.γ d.frame y a j k • firstFrameAdjointCorrectionL d y k).comp
      (sphereSobolevInclusionL 1 0 (by norm_num))

def firstFrameAdjointCovariantJetL (d : Data) (y a : X) (j : I) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (firstRadialCoefficientCovariantJetL d y a).adjoint.comp (coordinateMultiplierSobolevL 0 j)+
    scaledFrameLogRadius d.radius d.frame j y • (firstRadialCoefficientCovariantJetL d y a).adjoint+
    scaledFrameLogRadiusCovariant d.γ d.radius d.frame y a j • (firstRadialCorrectionL d y).adjoint

theorem Admissible.firstFrameAdjointHorizontalCommutatorL_eq {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    {y : X} (hy : y ∈ Y) (a : X) (j : I) :
    firstFrameAdjointHorizontalCommutatorL d y a j =
      (firstFrameAdjointCovariantJetL d y a j).comp (sphereSobolevInclusionL 1 0 (by norm_num)) := by
  apply ContinuousLinearMap.ext
  intro u
  let I0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let A := frameConnectionCoefficient d.γ d.frame y a
  let L := angularConnectionL A
  let B0 := (firstRadialCorrectionL d y).adjoint
  let B1 := radialCorrectionAdjointSobolevL 1 (firstDensityLogCovector d y)
  let DB := fderiv ℝ (fun x => (firstRadialCorrectionL d x).adjoint) y a
  let J := (firstRadialCoefficientCovariantJetL d y a).adjoint
  let M0 := coordinateMultiplierSobolevL 0
  let M1 := coordinateMultiplierSobolevL 1
  let t : I → ℝ := fun k => scaledFrameLogRadius d.radius d.frame k y
  let dt := fderiv ℝ (scaledFrameLogRadius d.radius d.frame j) y a
  have hSkew : ∀ i j,A i j = -A j i :=
    frameConnection_skew hΩ hd.1.1 hK d.frame hd.1.2.2.2.2.2.2.1 hd.1.2.2.2.2.2.2.2
      (hd.2.1.center_mem hy) a
  have hMI (v : SphereSobolev 1) : I0 (M1 j v) = M0 j (I0 v) :=
    sphereSobolevInclusionL_linearCoordinateMul sphereFischerInner orthogonalSphereHarmonics
      denseSphereHarmonics 1 0 (by norm_num) (axis j) v
  have hB (v : SphereSobolev 1) : DB (I0 v)+L (B1 v)-B0 (L v) = J (I0 v) := by
    have h := congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v)
      (hd.1.firstRadialAdjointHorizontalCommutatorL_eq hΩ hK (hd.2.1.center_mem hy) a)
    change DB (I0 v)+(L (B1 v)-B0 (L v)) = J (I0 v) at h
    exact (show DB (I0 v)+L (B1 v)-B0 (L v) = DB (I0 v)+(L (B1 v)-B0 (L v)) by abel).trans h
  have hM (v : SphereSobolev 1) : L (M1 j v)-M0 j (L v) = (∑ k : I,A j k • M0 k) (I0 v) :=
    congrArg (fun T : SphereSobolev 1 →L[ℝ] SphereSobolev 0 => T v)
      (angularConnection_coordinateMultiplier_commutator A hSkew j)
  have hAlg := correction_covariant_algebra I0 L B1 B0 DB J M1 M0 A t j dt hMI hB hM u
  have hDerivative := hd.fderiv_firstFrameAdjointCorrectionL hY hΩ hK hy a j
  simp only [firstFrameAdjointHorizontalCommutatorL,ContinuousLinearMap.comp_apply,
    _root_.add_apply,_root_.sub_apply]
  rw [hDerivative]
  simpa only [firstFrameAdjointCovariantJetL,
    firstFrameAdjointCorrectionL,firstFrameAdjointCorrectionSobolevL,
    firstAdjointCorrectionSobolevL,scaledFrameLogRadiusCovariant,scaledFrameLogRadius,
    _root_.sum_apply,_root_.add_apply,_root_.sub_apply,_root_.smul_apply,ContinuousLinearMap.comp_apply,
    map_add,map_smul,I0,A,L,B0,B1,DB,J,M0,M1,t,dt] using hAlg

def firstRadialCovariantBudget (K M1 M2 : ℝ) : ℝ :=
  6*K*((K*|M2|+K^2*|M1|^2)+(K*|M1|)*(243*K*|M1|))

def firstFrameAdjointCovariantBudget (K M1 M2 C2 : ℝ) : ℝ :=
  2*firstRadialCovariantBudget K M1 M2*K+(|C2|+1)*(6*K^2*|M1|)

theorem Admissible.norm_firstFrameAdjointCorrectionL_le {Y Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (j : I) :
    ‖firstFrameAdjointCorrectionL d y j‖ ≤ 12*K^2*|M ⟨1,by omega⟩| := by
  have hQ := hd.1.norm_firstDensityLogCovector_le hΩ hK hm (hd.2.1.center_mem hy)
  have hT : |scaledFrameLogRadius d.radius d.frame j y| ≤ 1 :=
    hd.scaled_frame_logRadius_bound hf hε hε1 hy j
  calc
    _ = ‖firstAdjointCorrectionSobolevL 0 (firstDensityLogCovector d y)
        (scaledFrameLogRadius d.radius d.frame j y) j‖ :=
      congrArg norm (firstFrameAdjointCorrectionL_zero d y j).symm
    _ ≤ 6*‖firstDensityLogCovector d y‖*(1+|scaledFrameLogRadius d.radius d.frame j y|) :=
      norm_firstAdjointCorrectionSobolevL_zero_le _ _ j
    _ ≤ 6*(K^2*|M ⟨1,by omega⟩|)*(1+1) := by gcongr
    _ = _ := by ring

theorem Admissible.norm_firstFrameAdjointCovariantJetL_le {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i j : I) :
    ‖firstFrameAdjointCovariantJetL d y (d.frame y i) j‖ ≤
      firstFrameAdjointCovariantBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let CB := firstRadialCovariantBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩)
  have hCB : 0 ≤ CB := by dsimp only [CB,firstRadialCovariantBudget];positivity
  let J := (firstRadialCoefficientCovariantJetL d y (d.frame y i)).adjoint
  let B := (firstRadialCorrectionL d y).adjoint
  let t := scaledFrameLogRadius d.radius d.frame j y
  let dt := scaledFrameLogRadiusCovariant d.γ d.radius d.frame y (d.frame y i) j
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hEop := hd.1.1.norm_frameVectorLinear_le hK (hd.2.1.center_mem hy) d.frame hFrame
  have hE : ‖d.frame y i‖ ≤ K := by
    have h := (frameVectorLinear d.frame y).le_opNorm (axis i)
    rw [frameVectorLinear_apply,frameVector_axis,norm_axis,mul_one] at h
    exact h.trans hEop
  have hJ : ‖J‖ ≤ CB*K := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    have h := hd.1.norm_firstRadialCoefficientCovariantJetL_le hΩ hK hm
      (hd.2.1.center_mem hy) (d.frame y i)
    change ‖firstRadialCoefficientCovariantJetL d y (d.frame y i)‖ ≤ CB*‖d.frame y i‖ at h
    exact h.trans (mul_le_mul_of_nonneg_left hE hCB)
  have hB : ‖B‖ ≤ 6*K^2*|M ⟨1,by omega⟩| := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hd.1.norm_firstRadialCorrectionL_le hΩ hK hm (hd.2.1.center_mem hy)
  have ht : |t| ≤ 1 := hd.scaled_frame_logRadius_bound hf hε hε1 hy j
  have hdt : |dt| ≤ |Cj 2|+1 := hd.scaledFrameLogRadiusCovariant_frame_le hY hε1 hy i j
  have hM := norm_coordinateMultiplierSobolevL_zero_le j
  change ‖J.comp (coordinateMultiplierSobolevL 0 j)+t • J+dt • B‖ ≤ _
  calc
    _ ≤ (‖J.comp (coordinateMultiplierSobolevL 0 j)‖+‖t • J‖)+‖dt • B‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖J‖*‖coordinateMultiplierSobolevL 0 j‖+|t| *‖J‖)+|dt| *‖B‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
      exact add_le_add (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) le_rfl) le_rfl
    _ ≤ (CB*K*1+1*(CB*K))+(|Cj 2|+1)*(6*K^2*|M ⟨1,by omega⟩|) := by gcongr
    _ = _ := by dsimp only [firstFrameAdjointCovariantBudget,CB];ring

/-- A shared bounded L2 producer for the actual first-correction horizontal
    commutator in every frame direction, with no frame-derivative hypothesis. -/
theorem Admissible.exists_bounded_firstFrameAdjointHorizontalCommutator
    {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K)
    (hf : 1 ≤ floor) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (i j : I) :
    ∃ J : SphereSobolev 0 →L[ℝ] SphereSobolev 0,
      ‖J‖ ≤ firstFrameAdjointCovariantBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) ∧
      firstFrameAdjointHorizontalCommutatorL d y (d.frame y i) j =
        J.comp (sphereSobolevInclusionL 1 0 (by norm_num)) :=
  ⟨firstFrameAdjointCovariantJetL d y (d.frame y i) j,
    hd.norm_firstFrameAdjointCovariantJetL_le hY hΩ hm hK hf hε hε1 hy i j,
    hd.firstFrameAdjointHorizontalCommutatorL_eq hY hΩ (zero_lt_one.trans_le hK) hy (d.frame y i) j⟩

end ShrinkingSpheres
