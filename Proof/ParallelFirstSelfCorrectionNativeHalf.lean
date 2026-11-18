import Proof.UniformNativeFirstCorrectionThreeJets
import Proof.BoundedCorrectionStrongHalf

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

/-- Bounded L2 radial adjoint, before the H1 input restriction. -/
def correctionRadialBoundedMapL : (X →L[ℝ] ℝ) →L[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0) :=
  (ContinuousLinearMap.adjoint : (SphereSobolev 0 →L[ℝ] SphereSobolev 0) ≃ₗᵢ[ℝ]
    (SphereSobolev 0 →L[ℝ] SphereSobolev 0)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      radialCorrectionCovectorL

def correctionBoundedPacket (q : X →L[ℝ] ℝ) (c : I → ℝ) (t : ℝ) :
    SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  (correctionRadialBoundedMapL q).comp (∑ j : I,c j • coordinateMultiplierSobolevL 0 j)+
    t • correctionRadialBoundedMapL q

lemma correctionBoundedPacket_coarse (q : X →L[ℝ] ℝ) (c : I → ℝ) (t : ℝ) :
    (correctionBoundedPacket q c t).comp (sphereSobolevInclusionL 1 0 (by norm_num))=
      (firstRadialAdjointOperatorMapL q).comp (∑ j : I,c j • coordinateMultiplierSobolevL 1 j)+
        t • firstRadialAdjointOperatorMapL q := by
  have hCoordinate (u : SphereSobolev 1) :
      (∑ j : I,c j • coordinateMultiplierSobolevL 0 j)
          (sphereSobolevInclusionL 1 0 (by norm_num) u)=
        sphereSobolevInclusionL 1 0 (by norm_num)
          ((∑ j : I,c j • coordinateMultiplierSobolevL 1 j) u) := by
    simp only [_root_.sum_apply,_root_.smul_apply,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    exact congrArg (fun z : SphereSobolev 0 => c j • z)
      (by rw [coordinateMultiplierSobolevL_coarse,coordinateMultiplierSobolevL_zero])
  apply ContinuousLinearMap.ext
  intro u
  change (radialCorrectionCovectorL q).adjoint
      ((∑ j : I,c j • coordinateMultiplierSobolevL 0 j)
        (sphereSobolevInclusionL 1 0 (by norm_num) u))+
      t • (radialCorrectionCovectorL q).adjoint (sphereSobolevInclusionL 1 0 (by norm_num) u)=
    (radialCorrectionCovectorL q).adjoint
      (sphereSobolevInclusionL 1 0 (by norm_num) ((∑ j : I,c j • coordinateMultiplierSobolevL 1 j) u))+
      t • (radialCorrectionCovectorL q).adjoint (sphereSobolevInclusionL 1 0 (by norm_num) u)
  exact congrArg (fun z : SphereSobolev 0 =>
    (radialCorrectionCovectorL q).adjoint z+
      t • (radialCorrectionCovectorL q).adjoint (sphereSobolevInclusionL 1 0 (by norm_num) u))
    (hCoordinate u)

/-- One native bounded family and its literal strong-half extension. -/
def correctionNativeBoundedFamily (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) : SphereSobolev 0 →L[ℝ] SphereSobolev 0 :=
  correctionBoundedPacket (normalizedFirstCorrectionCovector d.γ d.g₁ p)
    (fun j => normalFrameRelativeCoframeValue d.γ b j p)
    (nativePhysicalFirstCorrectionScalar d r0 b p)

def correctionNativeHalfFamily (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  halfLiftOfBoundedL2Operator (correctionNativeBoundedFamily d r0 b p)

lemma correctionNativeBoundedFamily_coarse (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) :
    (correctionNativeBoundedFamily d r0 b p).comp (sphereSobolevInclusionL 1 0 (by norm_num))=
      nativePhysicalFirstCorrectionFamily d r0 b p := by
  simpa only [correctionNativeBoundedFamily,nativePhysicalFirstCorrectionFamily,
    relativeCoframeNormalSobolevL] using correctionBoundedPacket_coarse
      (normalizedFirstCorrectionCovector d.γ d.g₁ p)
      (fun j => normalFrameRelativeCoframeValue d.γ b j p)
      (nativePhysicalFirstCorrectionScalar d r0 b p)

lemma correctionNativeHalfFamily_coarse (d : Data) (r0 : ℝ) (b : X)
    (p : NormalFrameRelativeParameter) :
    (sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)).comp
      (nativePhysicalFirstCorrectionFamily d r0 b p)=
    (correctionNativeHalfFamily d r0 b p).comp (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)) := by
  rw [←correctionNativeBoundedFamily_coarse]
  exact halfLiftOfBoundedL2Operator_coarse _

lemma correctionNativeHalfFamily_smooth {Y Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (r0 : ℝ) (b : X) :
    ContDiffOn ℝ ∞ (correctionNativeHalfFamily d r0 b) (nativeFirstCorrectionDomain Y Ω) := by
  have hCov := (hd.1.normalizedFirstCorrectionCovector_smooth hΩ hK).mono
    (inter_subset_left : nativeFirstCorrectionDomain Y Ω ⊆ normalFrameRelativePositiveDomain Ω)
  have hB := correctionRadialBoundedMapL.contDiff.comp_contDiffOn hCov
  have hM := (hd.1.1.contDiffOn_relativeCoframeNormalSobolevL hΩ hK 0 b).mono
    (inter_subset_left : nativeFirstCorrectionDomain Y Ω ⊆ normalFrameRelativePositiveDomain Ω)
  have hLog := ((hd.2.2.2.2.1.1.log (fun x hx => (hd.2.2.2.2.1.2 x hx).1.ne')).fderiv_of_isOpen
    (m:=∞) hY (by simp)).clm_apply (contDiffOn_const (c:=b))
  have hLog' : ContDiffOn ℝ ∞ (fun p : NormalFrameRelativeParameter =>
      fderiv ℝ (fun x => Real.log (d.radius x)) p.1.1 b) (nativeFirstCorrectionDomain Y Ω) :=
    hLog.comp contDiffOn_fst.fst (fun p hp => hp.2)
  have hScalar : ContDiffOn ℝ ∞ (nativePhysicalFirstCorrectionScalar d r0 b)
      (nativeFirstCorrectionDomain Y Ω) :=
    (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_snd)).mul hLog'
  have hBounded := (hB.clm_comp hM).add (hScalar.smul hB)
  exact contDiffOn_const.clm_comp (hBounded.clm_comp contDiffOn_const)

/-- A finite explicit budget for joint jets of the bounded correction. -/
def correctionBoundedJetBudget (N : ℕ) (Bq Bc Bt : ℝ) : ℝ :=
  2^N*(‖correctionRadialBoundedMapL‖*Bq)*
    (∑ j : I,2^N*Bc*‖coordinateMultiplierSobolevL 0 j‖)+
  2^N*Bt*(‖correctionRadialBoundedMapL‖*Bq)

lemma correctionBoundedPacket_jet_bound
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (q : P → X →L[ℝ] ℝ) (c : I → P → ℝ) (t : P → ℝ) (p : P)
    (N : ℕ) (Bq Bc Bt : ℝ)
    (hq : SmoothFiniteJetBound q p N Bq) (hc : ∀ j,SmoothFiniteJetBound (c j) p N Bc)
    (ht : SmoothFiniteJetBound t p N Bt) :
    SmoothFiniteJetBound (fun x => correctionBoundedPacket (q x) (fun j => c j x) (t x))
      p N (correctionBoundedJetBudget N Bq Bc Bt) := by
  have hB := hq.clm correctionRadialBoundedMapL
  have hM := SmoothFiniteJetBound.sum
    (fun j x => c j x • coordinateMultiplierSobolevL 0 j) p N
    (fun j => 2^N*Bc*‖coordinateMultiplierSobolevL 0 j‖)
    (fun j => (hc j).scalar (SmoothFiniteJetBound.constant _ p N))
  exact (hB.comp hM).add (ht.scalar hB)

end ShrinkingSpheres.ParallelEnergy
