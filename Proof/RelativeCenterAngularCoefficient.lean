import Proof.RelativeCenterOneRotationDerivative
import Proof.FixedGeneratorScalarCommutators
import Proof.UniformRelativeAngularDerivativeJets
import Proof.FiniteJetLinearCombination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic
namespace RelativeCenterErrorCoefficientFamily
variable {d : Data} {y a : X} {CC CH : ℝ}

/-- Remove the rotating frame slot from the actual parameter angular derivative. -/
def angularCoefficient (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (k i j : I) (p : NormalFrameRelativeParameter) : ClosedCoefficientJets 3 :=
  normalFrameRelativeAngularDerivative d.γ (C k).closed i j p-
    (if k=i then (C j).closed p else 0)+(if k=j then (C i).closed p else 0)

lemma angularCoefficient_coarse (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (k i j : I) :
    closedThreeJetCoarseScalarMultiplierL (angularCoefficient C k i j p)=
      closedCoefficientAngularCoarseL i j ((C k).closed p) := by
  have hC : ContDiff ℝ ∞ (C k).closed :=
    contDiff_commonSupportClosedCoefficientFamily 3 (C k).scalar (C k).smooth
      (C k).support (C k).compact (C k).supported
  have hD := closedThreeJetCoarseScalarMultiplierL.hasFDerivAt.comp_hasDerivAt (0:ℝ)
    (hasDerivAt_relativeAngularFamily d.γ (C k).closed p i j (hC.differentiable (by simp) _))
  have hEq := hD.unique (hasDerivAt_coarse_angular_curve_at C p hp he k i j)
  change closedThreeJetCoarseScalarMultiplierL
    (normalFrameRelativeAngularDerivative d.γ (C k).closed i j p)=_ at hEq
  have hIf (P : Prop) [Decidable P] (l : I) :
      closedThreeJetCoarseScalarMultiplierL (if P then (C l).closed p else 0)=
        if P then closedThreeJetCoarseScalarMultiplierL ((C l).closed p) else 0 := by
    split_ifs
    · rfl
    · exact closedThreeJetCoarseScalarMultiplierL.map_zero
  simp only [angularCoefficient,ContinuousLinearMap.map_add,ContinuousLinearMap.map_sub,hIf,hEq]
  abel

lemma angularCoefficient_half (C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (p : NormalFrameRelativeParameter) (hp : ∀ k,p ∈ (C k).domain)
    (he : ∀ k l,metricPair d.γ p.1.1 (p.1.2 (axis k)) (p.1.2 (axis l))=if k=l then 1 else 0)
    (k i j : I) :
    closedThreeJetHalfBoundaryScalarMultiplierL (angularCoefficient C k i j p)=
      closedCoefficientAngularHalfL i j ((C k).closed p) := by
  apply ContinuousLinearMap.ext
  intro u
  apply sphereSobolevInclusionL_injective (1/2:ℝ) 0 (by norm_num)
  rw [closedThreeJet_half_scalar_multiplier_coarse,closedCoefficientAngularHalfL_coarse,
    angularCoefficient_coarse C p hp he]

lemma closed_three_jets {k : I} (C : RelativeCenterErrorCoefficientFamily d y a k CC CH)
    (hCC : 0 ≤ CC) :
    SmoothFiniteJetBound C.closed ((y,frameVectorLinear d.frame y),0) 3 (CC*‖a‖*(d.radius y)^2) :=
  ⟨by positivity,(contDiff_commonSupportClosedCoefficientFamily 3 C.scalar C.smooth
    C.support C.compact C.supported).contDiffAt,C.joint⟩

/-- Only the existing completed C3 joint-three bound is consumed. -/
theorem uniform_angularCoefficient_two_jets {Ω : Set X} (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 1 ≤ K) :
    ∃ CG : ℝ,1 ≤ CG ∧ ∀ d : Data,Background Ω K M d.γ d.g₁ d.g₂ d.frame →
      ∀ y ∈ Ω,∀ a : X,∀ CC CH : ℝ,0 ≤ CC →
      ∀ C : (k : I) → RelativeCenterErrorCoefficientFamily d y a k CC CH,
      (∀ i j,metricPair d.γ y ((frameVectorLinear d.frame y) (axis i))
        ((frameVectorLinear d.frame y) (axis j))=if i=j then 1 else 0) →
      ∀ k i j : I,SmoothFiniteJetBound (angularCoefficient C k i j)
        ((y,frameVectorLinear d.frame y),0) 2 (((CG+2)*CC*‖a‖)*(d.radius y)^2) := by
  obtain ⟨CG,hCG,hJets⟩ := uniform_relative_angular_derivative_higher_jets
    (E:=ClosedCoefficientJets 3) hΩ 2 hm K M hK
  refine ⟨CG,hCG,?_⟩
  intro d hd y hy a CC CH hCC C he k i j
  let p : NormalFrameRelativeParameter := ((y,frameVectorLinear d.frame y),0)
  let B := CC*‖a‖*(d.radius y)^2
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hC (l : I) : SmoothFiniteJetBound (C l).closed p 3 B := (C l).closed_three_jets hCC
  obtain ⟨hSmooth,hBound⟩ := hJets d.γ d.g₁ d.g₂ d.frame hd y hy _ he (C k).closed
    (hC k).smooth B hB (hC k).bound i j
  have hAngular : SmoothFiniteJetBound (normalFrameRelativeAngularDerivative d.γ (C k).closed i j)
      p 2 (CG*B) := ⟨mul_nonneg (zero_le_one.trans hCG) hB,hSmooth,hBound⟩
  have hIf (P : Prop) [Decidable P] (l : I) :
      SmoothFiniteJetBound (fun q => if P then (C l).closed q else 0) p 2 B := by
    split_ifs
    · exact ⟨hB,(hC l).smooth,fun n hn => (hC l).bound n (by omega)⟩
    · exact (SmoothFiniteJetBound.constant (0:ClosedCoefficientJets 3) p 2).weaken
        (by simpa only [norm_zero] using hB)
  exact ((hAngular.sub (hIf (k=i) j)).add (hIf (k=j) i)).weaken
    (le_of_eq (by dsimp only [B];ring))

end RelativeCenterErrorCoefficientFamily
end ShrinkingSpheres
