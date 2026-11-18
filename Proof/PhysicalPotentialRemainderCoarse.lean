import Proof.CoarsePotentialSmoothParts
import Proof.UniformPhysicalCoarseFirstErrorBound
import Proof.PhysicalPotentialQuadraticSplit
import Proof.PhysicalBalancedPotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2800
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

lemma balancedCoarsePotentialL_add (A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    balancedCoarsePotentialL (A+B)=balancedCoarsePotentialL A+balancedCoarsePotentialL B := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [balancedCoarsePotentialL,ContinuousLinearMap.comp_apply,_root_.add_apply,map_add]

lemma balancedCoarsePotentialL_smul (a : ℝ) (A : SphereSobolev 1 →L[ℝ] SphereSobolev 0) :
    balancedCoarsePotentialL (a • A)=a • balancedCoarsePotentialL A := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [balancedCoarsePotentialL,ContinuousLinearMap.comp_apply,_root_.smul_apply,map_smul]

def potentialRemainderCoarseRawBudget (K M1 M2 C2 CE CT : ℝ) : ℝ :=
  81*(K+1)*K^2*(2*|C2|+4)+
  81*(K+1)*K^2*(firstFrameAdjointCovariantBudget K M1 M2 C2+CT)+
  162*K^2*(firstCorrectionGradeBound 1 K M1+firstCorrectionGradeBound 0 K M1)+
  162*(K+1)*K^2*(firstCorrectionGradeBound 1 K M1+firstCorrectionGradeBound 0 K M1)+
  81*(K+1)*K^2*(firstCorrectionGradeBound 0 K M1)^2+
  81*(K+1)*K^2*(firstCorrectionGradeBound 0 K M1+firstCorrectionGradeBound 1 K M1)*CE

def potentialRemainderCoarseBudget (K M1 M2 C2 CE CT : ℝ) : ℝ :=
  |potentialRemainderCoarseRawBudget K M1 M2 C2 CE CT|

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- The complete complementary potential as an actual order-one operator,
retaining all six original groups and their SAME physical coefficients. -/
def potentialRemainderCoarseL (P : PhysicalPrincipalData Y d CF CT) (y : X) :
    SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
  principalModelPotentialLinearCoarseL d y+principalCovariantPotentialL d P.tensor y+
  principalRaisingCorrectionPerturbationL d y+principalDegreeCorrectionCrossL d y+
  (principalCorrectionProductL 0 d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))+
  radiusFrameCorrectionErrorCoarseCrossL d (actualFrameFirstAdjointErrorFamily d P.adjoint P.center)
    (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) y

lemma correction_error_coarse_cross_balanced (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) :
    balancedCoarsePotentialL (radiusFrameCorrectionErrorCoarseCrossL d
      (actualFrameFirstAdjointErrorFamily d P.adjoint P.center)
      (fun x i j => frameTensorMatrix d.γ d.frame x (principal d.γ d.g₂ x) i j) y)=
      P.first.principalCorrectionCrossL y := by
  rw [radiusFrameCorrectionErrorCoarseCrossL,balancedCoarsePotentialL_smul,
    frameCorrectionErrorCoarseCrossL_balanced d _ P.first.low P.first.high _ y
      (fun i => P.first.low_coarse i y hy) (fun j => P.first.high_coarse j y hy)]
  rfl

/-- Genuine balanced agreement, rather than equality of underlying Sobolev
types, identifies the entire complementary operator with the previous split. -/
lemma potentialRemainderCoarseL_balanced (P : PhysicalPrincipalData Y d CF CT) {y : X} (hy : y ∈ Y) :
    balancedCoarsePotentialL (P.potentialRemainderCoarseL y)=P.potentialRemainderHalfL y := by
  simp only [potentialRemainderCoarseL,balancedCoarsePotentialL_add,
    principalModelPotentialLinearCoarseL_balanced,P.correction_error_coarse_cross_balanced hy]
  rfl

lemma norm_potentialRemainderCoarseL_small {Ω : Set X}
    (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε CE : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (P : PhysicalPrincipalData Y d CF CT) (hCT : 0 ≤ CT) (hCE : 0 ≤ CE)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y)
    (hE : ∀ i,‖actualFrameFirstAdjointErrorFamily d P.adjoint P.center i y‖ ≤ CE*d.radius y) :
    ‖P.potentialRemainderCoarseL y‖ ≤
      potentialRemainderCoarseBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) CE CT*ε := by
  have hModel := hd.norm_principalModelPotentialLinearCoarseL_small hY hK hf hε hε1 hy
  have hCov := P.norm_principalCovariantPotentialL_small hY hΩ hm hCT hd hK hf hε hε1 hy
  have hRP := hd.norm_principalRaisingCorrectionPerturbationL_small hΩ hm hK hf hε hε1 hy
  have hDF := hd.norm_principalDegreeCorrectionCrossL_small hΩ hm hK hf hε hε1 hy
  have hFF : ‖(principalCorrectionProductL 0 d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤
      81*(K+1)*K^2*(firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩))^2*ε := by
    have hComp : ‖(principalCorrectionProductL 0 d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤
        ‖principalCorrectionProductL 0 d y‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (mul_one _))
    exact hComp.trans (hd.norm_principalCorrectionProductL_small hΩ hm hK hf hε hε1 0 hy)
  have hFE := hd.norm_radiusFrameCorrectionErrorCoarseCrossL_small hm hΩ hK hf hε hε1 hCE
    (actualFrameFirstAdjointErrorFamily d P.adjoint P.center) hy hE
  have hAdd {A B : SphereSobolev 1 →L[ℝ] SphereSobolev 0} {a b : ℝ}
      (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) : ‖A+B‖ ≤ a+b := (norm_add_le _ _).trans (add_le_add hA hB)
  have hRaw : ‖P.potentialRemainderCoarseL y‖ ≤
      potentialRemainderCoarseRawBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) CE CT*ε :=
    (hAdd (hAdd (hAdd (hAdd (hAdd hModel hCov) hRP) hDF) hFF) hFE).trans_eq
      (by dsimp only [potentialRemainderCoarseRawBudget];ring)
  exact hRaw.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hε)
end PhysicalPrincipalData
end ShrinkingSpheres
