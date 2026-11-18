import Proof.PrincipalModelPotentialHalf
import Proof.BalancedCoarsePotential
import Proof.PrincipalCovariantPotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic

def physicalPotentialBudget (K M1 M2 C2 CF CT : ℝ) : ℝ :=
  (81*(K+1)*K^2*(2*|C2|+8)+3240*K^2*radialDriftSobolevBound (-(1/2:ℝ)))+
  8100*K^2*radialDriftSobolevBound (-(1/2:ℝ))*radialDriftSobolevBound (-(3/2:ℝ))+
  81*(K+1)*K^2*(firstFrameAdjointCovariantBudget K M1 M2 C2+CT)+
  162*K^2*(firstCorrectionGradeBound 1 K M1+firstCorrectionGradeBound 0 K M1)+
  162*(K+1)*K^2*(firstCorrectionGradeBound 1 K M1+firstCorrectionGradeBound 0 K M1)+
  81*(K+1)*K^2*(firstCorrectionGradeBound 0 K M1)^2+
  81*(K+1)*K^2*(10*radialDriftSobolevBound (-(1/2:ℝ))+10*radialDriftSobolevBound (-(3/2:ℝ)))*CF+
  324*(K+1)*K^2*CF+
  81*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K M1+firstCorrectionGradeBound (1/2:ℝ) K M1)*CF+
  81*(K+1)*K^2*CF^2

namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

/-- All zero-base terms of the SAME physical residual, on the genuine
    balanced angular domains. Coarse order-one pieces use canonical inclusions. -/
def remainingPotentialHalfL (D : PhysicalPrincipalData Y d CF CT) (y : X) :
    SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  principalModelPotentialHalfL d y+pureAngularPrincipalHalfL d y+
  balancedCoarsePotentialL (principalCovariantPotentialL d D.tensor y)+
  balancedCoarsePotentialL (principalRaisingCorrectionPerturbationL d y)+
  balancedCoarsePotentialL (principalDegreeCorrectionCrossL d y)+
  balancedCoarsePotentialL ((principalCorrectionProductL 0 d y).comp
    (sphereSobolevInclusionL 1 0 (by norm_num)))+
  D.first.principalRaisingCrossL y+D.first.principalDegreeCrossL y+
  D.first.principalCorrectionCrossL y+D.first.radiusPrincipalProductL y

lemma remainingPotentialHalfL_actual (D : PhysicalPrincipalData Y d CF CT) {y : X}
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0)
    (u : SphereSobolev 2) :
    D.remainingPotentialHalfL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)=
      D.remainingPotentialValue y u := by
  simp only [remainingPotentialHalfL,remainingPotentialValue,_root_.add_apply,map_add,
    ← principalModelPotentialHalfL_actual d y u,pureAngularPrincipalHalfL_actual d y he u,
    balancedCoarsePotentialL_actual,ContinuousLinearMap.comp_apply,sphereSobolevInclusionL_trans_apply,
    principalCovariantPotentialL_actual d D.tensor (fun _ => u) y]

theorem norm_remainingPotentialHalfL_small {Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (D : PhysicalPrincipalData Y d CF CT) (hCF : 0 ≤ CF) (hCT : 0 ≤ CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) :
    ‖D.remainingPotentialHalfL y‖ ≤
      physicalPotentialBudget K (M ⟨1,by omega⟩) (M ⟨2,by omega⟩) (Cj 2) CF CT*ε := by
  have hModel := hd.norm_principalModelPotentialHalfL_small hY hK hf hε hε1 hy
  have hPure := hd.norm_pureAngularPrincipalHalfL_small hK hf hε hε1 hy
  have hCov := (norm_balancedCoarsePotentialL_le (principalCovariantPotentialL d D.tensor y)).trans
    (D.norm_principalCovariantPotentialL_small hY hΩ hm hCT hd hK hf hε hε1 hy)
  have hRP := (norm_balancedCoarsePotentialL_le (principalRaisingCorrectionPerturbationL d y)).trans
    (hd.norm_principalRaisingCorrectionPerturbationL_small hΩ hm hK hf hε hε1 hy)
  have hDF := (norm_balancedCoarsePotentialL_le (principalDegreeCorrectionCrossL d y)).trans
    (hd.norm_principalDegreeCorrectionCrossL_small hΩ hm hK hf hε hε1 hy)
  have hFF : ‖balancedCoarsePotentialL ((principalCorrectionProductL 0 d y).comp
      (sphereSobolevInclusionL 1 0 (by norm_num)))‖ ≤
      81*(K+1)*K^2*(firstCorrectionGradeBound 0 K (M ⟨1,by omega⟩))^2*ε := by
    have hComp : ‖(principalCorrectionProductL 0 d y).comp (sphereSobolevInclusionL 1 0 (by norm_num))‖ ≤
        ‖principalCorrectionProductL 0 d y‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left (norm_sphereSobolevInclusionL_le _ _ _) (norm_nonneg _)).trans_eq (mul_one _))
    exact (norm_balancedCoarsePotentialL_le _).trans
      (hComp.trans (hd.norm_principalCorrectionProductL_small hΩ hm hK hf hε hε1 0 hy))
  have hRE := D.first.norm_principalRaisingCrossL_small hCF hd hK hf hε hε1 hy
  have hDE := D.first.norm_principalDegreeCrossL_small hCF hd hK hf hε hε1 hy
  have hFE := D.first.norm_principalCorrectionCrossL_small hΩ hm hCF hd hK hf hε hε1 hy
  have hEE := D.first.norm_radiusPrincipalProductL_small hCF hd hK hf hε hε1 hy
  have hAdd {A B : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ))} {a b : ℝ}
      (hA : ‖A‖ ≤ a) (hB : ‖B‖ ≤ b) : ‖A+B‖ ≤ a+b :=
    (norm_add_le _ _).trans (add_le_add hA hB)
  exact (hAdd (hAdd (hAdd (hAdd (hAdd (hAdd (hAdd (hAdd (hAdd hModel hPure) hCov) hRP) hDF) hFF)
    hRE) hDE) hFE) hEE).trans_eq (by dsimp only [physicalPotentialBudget];ring)

/-- The complete actual residual now has genuine balanced coefficients at
    each base order. Higher jets and the energy-form estimate remain separate. -/
theorem residualValue_balanced_normal_form (D : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev 2) {y : X} (hy : y ∈ Y)
    (he : ∀ i j,metricPair d.γ y (d.frame y i) (d.frame y j)=if i=j then 1 else 0) :
    D.residualValue U y=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
          highSectionCovariantHessian d U y i j))+
      (∑ j : I,D.firstDerivativeHalfL y j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d U y (d.frame y j))))+
      D.remainingPotentialHalfL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)) := by
  rw [D.remainingPotentialHalfL_actual he]
  exact D.residualValue_covariant_normal_form U hy
end PhysicalPrincipalData
end ShrinkingSpheres
