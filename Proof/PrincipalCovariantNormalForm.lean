import Proof.PrincipalFirstDerivativeHalfCoefficient
import Proof.PrincipalModelFirstDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2400
open Set
open scoped ContDiff Topology
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
namespace PhysicalPrincipalData
variable {Y : Set X} {d : Data} {CF CT : ℝ}

def firstDerivativeHalfL (D : PhysicalPrincipalData Y d CF CT) (y : X) (j : I) :
    SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
  principalModelFirstDerivativeHalfL d y j+D.first.principalFirstDerivativeHalfL y j

/-- All zero-base terms of the SAME actual residual. This value still needs
its full compatible balanced coefficient and higher-jet estimates. -/
def remainingPotentialValue (D : PhysicalPrincipalData Y d CF CT) (y : X) (u : SphereSobolev 2) :
    SphereSobolev (-(1/2:ℝ)) :=
  sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
    (principalModelPotentialL d y u+pureAngularPrincipalPerturbationL d y u+
      principalCovariantRemainderSection d D.tensor (fun _ => u) y+
      principalRaisingCorrectionPerturbationL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)+
      principalDegreeCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) u)+
      principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) u))+
  D.first.principalRaisingCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
  D.first.principalDegreeCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
  D.first.principalCorrectionCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)+
  D.first.radiusPrincipalProductL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) u)

/-- Full actual covariant base-order normal form. The only second-base
coefficient is real scalar rQ, and the complete first-base coefficient acts
on the genuine half-order horizontal section. -/
theorem residualValue_covariant_normal_form (D : PhysicalPrincipalData Y d CF CT)
    (U : X → SphereSobolev 2) {y : X} (hy : y ∈ Y) :
    D.residualValue U y=
      sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
        (d.radius y • (∑ i : I,∑ j : I,frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y) i j •
          highSectionCovariantHessian d U y i j))+
      (∑ j : I,D.firstDerivativeHalfL y j (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num)
        (highSectionCovariantDerivative d U y (d.frame y j))))+
      D.remainingPotentialValue y (U y) := by
  let Inc := sphereSobolevInclusionL 0 (-(1/2:ℝ)) (by norm_num)
  let q := frameTensorMatrix d.γ d.frame y (principal d.γ d.g₂ y)
  let H := fun j => highSectionCovariantDerivative d U y (d.frame y j)
  have hModel := congrArg Inc (principal_model_base_collection d U y)
  have hFirst := D.first.principal_first_remainder_actual U hy
  have hModelFirst : Inc (∑ j : I,principalModelFirstDerivativeL d y j (H j))=
      ∑ j : I,principalModelFirstDerivativeHalfL d y j
        (sphereSobolevInclusionL 1 (1/2:ℝ) (by norm_num) (H j)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => principalModelFirstDerivativeHalfL_actual d y j (H j))
  simp only [map_add] at hModel
  let Base := Inc (d.radius y • (∑ i : I,∑ j : I,q i j • highSectionCovariantHessian d U y i j))
  let Pot := Inc (principalModelPotentialL d y (U y))
  have hModelB := hModel.trans
    (congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Base+z+Pot) hModelFirst)
  have hAlgebra {W : Type} [AddCommGroup W]
      (m b x p a f c d e k l1 l2 l3 l4 z : W) (hm : m=b+x+p) (hf : f=z) :
      m+a+f+c+d+e+k+l1+l2+l3+l4=
        b+(x+z)+(p+a+c+d+e+k+l1+l2+l3+l4) := by rw [hm,hf];abel
  have h := hAlgebra _ _ _ _
    (Inc (pureAngularPrincipalPerturbationL d y (U y))) _
    (Inc (principalCovariantRemainderSection d D.tensor U y))
    (Inc (principalRaisingCorrectionPerturbationL d y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))))
    (Inc (principalDegreeCorrectionCrossL d y (sphereSobolevInclusionL 2 1 (by norm_num) (U y))))
    (Inc (principalCorrectionProductL 0 d y (sphereSobolevInclusionL 2 0 (by norm_num) (U y))))
    (D.first.principalRaisingCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)))
    (D.first.principalDegreeCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)))
    (D.first.principalCorrectionCrossL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y)))
    (D.first.radiusPrincipalProductL y (sphereSobolevInclusionL 2 (3/2:ℝ) (by norm_num) (U y))) _ hModelB hFirst
  simpa only [residualValue,remainingPotentialValue,firstDerivativeHalfL,
    map_add,_root_.add_apply,Finset.sum_add_distrib,Base,Pot,Inc,q,H,
    principalCovariantRemainderSection] using h

theorem norm_firstDerivativeHalfL_small {Ω : Set X} (hΩ : IsOpen Ω) {m : ℕ} (hm : 2 ≤ m)
    {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (D : PhysicalPrincipalData Y d CF CT) (hCF : 0 ≤ CF)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 1 ≤ K) (hf : 1 ≤ floor)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {y : X} (hy : y ∈ Y) (j : I) :
    ‖D.firstDerivativeHalfL y j‖ ≤
      (108*(K+1)*K^2+540*K^2*radialDriftSobolevBound (-(1/2:ℝ))+
        54*(K+1)*K^2*(firstCorrectionGradeBound (-(1/2:ℝ)) K (M ⟨1,by omega⟩)+CF))*ε/beta d.γ d.radius y := by
  exact (norm_add_le _ _).trans ((add_le_add
    (hd.norm_principalModelFirstDerivativeHalfL_small hK hf hε hε1 hy j)
    (D.first.norm_principalFirstDerivativeHalfL_small hΩ hm hCF hd hK hf hε hε1 hy j)).trans_eq (by ring))
theorem firstDerivativeHalfL_smooth {Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} {K ρ c₀ floor ε : ℝ} {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ}
    (D : PhysicalPrincipalData Y d CF CT)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K) (j : I) :
    ContDiffOn ℝ ∞ (fun y => D.firstDerivativeHalfL y j) Y :=
  (hd.contDiffOn_principalModelFirstDerivativeHalfL hY hK j).add
    (D.first.principalFirstDerivativeHalfL_smooth hY hΩ hd hK j)

end PhysicalPrincipalData
end ShrinkingSpheres
