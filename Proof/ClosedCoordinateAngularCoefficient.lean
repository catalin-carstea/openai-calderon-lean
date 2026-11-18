import Proof.ClosedCoefficientAngularProduct
import Proof.FirstErrorScalarCoefficientBounds
import Proof.FiniteJetLinearCombination
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set Filter
open scoped ContDiff Topology InnerProductSpace
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.DirichletFamily OAI.AnisotropicCalderon.SphereHarmonic

/-- Angular coefficient of a coordinate times a completed scalar. -/
def closedCoordinateAngularCoefficient (Q0 : SmoothCoefficientJets 2) (k i j : I)
    (Q R : ClosedCoefficientJets 3) : ClosedCoefficientJets 3 :=
  closedCoordinateCoefficientProductL Q0 k R+
    (if k=j then closedCoordinateCoefficientProductL Q0 i Q else 0)-
    (if k=i then closedCoordinateCoefficientProductL Q0 j Q else 0)

lemma closedCoordinateAngularCoefficient_half (Q0 : SmoothCoefficientJets 2)
    (hQ0 : ∀ z ∈ Metric.closedBall (0:X) 1,coefficientValue 2 Q0 =ᶠ[𝓝 z] (fun _ => (1:ℝ)))
    (k i j : I) (Q R : ClosedCoefficientJets 3)
    (hR : closedThreeJetHalfBoundaryScalarMultiplierL R=closedCoefficientAngularHalfL i j Q) :
    closedThreeJetHalfBoundaryScalarMultiplierL (closedCoordinateAngularCoefficient Q0 k i j Q R)=
      closedCoefficientAngularHalfL i j (closedCoordinateCoefficientProductL Q0 k Q) := by
  let M := closedThreeJetHalfBoundaryScalarMultiplierL
  have hProd := closedCoefficientAngularHalf_fixed_product (coordinateScalarSmoothJet Q0 k) Q i j
  rw [coordinateScalarClosedJet_angular_half Q0 hQ0,coordinateScalarClosedJet_half Q0 hQ0] at hProd
  have hFirst : M (closedCoordinateCoefficientProductL Q0 k R)=
      (coordinateMultiplierSobolevL (1/2:ℝ) k).comp (closedCoefficientAngularHalfL i j Q) :=
    (closedCoordinateCoefficientProduct_half Q0 hQ0 k R).trans
      (congrArg (fun T : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) =>
        (coordinateMultiplierSobolevL (1/2:ℝ) k).comp T) hR)
  have hIf (T : Prop) [Decidable T] (l : I) :
      M (if T then closedCoordinateCoefficientProductL Q0 l Q else 0)=
        if T then (coordinateMultiplierSobolevL (1/2:ℝ) l).comp (M Q) else 0 := by
    split_ifs
    · exact closedCoordinateCoefficientProduct_half Q0 hQ0 l Q
    · exact M.map_zero
  have hMap : M (closedCoordinateAngularCoefficient Q0 k i j Q R)=
      (coordinateMultiplierSobolevL (1/2:ℝ) k).comp (closedCoefficientAngularHalfL i j Q)+
        (if k=j then (coordinateMultiplierSobolevL (1/2:ℝ) i).comp (M Q) else 0)-
        (if k=i then (coordinateMultiplierSobolevL (1/2:ℝ) j).comp (M Q) else 0) := by
    exact (M.map_sub _ _).trans
      (congrArg₂ (fun U V : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => U-V)
        ((M.map_add _ _).trans (congrArg₂ (fun U V : SphereSobolev (1/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => U+V)
          hFirst (hIf (k=j) i))) (hIf (k=i) j))
  have hAlg :
      (coordinateMultiplierSobolevL (1/2:ℝ) k).comp (closedCoefficientAngularHalfL i j Q)+
        (if k=j then (coordinateMultiplierSobolevL (1/2:ℝ) i).comp (M Q) else 0)-
        (if k=i then (coordinateMultiplierSobolevL (1/2:ℝ) j).comp (M Q) else 0)=
      ((if k=j then coordinateMultiplierSobolevL (1/2:ℝ) i else 0)-
        (if k=i then coordinateMultiplierSobolevL (1/2:ℝ) j else 0)).comp (M Q)+
        (coordinateMultiplierSobolevL (1/2:ℝ) k).comp (closedCoefficientAngularHalfL i j Q) := by
    split_ifs <;> simp only [ContinuousLinearMap.sub_comp,ContinuousLinearMap.zero_comp] <;> abel
  exact hMap.trans (hAlg.trans hProd.symm)

lemma closedCoordinateAngularCoefficient_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Q0 : SmoothCoefficientJets 2) (k i j : I)
    (Q R : P → ClosedCoefficientJets 3) (p : P) (N : ℕ) (BQ BR : ℝ)
    (hQ : SmoothFiniteJetBound Q p N BQ) (hR : SmoothFiniteJetBound R p N BR) :
    SmoothFiniteJetBound (fun x => closedCoordinateAngularCoefficient Q0 k i j (Q x) (R x)) p N
      (firstErrorScalarFixedBudget Q0*(BR+2*BQ)) := by
  let J := firstErrorScalarFixedBudget Q0
  have hJ : 0 ≤ J := zero_le_one.trans (firstErrorScalarFixedBudget_bounds Q0).1
  have hProd (l : I) : ‖closedCoordinateCoefficientProductL Q0 l‖ ≤ J :=
    (firstErrorScalarFixedBudget_bounds Q0).2.2.2 l
  have hOne := (hR.clm (closedCoordinateCoefficientProductL Q0 k)).weaken
    (mul_le_mul_of_nonneg_right (hProd k) hR.nonneg)
  have hIf (T : Prop) [Decidable T] (l : I) :
      SmoothFiniteJetBound (fun x => if T then closedCoordinateCoefficientProductL Q0 l (Q x) else 0)
        p N (J*BQ) := by
    split_ifs
    · exact (hQ.clm (closedCoordinateCoefficientProductL Q0 l)).weaken
        (mul_le_mul_of_nonneg_right (hProd l) hQ.nonneg)
    · exact (SmoothFiniteJetBound.constant (0:ClosedCoefficientJets 3) p N).weaken
        (by simpa only [norm_zero] using mul_nonneg hJ hQ.nonneg)
  exact ((hOne.add (hIf (k=j) i)).sub (hIf (k=i) j)).weaken (le_of_eq (by dsimp only [J];ring))
end ShrinkingSpheres
