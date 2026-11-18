import Proof.BoundaryCoefficientC1Bounds
import Proof.RadialConversionCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge OAI.AnisotropicCalderon.DirichletFamily
open OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

lemma boundaryNormalCoefficient_hasCompactSupport (F : SmoothCoefficientMatrix 2) :
    HasCompactSupport (boundaryNormalCoefficientData F).1 := by
  change HasCompactSupport (fun x : X => ∑ i : I,∑ j : I,x i*coefficientValue 2 (F i j) x*x j)
  have hTerm (i j : I) : HasCompactSupport (fun x : X => x i*coefficientValue 2 (F i j) x*x j) := by
    have hFirst : HasCompactSupport (fun x : X => x i*coefficientValue 2 (F i j) x) :=
      (hasCompactSupport_coefficientValue 2 (F i j)).mul_left
    exact hFirst.mul_right
  have hSum := HasCompactSupport.finset_sum (s:=Finset.univ) (fun i hi =>
    HasCompactSupport.finset_sum (s:=Finset.univ) (fun j hj => hTerm i j))
  convert hSum using 1
  funext x
  rfl

lemma boundaryTangentCoefficient_hasCompactSupport (F : SmoothCoefficientMatrix 2) (j : I) :
    HasCompactSupport (boundaryTangentCoefficientData F j).1 := by
  have hTerm (i : I) : HasCompactSupport (fun x : X => x i*coefficientValue 2 (F i j) x) :=
    (hasCompactSupport_coefficientValue 2 (F i j)).mul_left
  have hCol : HasCompactSupport (fun x : X => ∑ i : I,x i*coefficientValue 2 (F i j) x) := by
    have hSum := HasCompactSupport.finset_sum (s:=Finset.univ) (fun i hi => hTerm i)
    convert hSum using 1
    funext x
    rfl
  have hProd : HasCompactSupport (fun x : X => (boundaryNormalCoefficientData F).1 x*x j) :=
    (boundaryNormalCoefficient_hasCompactSupport F).mul_right
  exact hCol.sub hProd

def normalCoefficientJet (F : SmoothCoefficientMatrix 2) : SmoothCoefficientJets 2 :=
  compactCoefficient 2 (boundaryNormalCoefficientData F).1 (boundaryNormalCoefficientData F).2
    (boundaryNormalCoefficient_hasCompactSupport F)

def tangentCoefficientJet (F : SmoothCoefficientMatrix 2) (j : I) : SmoothCoefficientJets 2 :=
  compactCoefficient 2 (boundaryTangentCoefficientData F j).1 (boundaryTangentCoefficientData F j).2
    (boundaryTangentCoefficient_hasCompactSupport F j)

lemma coefficientValue_normalCoefficientJet (F : SmoothCoefficientMatrix 2) :
    coefficientValue 2 (normalCoefficientJet F) = (boundaryNormalCoefficientData F).1 :=
  coefficientValue_compactCoefficient 2 _ _ _

lemma coefficientValue_tangentCoefficientJet (F : SmoothCoefficientMatrix 2) (j : I) :
    coefficientValue 2 (tangentCoefficientJet F j) = (boundaryTangentCoefficientData F j).1 :=
  coefficientValue_compactCoefficient 2 _ _ _

lemma coefficientSmoothData_normalCoefficientJet (F : SmoothCoefficientMatrix 2) :
    coefficientSmoothData (normalCoefficientJet F) = boundaryNormalCoefficientData F :=
  Subtype.ext (coefficientValue_normalCoefficientJet F)

lemma coefficientSmoothData_tangentCoefficientJet (F : SmoothCoefficientMatrix 2) (j : I) :
    coefficientSmoothData (tangentCoefficientJet F j) = boundaryTangentCoefficientData F j :=
  Subtype.ext (coefficientValue_tangentCoefficientJet F j)

theorem normalCoefficientJet_local_C1 (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q) :
    LocalC1Bound (coefficientValue 2 (normalCoefficientJet F)) (36*q) := by
  rw [coefficientValue_normalCoefficientJet]
  exact boundaryNormalCoefficient_local_C1 F q hq hValue hDerivative

theorem tangentCoefficientJet_local_C1 (F : SmoothCoefficientMatrix 2) (q : ℝ) (hq : 0 ≤ q)
    (hValue : ∀ i j,∀ x ∈ (ballOpens : Set X),|coefficientValue 2 (F i j) x| ≤ q)
    (hDerivative : ∀ i j,∀ x ∈ (ballOpens : Set X),‖fderiv ℝ (coefficientValue 2 (F i j)) x‖ ≤ q)
    (j : I) : LocalC1Bound (coefficientValue 2 (tangentCoefficientJet F j)) (78*q) := by
  rw [coefficientValue_tangentCoefficientJet]
  exact boundaryTangentCoefficient_local_C1 F q hq hValue hDerivative j

end ShrinkingSpheres
