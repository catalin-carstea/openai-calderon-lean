import Proof.LocalScalarAdjointHigherJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 30
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.ActualScalarPrincipalAdjoint

lemma contDiffOn_adjointFirstCoefficient {Y : Set X} (hY : IsOpen Y)
    (mu : X → ℝ) (a : MetricField) (hmu : ContDiffOn ℝ ∞ mu Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (hpos : ∀ x ∈ Y,mu x ≠ 0) (i : I) :
    ContDiffOn ℝ ∞ (fun x => adjointFirstCoefficient axis mu a x i) Y := by
  have hSum : ContDiffOn ℝ ∞ (fun x => ∑ j : I,coordDeriv j (fun y => mu y*a y i j) x) Y :=
    ContDiffOn.sum (fun j _ => contDiffOn_coordDeriv hY (hmu.mul (ha i j)) j)
  exact (contDiffOn_const.mul (hmu.inv hpos)).mul hSum

lemma contDiffOn_adjointZeroCoefficient {Y : Set X} (hY : IsOpen Y)
    (mu : X → ℝ) (a : MetricField) (hmu : ContDiffOn ℝ ∞ mu Y)
    (ha : ∀ i j,ContDiffOn ℝ ∞ (fun x => a x i j) Y)
    (hpos : ∀ x ∈ Y,mu x ≠ 0) :
    ContDiffOn ℝ ∞ (adjointZeroCoefficient axis mu a) Y := by
  have hSum : ContDiffOn ℝ ∞ (fun x => ∑ i : I,∑ j : I,
      coordDeriv j (coordDeriv i (fun y => mu y*a y i j)) x) Y :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      contDiffOn_coordDeriv hY (contDiffOn_coordDeriv hY (hmu.mul (ha i j)) i) j))
  exact (hmu.inv hpos).mul hSum

end ShrinkingSpheres
