module

public import Proof.CalderonN.ParametricBallVelocityAdjoint

import Proof.CalderonN.FlatAngularAdjoint
import Proof.CalderonN.MetricCalculus
import Mathlib.Tactic

/-! Adapted from `BallVelocityDatumCongruence` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]
open OAI.AnisotropicCalderon.SmoothSphereRotation

/-- A velocity adjoint at a sphere point only uses the metric and velocity
at the given parameter and the sphere restriction of the datum. -/
theorem parametricBallVelocityAdjoint_congr_slice {P Q : Type}
    {g : P × (X dim) → (Mat dim)} {h : Q × (X dim) → (Mat dim)} {V : P × (X dim) → (X dim)} {W : Q × (X dim) → (X dim)}
    {φ : P × (X dim) → ℝ} {ψ : Q × (X dim) → ℝ} {p : P} {q : Q}
    (hm : (fun z => g (p,z)) = (fun z => h (q,z)))
    (hv : (fun z => V (p,z)) = (fun z => W (q,z)))
    {U S : Set (X dim)} (hU : IsOpen U) (hS : IsOpen S)
    (hCU : closedBall (0 : (X dim)) 1 ⊆ U) (hSS : (standardSphere dim) ⊆ S) (hSU : S ⊆ U)
    (hS₀ : (0 : (X dim)) ∉ S) (hg : SmoothMetric U (fun z => g (p,z)))
    (hV : ContDiffOn ℝ ∞ (fun z => V (p,z)) S)
    (hφ : ContDiffOn ℝ ∞ (fun z => φ (p,z)) S)
    (hψ : ContDiffOn ℝ ∞ (fun z => ψ (q,z)) S)
    (hdata : EqOn (fun z => φ (p,z)) (fun z => ψ (q,z)) (standardSphere dim))
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    parametricBallVelocityAdjoint g V φ (p,w) = parametricBallVelocityAdjoint h W ψ (q,w) := by
  let m : (MetricField dim) := fun z => g (p,z)
  let v : (X dim) → (X dim) := fun z => V (p,z)
  let c (z : (X dim)) := conormalComponent m z (v z)
  let a (z : (X dim)) := φ (p,z)*c z
  let b (z : (X dim)) := ψ (q,z)*c z
  have hC : ContDiffOn ℝ ∞ (ballConormalVector m) S := (contDiffOn_ballConormalVector hg).mono hSU
  have hc : ContDiffOn ℝ ∞ c S :=
    (contDiffOn_id.inner ℝ hV).div (contDiffOn_id.inner ℝ hC)
      (fun z hz => (ballConormalVector_inner_pos (hg.2 z (hSU hz))
        (fun h => hS₀ (h ▸ hz))).ne')
  have ht : ContDiffOn ℝ ∞ (fun z => tangentialComponent m z (v z)) S := hV.sub (hc.smul hC)
  have hPa := fixedBallPoisson_solution hU hCU hg ⟨S,hS,hSS,hφ.mul hc⟩
  have hPb := fixedBallPoisson_solution hU hCU hg ⟨S,hS,hSS,hψ.mul hc⟩
  have hab : EqOn a b (standardSphere dim) :=
    fun z hz => congrArg (· * c z) (hdata hz)
  have hpEq := eqOn_fixedBallSolution hU hCU hg hPa hPb hab
  have hpDeriv := eqOn_fderiv_closedUnitBall hPa.1 hPb.1 hpEq (sphere_subset_closedBall hw)
  rw [parametricBallVelocityAdjoint_on_sphere g V φ p hw,
    parametricBallVelocityAdjoint_on_sphere h W ψ q hw]
  have hVz (z : (X dim)) : W (q,z) = V (p,z) := (congrFun hv z).symm
  simp only [velocityBoundaryDatum,← hm,hVz]
  change ballVelocityAdjoint m v (fun z => φ (p,z)) (fixedBallPoisson m a) w =
    ballVelocityAdjoint m v (fun z => ψ (q,z)) (fixedBallPoisson m b) w
  unfold ballVelocityAdjoint
  rw [ballConormal_eq_fderiv_conormalVector,ballConormal_eq_fderiv_conormalVector,hpDeriv]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let k (z : (X dim)) := z i * tangentialComponent m z (v z) j
  have hk : ContDiffOn ℝ ∞ k S :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp_contDiffOn ht)
  exact sphereRotationDerivative_congr_of_eqOn_sphere hw
    (((hφ.mul hk).contDiffAt (hS.mem_nhds (hSS hw))).differentiableAt (by simp))
    (((hψ.mul hk).contDiffAt (hS.mem_nhds (hSS hw))).differentiableAt (by simp))
    (fun z hz => congrArg (· * k z) (hdata hz)) i j

/-- Zero angular input gives zero velocity adjoint. -/
theorem parametricBallVelocityAdjoint_zero {P : Type}
    {g : P × (X dim) → (Mat dim)} (V : P × (X dim) → (X dim)) (p : P) {U : Set (X dim)} (hU : IsOpen U)
    (hCU : closedBall (0 : (X dim)) 1 ⊆ U) (hg : SmoothMetric U (fun z => g (p,z)))
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    parametricBallVelocityAdjoint g V (fun _ => 0) (p,w) = 0 := by
  let m : (MetricField dim) := fun z => g (p,z)
  have hsol : FixedBallSolution m 0 0 := by
    refine ⟨contDiff_const,fun _ _ => rfl,fun z hz => ?_⟩
    have h₀ (i : (I dim)) : coordDeriv i (0 : (X dim) → ℝ) = 0 := by
      funext x
      change fderiv ℝ (fun _ : (X dim) => (0 : ℝ)) x (axis i) = 0
      simp
    simp [laplace,h₀]
  have hp := fixedBallPoisson_solution hU hCU hg
    (show smoothNear (0 : (X dim) → ℝ) (standardSphere dim) from ⟨univ,isOpen_univ,subset_univ _,contDiffOn_const⟩)
  have he := eqOn_fixedBallSolution hU hCU hg hp hsol (fun _ _ => rfl)
  have hd := eqOn_fderiv_closedUnitBall hp.1 hsol.1 he (sphere_subset_closedBall hw)
  change fderiv ℝ (fixedBallPoisson m 0) w = fderiv ℝ (fun _ : (X dim) => (0 : ℝ)) w at hd
  rw [parametricBallVelocityAdjoint_on_sphere g V _ p hw]
  simp only [velocityBoundaryDatum,zero_mul]
  change ballVelocityAdjoint m (fun z => V (p,z)) 0 (fixedBallPoisson m 0) w = 0
  simp only [ballVelocityAdjoint,ballConormal_eq_fderiv_conormalVector,hd,Pi.zero_apply,zero_mul,
    sphereRotationDerivative,fderiv_const_apply,zero_apply,Finset.sum_const_zero,sub_zero]

end CalderonN
