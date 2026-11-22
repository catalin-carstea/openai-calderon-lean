module

public import Proof.CalderonN.ActualGaussOperatorExpansion

import Proof.CalderonN.SmoothConormalTaylorSymmetry
import Mathlib.Tactic

/-! Identify the single symmetric conormal Taylor remainder shared
by the angular generators of the actual moving trace. -/

public section

noncomputable section
open Set Metric Filter
open scoped ContDiff Matrix.Norms.Elementwise Topology
set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxSynthPendingDepth 26
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)] {d : Data dim} {x : X dim}

theorem conormalTaylorSolutions_remainder_eqOn_of_coefficientEq
    {A C : X dim → Mat dim} (hA : ContDiff ℝ ∞ A) (hC : ContDiff ℝ ∞ C)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} {f g : SmoothData dim}
    (U : ConormalTaylorSolutions A ell f) (V : ConormalTaylorSolutions C ell g)
    (hAC : EqOn A C (ball (0:X dim) 1)) (hfg : EqOn f.1 g.1 (standardSphere dim)) (r : ℝ) :
    EqOn (U.remainder hA r).1 (V.remainder hC r).1 (standardSphere dim) := by
  let V' : ConormalTaylorSolutions A ell g := ⟨V.actual,V.flat,V.first,V.actualTrace,
    fun z hz => by
      have hEq : A =ᶠ[𝓝 z] C := by
        filter_upwards [isOpen_ball.mem_nhds hz] with p hp using hAC hp
      exact (negativeBallDivergence_congr_germ hEq EventuallyEq.rfl).trans (V.actualEquation hz),
    V.flatTrace,V.flatEquation,V.firstTrace,V.firstEquation⟩
  have hClosed : EqOn A C (closedBall (0:X dim) 1) := by
    rw [← closure_ball _ (by norm_num : (1:ℝ) ≠ 0)]
    exact hAC.closure hA.continuous hC.continuous
  intro z hz
  refine (conormalTaylorSolutions_remainder_eqOn hA hEll U V' hfg r hz).trans ?_
  change smoothBallConormal A V.actual.1 z-(V.degree.1 z)-r*V.affineConormal.1 z =
    smoothBallConormal C V.actual.1 z-(V.degree.1 z)-r*V.affineConormal.1 z
  have hF : smoothBallFlux A V.actual.1 z = smoothBallFlux C V.actual.1 z := by
    ext i
    simp only [smoothBallFlux_apply,hClosed (sphere_subset_closedBall hz)]
  rw [smoothBallConormal,smoothBallConormal,hF]

namespace ActualGaussFiberData
variable (D : ActualGaussFiberData d x)

@[expose] def conormalRemainder : Module.End ℝ (SmoothSphereTrace dim) :=
  let R := smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve
  let L := affineDensityMul d x
  let B := D.flatDegree
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  smoothSphereTraceMul D.weight * ((LinearMap.fst ℝ _ _).comp R)-B-d.radius x • (L*B+Q)

theorem conormalRemainder_apply (f : SmoothData dim) :
    D.conormalRemainder (smoothSphereTrace f) =
      smoothSphereTrace ((D.solve f).remainder D.smoothCoefficient (d.radius x)) := by
  symm
  exact smoothSphereTaylorResponse_remainder D.smoothCoefficient D.ellipticCoefficient D.solve
    D.weight D.weightConormal (d.radius x) f

theorem conormalRemainder_eq_of_actual {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A (firstDensityCenterLinear d x) f)
    (hAeq : EqOn A (fun z => firstNormalVelocityCoefficient d x
      (d.radius x • frameVector d.frame x z)) (ball (0:X dim) 1))
    (T : Module.End ℝ (SmoothSphereTrace dim))
    (hT : ∀ f,T (smoothSphereTrace f) = smoothSphereTrace ((S f).remainder hA (d.radius x))) :
    D.conormalRemainder = T := by
  apply LinearMap.ext
  intro u
  obtain ⟨f,rfl⟩ := smoothSphereTraceL_surjective u
  let g : SmoothData dim := ⟨f.1,smoothBallData_contDiff f⟩
  change D.conormalRemainder (smoothSphereTrace g) = T (smoothSphereTrace g)
  rw [D.conormalRemainder_apply,hT g,smoothSphereTrace_eq_iff]
  exact conormalTaylorSolutions_remainder_eqOn_of_coefficientEq D.smoothCoefficient hA
    D.ellipticCoefficient (D.solve g) (S g) (D.coefficientEq.trans hAeq.symm) (fun _ _ => rfl) (d.radius x)

theorem responseRemainder_eq_conormal (hr : d.radius x ≠ 0) :
    let r := d.radius x
    let B := D.flatDegree
    let L := affineDensityMul d x
    let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp
      (smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve))
    let H := smoothSphereTraceMul D.reciprocal
    let H₂ := (r^2)⁻¹ • (H-1+r • L)
    D.responseRemainder = B*H₂+(L*B+Q)*(-L+r • H₂)+
      ((r^2)⁻¹ • D.conormalRemainder)*H := by
  dsimp only
  let r := d.radius x
  let B := D.flatDegree
  let L := affineDensityMul d x
  let R := smoothSphereTaylorResponses D.smoothCoefficient D.ellipticCoefficient D.solve
  let Q := (LinearMap.snd ℝ _ _).comp ((LinearMap.snd ℝ _ _).comp R)
  let H := smoothSphereTraceMul D.reciprocal
  let H₂ := (r^2)⁻¹ • (H-1+r • L)
  let C := smoothSphereTraceMul D.weight * ((LinearMap.fst ℝ _ _).comp R)
  let E := (r^2)⁻¹ • D.conormalRemainder
  have hr₂ : r^2 ≠ 0 := pow_ne_zero 2 hr
  have hC : B+r • (L*B+Q)+r^2 • E = C := by
    change B+r • (L*B+Q)+r^2 • ((r^2)⁻¹ • (C-B-r • (L*B+Q))) = C
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have hH : 1-r • L+r^2 • H₂ = H := by
    change 1-r • L+r^2 • ((r^2)⁻¹ • (H-1+r • L)) = H
    rw [smul_smul,mul_inv_cancel₀ hr₂,one_smul]
    abel
  have h := conormal_times_inverseWeight_expansion B L Q E H₂ r
  dsimp only at h
  rw [hC,hH] at h
  change (r^2)⁻¹ • (C*H-B-r • (Q-(B*L-L*B))) =
    B*H₂+(L*B+Q)*(-L+r • H₂)+E*H
  rw [h,show ∀ J F : Module.End ℝ (SmoothSphereTrace dim), B+r • F+r^2 • J-B-r • F = r^2 • J
      from fun J F => by abel,smul_smul,inv_mul_cancel₀ hr₂,one_smul]

end ActualGaussFiberData
end CalderonN
