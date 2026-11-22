module

public import Proof.CalderonN.RelativeRadiusCoefficientFamily
public import Proof.CalderonN.AngleLowJetDerivative
public import Proof.CalderonN.NormalizedStrongPoissonTaylor

import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option maxHeartbeats 3500000
set_option maxSynthPendingDepth 27
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

private theorem exists_relativeRadius_operator_comparison
    (d : Data dim) (y : X dim) (F F1 : SmoothCoefficientMatrix dim 2) (Q : ℝ) (hQ : 0 ≤ Q)
    (hF : EqOn (coefficientMatrixField 2 F)
      (fun z => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z))
      (ball (0 : X dim) (5/4)))
    (hF1 : EqOn (coefficientMatrixField 2 F1)
      (fun z => firstDensityCenterLinear d y z • (1 : Mat dim)) (ball (0 : X dim) (5/4)))
    (hJet : let R := fun z => deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
        (d.radius y*firstDensityCenterLinear d y z) • (1 : Mat dim)
      ∀ z ∈ ball (0 : X dim) 2, ContDiffAt ℝ ∞ R z ∧ ‖R z‖ ≤ Q*(d.radius y)^2 ∧
        ‖fderiv ℝ R z‖ ≤ Q*(d.radius y)^2) :
    ∃ a : ℝ × X dim → Mat dim, ∃ ha : ContDiff ℝ ∞ a,
      ∃ K : Set (X dim), ∃ hK : IsCompact K, ∃ hS : ∀ t z, z ∉ K → a (t,z) = 0,
      let A := commonSupportMatrixFamily 2 a ha K hK hS
      A 0 = F ∧
      (∀ t ∈ ball (0 : ℝ) (1/16), ∀ z ∈ ball (0 : X dim) (9/8),
        a (t,z) = relativeRadiusCoefficient d y t z) ∧
      ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (A t) -
          ((1+t)*d.radius y) • strongDirichletOperator fixedSobolevCalculus 0 F1) 0‖ ≤
        (2*strongC1OperatorBudget (fixedSobolevCalculus (dim := dim))*Q)*(d.radius y)^2 ∧
      ‖fderiv ℝ (fun t => fullBallDivergenceL 0 (A t) -
          ((1+t)*d.radius y) • fullBallDivergenceL 0 F1) 0‖ ≤
        (2*fullC1OperatorBudget (dim := dim)*Q)*(d.radius y)^2 := by
  obtain ⟨a,ha,K,hK,hS,hA,hReal⟩ := exists_relativeRadius_coefficientFamily d y F hF
  obtain ⟨g,hg,J,hJ,hgS,hgE,_⟩ := exists_constantFamily_of_coefficientMatrix 2 F1
  let g1 := coefficientMatrixField 2 F1
  have hg1 : ContDiff ℝ ∞ g1 := by
    rw [hgE] at hg
    exact hg.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  have hg1S (z : X dim) (hz : z ∉ J) : g1 z = 0 := by
    simpa only [hgE,Function.comp_apply,g1] using hgS 0 z hz
  let r := d.radius y
  let R (z : X dim) := deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
    (r*firstDensityCenterLinear d y z) • (1 : Mat dim)
  let S := K ∪ J
  let δ : ℝ × X dim → Mat dim := fun p => a p - ((1+p.1)*r) • g1 p.2
  have hδ : ContDiff ℝ ∞ δ :=
    ha.sub (((contDiff_const.add contDiff_fst).mul contDiff_const).smul (hg1.comp contDiff_snd))
  have hSK : IsCompact S := hK.union hJ
  have hδS (t : ℝ) (z : X dim) (hz : z ∉ S) : δ (t,z) = 0 := by
    change a (t,z)-((1+t)*r) • g1 z = 0
    rw [hS t z (fun h => hz (Or.inl h)),hg1S z (fun h => hz (Or.inr h)),smul_zero,sub_zero]
  let A := commonSupportMatrixFamily 2 a ha K hK hS
  let E := commonSupportMatrixFamily 2 δ hδ S hSK hδS
  have hEq (t : ℝ) : E t = A t - ((1+t)*r) • F1 := by
    apply coefficientMatrixField_injective 2
    rw [show coefficientMatrixField 2 (E t) = fun z => δ (t,z) from
      coefficientMatrixField_commonSupportMatrixFamily _ _ hδ _ hSK hδS t]
    have hAt := coefficientMatrixField_commonSupportMatrixFamily 2 a ha K hK hS t
    funext z
    ext i j
    change a (t,z) i j - ((1+t)*r)*(g1 z i j) =
      coefficientMatrixField 2 (A t) z i j - ((1+t)*r)*(g1 z i j)
    rw [show coefficientMatrixField 2 (A t) z i j = a (t,z) i j from
      congrArg (fun f => f z i j) hAt]
  let b (z : X dim) := fderiv ℝ δ ((0:ℝ),z) (1,0)
  have hb : ContDiff ℝ ∞ b :=
    ((hδ.fderiv_right (m := ∞) (by simp)).comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  have hCurve (z : X dim) : HasDerivAt (fun t : ℝ => (t,z)) (1,0) 0 := by
    simpa only [id_eq] using (hasDerivAt_id (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) z)
  have hGen (z : X dim) : HasDerivAt (fun t => δ (t,z)) (b z) 0 := by
    have h := (hδ.differentiable (by simp) ((0:ℝ),z)).hasFDerivAt.comp_hasDerivAt 0 (hCurve z)
    simpa only [Function.comp_def,b] using h
  have hB (z : X dim) (hz : z ∈ ball (0 : X dim) (9/8)) : b z = R z := by
    have hA' : HasDerivAt (fun t => a (t,z)) (fderiv ℝ a ((0:ℝ),z) (1,0)) 0 :=
      (ha.differentiable (by simp) ((0:ℝ),z)).hasFDerivAt.comp_hasDerivAt 0 (hCurve z)
    have hC : HasDerivAt (fun t : ℝ => ((1+t)*r) • g1 z) (r • g1 z) 0 := by
      have h := (((hasDerivAt_id (0:ℝ)).const_add 1).mul_const r).smul_const (g1 z)
      simpa only [id_eq,one_mul] using h
    have hD := hA'.sub hC
    change HasDerivAt (fun t => δ (t,z)) (fderiv ℝ a ((0:ℝ),z) (1,0) - r • g1 z) 0 at hD
    rw [(hGen z).unique hD]
    have he : (fun t => a (t,z)) =ᶠ[𝓝 (0:ℝ)] (fun t => relativeRadiusCoefficient d y t z) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0:ℝ) < 1/16))] with t ht
      exact hReal t ht z hz
    have hD' : HasDerivAt (fun t => a (t,z)) (fderiv ℝ a ((0:ℝ),z) (1,0)) 0 := hA'
    rw [← hD'.deriv,he.deriv_eq]
    change deriv (fun t => relativeRadiusCoefficient d y t z) 0 -
      r • coefficientMatrixField 2 F1 z = R z
    rw [hF1 (ball_subset_ball (by norm_num : (9/8:ℝ) ≤ 5/4) hz)]
    simp only [R,smul_smul]
  have hzOf (z : X dim) (hz : z ∈ fixedBallOpens dim) : z ∈ ball (0 : X dim) (9/8) :=
    ball_subset_ball (by norm_num : (1:ℝ) ≤ 9/8) hz
  have hzOf' (z : X dim) (hz : z ∈ fixedBallOpens dim) : z ∈ ball (0 : X dim) 2 :=
    ball_subset_ball (by norm_num : (1:ℝ) ≤ 2) hz
  have hValue (z : X dim) (hz : z ∈ fixedBallOpens dim) : ‖b z‖ ≤ Q*r^2 := by
    rw [hB z (hzOf z hz)]
    exact (hJet z (hzOf' z hz)).2.1
  have hSpatial (z : X dim) (hz : z ∈ fixedBallOpens dim) : ‖fderiv ℝ b z‖ ≤ Q*r^2 := by
    have hn : b =ᶠ[𝓝 z] R := by
      filter_upwards [isOpen_ball.mem_nhds (hzOf z hz)] with w hw using hB w hw
    rw [hn.fderiv_eq]
    exact (hJet z (hzOf' z hz)).2.2
  have hh := norm_fderiv_angle_commonSupport_operators_le fixedSobolevCalculus δ hδ S hSK hδS
    b (hb.differentiable (by simp)) hGen (Q*r^2) (by positivity) hValue hSpatial
  have hStrong (t : ℝ) : strongDirichletOperator fixedSobolevCalculus 0 (E t) =
      strongDirichletOperator fixedSobolevCalculus 0 (A t) -
        ((1+t)*r) • strongDirichletOperator fixedSobolevCalculus 0 F1 := by
    rw [hEq]
    let L := strongCoefficientOperatorL (dim := dim) fixedSobolevCalculus 0
    change L (A t - ((1+t)*r) • F1) = _
    rw [map_sub,map_smul]
    rfl
  have hFull (t : ℝ) : fullBallDivergenceL 0 (E t) =
      fullBallDivergenceL 0 (A t) - ((1+t)*r) • fullBallDivergenceL 0 F1 := by
    rw [hEq,← fullBallCoefficientOperatorL_apply,← fullBallCoefficientOperatorL_apply,
      ← fullBallCoefficientOperatorL_apply,map_sub,map_smul]
  refine ⟨a,ha,K,hK,hS,hA,hReal,?_,?_⟩
  · rw [← funext hStrong]
    exact hh.1.trans_eq (by ring)
  · rw [← funext hFull]
    exact hh.2.trans_eq (by ring)

/-- The strong and full Dirichlet operators for the genuine moving
coefficient have quadratic first-variation errors under a relative
radius derivative, using the local coefficient value and first jet. -/
theorem uniform_relativeRadius_strong_coefficient (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} (hm : 4 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η BS BF : ℝ, 0 < η ∧ 0 ≤ BS ∧ 0 ≤ BF ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y, ∀ F F1 : SmoothCoefficientMatrix dim 2,
      EqOn (coefficientMatrixField 2 F)
        (fun z => firstNormalVelocityCoefficient d y (d.radius y • frameVector d.frame y z))
        (ball (0 : X dim) (5/4)) →
      EqOn (coefficientMatrixField 2 F1)
        (fun z => firstDensityCenterLinear d y z • (1 : Mat dim)) (ball (0 : X dim) (5/4)) →
      ∃ a : ℝ × X dim → Mat dim, ∃ ha : ContDiff ℝ ∞ a,
      ∃ J : Set (X dim), ∃ hJ : IsCompact J, ∃ hS : ∀ t z, z ∉ J → a (t,z) = 0,
      let A := commonSupportMatrixFamily 2 a ha J hJ hS
      A 0 = F ∧
      (∀ t ∈ ball (0 : ℝ) (1/16), ∀ z ∈ ball (0 : X dim) (9/8),
        a (t,z) = relativeRadiusCoefficient d y t z) ∧
      ‖fderiv ℝ (fun t => strongDirichletOperator fixedSobolevCalculus 0 (A t) -
        ((1+t)*d.radius y) • strongDirichletOperator fixedSobolevCalculus 0 F1) 0‖ ≤ BS*(d.radius y)^2 ∧
      ‖fderiv ℝ (fun t => fullBallDivergenceL 0 (A t) -
        ((1+t)*d.radius y) • fullBallDivergenceL 0 F1) 0‖ ≤ BF*(d.radius y)^2 := by
  obtain ⟨η,Q,hη,hQ,hR⟩ := uniform_relativeRadius_coefficient_jet (Y := Y) hn hΩ hm K ρ c₀ M Cj hK hρ
  let B := strongC1OperatorBudget (fixedSobolevCalculus (dim := dim))
  let C := fullC1OperatorBudget (dim := dim)
  have hB : 0 ≤ B := strongC1OperatorBudget_nonneg _
  have hC : 0 ≤ C := fullC1OperatorBudget_nonneg
  refine ⟨η,2*B*Q,2*C*Q,hη,by positivity,by positivity,?_⟩
  intro floor hf ε hε hεη d hd y hy F F1 hF hF1
  exact exists_relativeRadius_operator_comparison d y F F1 Q hQ hF hF1
    (hR floor hf ε hε hεη d hd y hy)

end CalderonN
