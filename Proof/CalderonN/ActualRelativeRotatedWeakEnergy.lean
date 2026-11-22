module

public import Proof.CalderonN.ActualRelativeWeakEnergyGerm
public import Proof.CalderonN.ParametricBallRotationCoefficientJets

import Proof.CalderonN.BallRotationCoefficientBounds
import Mathlib.Tactic

/-! The exact rotated coefficients of the relative-radius energy family.
Both coefficient jets retain the affine and quadratic radius factors. -/

public section

noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4250000
set_option maxSynthPendingDepth 28
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE OAI.AnisotropicCalderon.SmoothSphereRotation
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem ballRotationCoefficient_congrOn_open (i j : I dim) {a c : X dim → Mat dim}
    {V : Set (X dim)} (hV : IsOpen V) (hEq : EqOn a c V) :
    EqOn (ballRotationCoefficient i j a) (ballRotationCoefficient i j c) V := by
  intro z hz
  have h : a =ᶠ[𝓝 z] c := by
    filter_upwards [hV.mem_nhds hz] with w hw using hEq hw
  simp only [ballRotationCoefficient,h.fderiv_eq,hEq hz]

omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem ballRotationCoefficient_factored (i j : I dim) {a b : X dim → Mat dim}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (r s : ℝ) :
    ballRotationCoefficient i j (fun z => 1+r • a z+s • b z) =
      fun z => r • ballRotationCoefficient i j a z+s • ballRotationCoefficient i j b z := by
  funext z
  let J := ballRotationGeneratorL i j
  let L := coordinateMatrix J
  have ha' := (ha.differentiable (by simp) z).hasFDerivAt.const_smul r
  have hb' := (hb.differentiable (by simp) z).hasFDerivAt.const_smul s
  have hD : fderiv ℝ (fun z => 1+r • a z+s • b z) z = r • fderiv ℝ a z+s • fderiv ℝ b z :=
    ((ha'.const_add (1:Mat dim)).add hb').fderiv
  simp only [ballRotationCoefficient,hD,add_apply,smul_apply,
    mul_add,add_mul,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,smul_sub,smul_add]
  abel

omit [NeZero dim] [Nontrivial (Fin dim)] in
theorem ballRotationCoefficient_scalarAffine (i j : I dim) (ell : X dim →L[ℝ] ℝ) (c : ℝ) :
    ballRotationCoefficient i j (fun z => c • (ell z • (1:Mat dim))) =
      fun z => c • ((ell.comp (ballRotationGeneratorL i j)) z • (1:Mat dim)) := by
  funext z
  let M := ell.smulRight (1:Mat dim)
  have hD : fderiv ℝ (fun z => c • (ell z • (1:Mat dim))) z = c • M :=
    (c • M).fderiv
  simp only [ballRotationCoefficient,hD,M,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    smul_mul_assoc,mul_smul_comm,one_mul,mul_one,add_sub_cancel_right]

structure ActualRelativeRotatedWeakEnergyGerm (d : Data dim) (y : X dim) (N : ℕ) (C : ℝ) where
  first : X dim × ℝ → FixedBallEnergyOperator dim
  second : X dim × ℝ → FixedBallEnergyOperator dim
  rotFirst : I dim → I dim → X dim × ℝ → FixedBallEnergyOperator dim
  rotSecond : I dim → I dim → X dim × ℝ → FixedBallEnergyOperator dim
  neighborhood : Set (X dim × ℝ)
  openNeighborhood : IsOpen neighborhood
  center_mem : (y,0) ∈ neighborhood
  energy_eq : ∀ p ∈ neighborhood, ∀ u v : FixedBallH1 dim,
    (fixedBallFlatEnergyL dim+d.radius y • first p+(d.radius y)^2 • second p) u v =
      energyFormH1 (fun z => actualFramedCoefficientField d
        (actualRelativeCoefficientInput (d.radius y) (p,z))) 0 0 u v
  rotFirst_eq : ∀ i j p, p ∈ neighborhood → ∀ u v : FixedBallH1 dim, rotFirst i j p u v =
    energyFormH1 (fun z => (1+p.2) • (((firstDensityCenterLinear d p.1).comp
      (ballRotationGeneratorL i j)) z • (1:Mat dim))) 0 0 u v
  rotEnergy_eq : ∀ i j p, p ∈ neighborhood → ∀ u v : FixedBallH1 dim,
    (d.radius y • rotFirst i j p+(d.radius y)^2 • rotSecond i j p) u v =
      energyFormH1 (ballRotationCoefficient i j (fun z => actualFramedCoefficientField d
        (actualRelativeCoefficientInput (d.radius y) (p,z)))) 0 0 u v
  firstBound : LocalSmoothJetBudget first (y,0) N C
  secondBound : LocalSmoothJetBudget second (y,0) N C
  rotFirstBound : ∀ i j, LocalSmoothJetBudget (rotFirst i j) (y,0) N C
  rotSecondBound : ∀ i j, LocalSmoothJetBudget (rotSecond i j) (y,0) N C

theorem uniform_actual_relativeRotatedWeakEnergy_germ (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+5 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, Nonempty (ActualRelativeRotatedWeakEnergyGerm d y N C) := by
  obtain ⟨η,C₁,C₂,hη,hC₁,hC₂,hRel⟩ := uniform_actual_relativeCoefficient_germs hn hY hΩ hYc
    (N+1) (by omega) K ρ c₀ M Cj hK hρ
  obtain ⟨A,hA,hRotate⟩ := uniform_parametricBallRotationCoefficient_jet_budget (dim:=dim) (P:=X dim × ℝ) N
  let L := fixedBallWeakEnergyJetBudget dim
  let D := L*(max 1 A*(C₁+C₂))
  have hL : 0 ≤ L := by dsimp only [L,fixedBallWeakEnergyJetBudget]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hBound (C : ℝ) (hC : 0 ≤ C) (h : C ≤ C₁+C₂) : L*C ≤ D :=
    mul_le_mul_of_nonneg_left (h.trans (le_mul_of_one_le_left (add_nonneg hC₁ hC₂) (le_max_left _ _))) hL
  have hBoundR (C : ℝ) (hC : 0 ≤ C) (h : C ≤ C₁+C₂) : L*(A*C) ≤ D :=
    mul_le_mul_of_nonneg_left (mul_le_mul (le_max_right _ _) h hC
      (zero_le_one.trans (le_max_left _ _))) hL
  refine ⟨η,D,hη,hD,?_⟩
  intro floor hf ε he hs d hd hF y hy
  obtain ⟨a,b,J,W,ha,hb,hJ,hSupp,hW,hKW,hOne,_,hAeq,hJet⟩ := hRel floor hf ε he hs d hd hF y hy
  let p₀ : X dim × ℝ := (y,0)
  let r := d.radius y
  obtain ⟨V,Z,hV,_,hpV,hCZ,hVZ⟩ := generalized_tube_lemma
    (isCompact_singleton (x:=p₀)) (isCompact_closedBall (0:X dim) 1) hW hKW
  have has (p : X dim × ℝ) : ContDiff ℝ ∞ (fun z => a (p,z)) := ha.comp (contDiff_const.prodMk contDiff_id)
  have hbs (p : X dim × ℝ) : ContDiff ℝ ∞ (fun z => b (p,z)) := hb.comp (contDiff_const.prodMk contDiff_id)
  let aR (i j : I dim) := parametricBallRotationCoefficient i j a
  let bR (i j : I dim) := parametricBallRotationCoefficient i j b
  have haR (i j : I dim) := contDiff_parametricBallRotationCoefficient i j ha
  have hbR (i j : I dim) := contDiff_parametricBallRotationCoefficient i j hb
  let S (c : FramedRadialParameter dim → Mat dim) (hc : ContDiff ℝ ∞ c) (p : X dim × ℝ) :=
    fixedBallSmoothEnergyL (hc.continuous.comp (continuous_const.prodMk continuous_id) :
      Continuous (fun z => c (p,z)))
  let E₁ := S a ha
  let E₂ := S b hb
  let T₁ (i j : I dim) := S (aR i j) (haR i j)
  let T₂ (i j : I dim) := S (bR i j) (hbR i j)
  have hS₁ (p : X dim × ℝ) (z : X dim) (hz : z ∉ J) := (hSupp p z hz).1
  have hS₂ (p : X dim × ℝ) (z : X dim) (hz : z ∉ J) := (hSupp p z hz).2
  have hb₁ : LocalSmoothJetBudget E₁ p₀ N D := (local_fixedBallWeakEnergy_jet_budget a ha J hJ hS₁
    p₀ N C₁ hC₁ (fun z hz => (hJet z hz).1.mono_order (Nat.le_succ _))).enlarge
      (hBound _ hC₁ (le_add_of_nonneg_right hC₂))
  have hb₂ : LocalSmoothJetBudget E₂ p₀ N D := (local_fixedBallWeakEnergy_jet_budget b hb J hJ hS₂
    p₀ N C₂ hC₂ (fun z hz => (hJet z hz).2.mono_order (Nat.le_succ _))).enlarge
      (hBound _ hC₂ (le_add_of_nonneg_left hC₁))
  have ht₁ (i j : I dim) : LocalSmoothJetBudget (T₁ i j) p₀ N D :=
    (local_fixedBallWeakEnergy_jet_budget (aR i j) (haR i j) J hJ
      (fun p z hz => parametricBallRotationCoefficient_support i j hJ.isClosed hS₁ p hz)
      p₀ N (A*C₁) (by positivity) (fun z hz => hRotate i j a ha p₀ z hz _ (hJet z hz).1)).enlarge
      (hBoundR _ hC₁ (le_add_of_nonneg_right hC₂))
  have ht₂ (i j : I dim) : LocalSmoothJetBudget (T₂ i j) p₀ N D :=
    (local_fixedBallWeakEnergy_jet_budget (bR i j) (hbR i j) J hJ
      (fun p z hz => parametricBallRotationCoefficient_support i j hJ.isClosed hS₂ p hz)
      p₀ N (A*C₂) (by positivity) (fun z hz => hRotate i j b hb p₀ z hz _ (hJet z hz).2)).enlarge
      (hBoundR _ hC₂ (le_add_of_nonneg_left hC₁))
  refine ⟨⟨E₁,E₂,T₁,T₂,V,hV,hpV (mem_singleton _),?_,?_,?_,hb₁,hb₂,ht₁,ht₂⟩⟩
  · intro p hp u v
    let R (z : X dim) := 1+r • a (p,z)+r^2 • b (p,z)
    have hR : Continuous R := (continuous_const.add ((has p).continuous.const_smul r)).add
      ((hbs p).continuous.const_smul (r^2))
    have hOp : fixedBallSmoothEnergyL hR = fixedBallFlatEnergyL dim+r • E₁ p+r^2 • E₂ p := by
      have hFlat : Continuous (fun _ : X dim => (1:Mat dim)) := continuous_const
      rw [fixedBallSmoothEnergyL_add (hFlat.add ((has p).continuous.const_smul r)) ((hbs p).continuous.const_smul (r^2)),
        fixedBallSmoothEnergyL_add hFlat ((has p).continuous.const_smul r),
        fixedBallSmoothEnergyL_smul,fixedBallSmoothEnergyL_smul]
      rfl
    rw [← hOp]
    exact fixedBallSmoothEnergyL_eq_weak_of_eqOn hR
      (fun z hz => (hAeq (p,z) (hVZ ⟨hp,hCZ (ball_subset_closedBall hz)⟩)).symm) u v
  · intro i j p hp u v
    have hOne' : EqOn (fun z => a (p,z))
        (fun z => (1+p.2) • (firstDensityCenterLinear d p.1 z • (1:Mat dim))) (ball (0:X dim) 1) :=
      fun z hz => hOne (hVZ ⟨hp,hCZ (ball_subset_closedBall hz)⟩)
    apply fixedBallSmoothEnergyL_eq_weak_of_eqOn
    intro z hz
    change ballRotationCoefficient i j (fun z => a (p,z)) z = _
    rw [show ballRotationCoefficient i j (fun z => a (p,z)) z = _ from
      ballRotationCoefficient_congrOn_open i j isOpen_ball hOne' hz,ballRotationCoefficient_scalarAffine]
  · intro i j p hp u v
    let H := ballRotationCoefficient i j (fun z => 1+r • a (p,z)+r^2 • b (p,z))
    have h1 : Continuous (fun z => aR i j (p,z)) :=
      ((haR i j).comp (contDiff_const.prodMk contDiff_id)).continuous
    have h2 : Continuous (fun z => bR i j (p,z)) :=
      ((hbR i j).comp (contDiff_const.prodMk contDiff_id)).continuous
    have hH : Continuous H := contDiff_ballRotationCoefficient i j
      ((contDiff_const.add ((has p).const_smul r)).add ((hbs p).const_smul (r^2))) |>.continuous
    have hOp : fixedBallSmoothEnergyL hH = r • T₁ i j p+r^2 • T₂ i j p := by
      have hEq : H = (fun z => r • aR i j (p,z)+r^2 • bR i j (p,z)) :=
        ballRotationCoefficient_factored i j (has p) (hbs p) r (r^2)
      have hR : Continuous (fun z => r • aR i j (p,z)+r^2 • bR i j (p,z)) :=
        (h1.const_smul r).add (h2.const_smul (r^2))
      have hB : fixedBallSmoothEnergyL hH = fixedBallSmoothEnergyL hR := by
        ext u v : 2
        rw [fixedBallSmoothEnergyL_apply,fixedBallSmoothEnergyL_apply,hEq]
      rw [hB,fixedBallSmoothEnergyL_add (h1.const_smul r) (h2.const_smul (r^2)),
        fixedBallSmoothEnergyL_smul,fixedBallSmoothEnergyL_smul]
    rw [← hOp]
    apply fixedBallSmoothEnergyL_eq_weak_of_eqOn
    intro z hz
    exact ballRotationCoefficient_congrOn_open i j isOpen_ball
      (fun w hw => (hAeq (p,w) (hVZ ⟨hp,hCZ (ball_subset_closedBall hw)⟩)).symm) hz

end CalderonN
