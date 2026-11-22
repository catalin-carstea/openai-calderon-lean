module

public import Proof.CalderonN.ActualRelativeWeakEnergyJets
public import Proof.CalderonN.NativeWeakHarmonicResponse

import Mathlib.Tactic

/-! The actual weak fixed-ball energy has the same affine and quadratic
parameter coefficients as the normalized metric pullback. -/

public section

noncomputable section
open Set MeasureTheory Metric
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim]

abbrev FixedBallEnergyOperator (dim : ℕ) :=
  FixedBallH1 dim →L[ℝ] FixedBallH1 dim →L[ℝ] ℝ

theorem fixedBallSmoothEnergyL_eq_weak_of_eqOn {a b : X dim → Mat dim}
    (ha : Continuous a) (h : EqOn a b (fixedBallOpens dim : Set (X dim)))
    (u v : FixedBallH1 dim) :
    fixedBallSmoothEnergyL ha u v = energyFormH1 b 0 0 u v := by
  rw [fixedBallSmoothEnergyL_apply,energyFormH1_def,energyFormH1_def]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (fixedBallOpens dim).isOpen.measurableSet] with z hz
  rw [h hz]

theorem uniform_actual_relativeWeakEnergy_germ (hn : 2 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∃ (E₁ E₂ : X dim × ℝ → FixedBallEnergyOperator dim) (V : Set (X dim × ℝ)),
        IsOpen V ∧ (y,0) ∈ V ∧
        (∀ p ∈ V, ∀ u v : FixedBallH1 dim, E₁ p u v =
          energyFormH1 (fun z => actualRelativeCoefficientFirst d (p,z)) 0 0 u v) ∧
        (∀ p ∈ V, ∀ u v : FixedBallH1 dim,
          (fixedBallFlatEnergyL dim+(d.radius y) • E₁ p+(d.radius y)^2 • E₂ p) u v =
            energyFormH1 (fun z => actualFramedCoefficientField d
                (actualRelativeCoefficientInput (d.radius y) (p,z))) 0 0 u v) ∧
        LocalSmoothJetBudget E₁ (y,0) N C ∧ LocalSmoothJetBudget E₂ (y,0) N C := by
  obtain ⟨η,C₁,C₂,hη,hC₁,hC₂,hRel⟩ := uniform_actual_relativeCoefficient_germs
    hn hY hΩ hYc N hm K ρ c₀ M Cj hK hρ
  let D := fixedBallWeakEnergyJetBudget dim
  let C := D*(C₁+C₂)
  have hD : 0 ≤ D := by dsimp only [D,fixedBallWeakEnergyJetBudget]; positivity
  refine ⟨η,C,hη,mul_nonneg hD (add_nonneg hC₁ hC₂),?_⟩
  intro floor hf ε he hs d hd hdFrame y hy
  obtain ⟨a₁,a₂,J,W,ha₁,ha₂,hJ,hSupp,hW,hCW,hOne,_,hEq,hJet⟩ :=
    hRel floor hf ε he hs d hd hdFrame y hy
  let p₀ : X dim × ℝ := (y,0)
  let r := d.radius y
  let a₁p (p : X dim × ℝ) (z : X dim) := a₁ (p,z)
  let a₂p (p : X dim × ℝ) (z : X dim) := a₂ (p,z)
  have ha₁p (p : X dim × ℝ) : Continuous (a₁p p) := ha₁.continuous.comp (continuous_const.prodMk continuous_id)
  have ha₂p (p : X dim × ℝ) : Continuous (a₂p p) := ha₂.continuous.comp (continuous_const.prodMk continuous_id)
  let E₁ (p : X dim × ℝ) := fixedBallSmoothEnergyL (ha₁p p)
  let E₂ (p : X dim × ℝ) := fixedBallSmoothEnergyL (ha₂p p)
  obtain ⟨V,Z,hV,hZ,hpV,hCZ,hVZ⟩ := generalized_tube_lemma
    (isCompact_singleton (x:=p₀)) (isCompact_closedBall (0:X dim) 1) hW hCW
  have hSupp₁ (p : X dim × ℝ) (z : X dim) (hz : z ∉ J) := (hSupp p z hz).1
  have hSupp₂ (p : X dim × ℝ) (z : X dim) (hz : z ∉ J) := (hSupp p z hz).2
  have hE₁ : LocalSmoothJetBudget E₁ p₀ N (D*C₁) :=
    local_fixedBallWeakEnergy_jet_budget a₁ ha₁ J hJ hSupp₁ p₀ N C₁ hC₁ (fun z hz => (hJet z hz).1)
  have hE₂ : LocalSmoothJetBudget E₂ p₀ N (D*C₂) :=
    local_fixedBallWeakEnergy_jet_budget a₂ ha₂ J hJ hSupp₂ p₀ N C₂ hC₂ (fun z hz => (hJet z hz).2)
  refine ⟨E₁,E₂,V,hV,hpV (mem_singleton _),?_,?_,
    hE₁.enlarge (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hC₂) hD),
    hE₂.enlarge (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hC₁) hD)⟩
  · intro p hp u v
    exact fixedBallSmoothEnergyL_eq_weak_of_eqOn (ha₁p p)
      (fun z hz => hOne (hVZ ⟨hp,hCZ (ball_subset_closedBall hz)⟩)) u v
  · intro p hp u v
    let e₀ : X dim → Mat dim := fun _ => 1
    let a := e₀+r • a₁p p+r^2 • a₂p p
    have ha : Continuous a :=
      (continuous_const.add ((ha₁p p).const_smul r)).add ((ha₂p p).const_smul (r^2))
    have hE : fixedBallSmoothEnergyL ha = fixedBallFlatEnergyL dim+r • E₁ p+r^2 • E₂ p := by
      change fixedBallSmoothEnergyL
        ((continuous_const (y:=(1:Mat dim))).add ((ha₁p p).const_smul r) |>.add ((ha₂p p).const_smul (r^2))) = _
      have hc : Continuous (fun _ : X dim => (1:Mat dim)) := continuous_const
      have h₁ := fixedBallSmoothEnergyL_smul (ha₁p p) r
      have h₂ := fixedBallSmoothEnergyL_smul (ha₂p p) (r^2)
      rw [fixedBallSmoothEnergyL_add (hc.add ((ha₁p p).const_smul r)) ((ha₂p p).const_smul (r^2)),
        fixedBallSmoothEnergyL_add hc ((ha₁p p).const_smul r),h₁,h₂]
      rfl
    change (fixedBallFlatEnergyL dim+r • E₁ p+r^2 • E₂ p) u v = _
    refine (congrArg (fun E : FixedBallEnergyOperator dim => E u v) hE.symm).trans ?_
    apply fixedBallSmoothEnergyL_eq_weak_of_eqOn ha _ u v
    intro z hz
    exact (hEq (p,z) (hVZ ⟨hp,hCZ (ball_subset_closedBall hz)⟩)).symm

end CalderonN
