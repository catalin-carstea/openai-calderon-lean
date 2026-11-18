import Proof.JointFramedNormalRegularity
import Proof.PullbackDirichletCoefficient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 20
open Set
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.EnergyBridge
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

lemma contDiffAt_matrix_det_entries (A : P → Mat) (p : P)
    (hA : ∀ i j,ContDiffAt ℝ ∞ (fun x => A x i j) p) :
    ContDiffAt ℝ ∞ (fun x => (A x).det) p := by
  classical
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum (fun σ _ => contDiffAt_const.mul (contDiffAt_prod (fun i _ => hA (σ i) i)))

lemma contDiffAt_matrix_density_inverse_entry (A : P → Mat) (p : P)
    (hA : ∀ i j,ContDiffAt ℝ ∞ (fun x => A x i j) p)
    (hPos : 0 < (A p).det) (i j : I) :
    ContDiffAt ℝ ∞ (fun x => Real.sqrt (A x).det*(A x)⁻¹ i j) p := by
  have hDet := contDiffAt_matrix_det_entries A p hA
  have hAdj : ContDiffAt ℝ ∞ (fun x => (A x).adjugate i j) p := by
    classical
    simp_rw [Matrix.adjugate_apply]
    apply contDiffAt_matrix_det_entries (fun x => (A x).updateRow j (Pi.single i 1)) p
    intro a b
    by_cases ha : a = j
    · subst a
      simp only [Matrix.updateRow_self]
      exact contDiffAt_const
    · simpa only [Matrix.updateRow_apply,ha,ite_false] using hA a b
  have hInv : ContDiffAt ℝ ∞ (fun x => (A x)⁻¹ i j) p := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv',Matrix.smul_apply,smul_eq_mul]
    exact (hDet.inv hPos.ne').mul hAdj
  exact (hDet.sqrt hPos.ne').mul hInv

/-- Joint regularity of the true normalized divergence coefficient, before
    choosing any compact coefficient representatives. -/
theorem uniform_framed_normal_coefficient_joint_regular {Y Ω : Set X} (hY : IsOpen Y) (hΩ : IsOpen Ω)
    {m : ℕ} (hm : 2 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η : ℝ,0 < η ∧ ∀ floor,1 ≤ floor → ∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ y ∈ Y,
      ∀ g ∈ ({d.γ,d.g₁} : Set MetricField),∀ z ∈ Metric.closedBall (0:X) L,∀ i j,
      ContDiffAt ℝ ∞ (fun p : X × X => principalCoefficient
        (framedNormalMetric g d.frame d.expMap p.1 (d.radius p.1)) p.2 i j) (y,z) := by
  obtain ⟨ηR,hηR,hRegular⟩ := uniform_framed_normal_metric_joint_regular hY hΩ hm K ρ c₀ M Cj hK hρ L hL
  obtain ⟨ηE,hηE,hElliptic⟩ := uniform_enlarged_framed_normal_elliptic
    (Y:=Y) hΩ hm K ρ c₀ M Cj hK hρ L hL
  refine ⟨min ηR ηE,lt_min hηR hηE,?_⟩
  intro floor hf ε hε hSmall d hd y hy g hmem z hz i j
  have hSmooth := hRegular floor hf ε hε (hSmall.trans (min_le_left _ _)) d hd y hy g hmem z hz
  have hEll := hElliptic floor hf ε hε (hSmall.trans (min_le_right _ _)) d hd y hy g hmem
  exact contDiffAt_matrix_density_inverse_entry
    (fun p : X × X => framedNormalMetric g d.frame d.expMap p.1 (d.radius p.1) p.2)
    (y,z) hSmooth (hEll.posDef (by have hKpos : 0 < K := zero_lt_one.trans_le hK;positivity) hz).det_pos i j

end ShrinkingSpheres
