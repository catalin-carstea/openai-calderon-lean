import Proof.CompactFiniteJetBound
import Proof.FiniteJetBoundCalculus
import Proof.NormalFrameMatrixInputJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 30
open Set Filter
open scoped ContDiff Topology
namespace ShrinkingSpheres

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def radialDilationInput (q : (P × ℝ) × ℝ) : P × ℝ := (q.1.1,(1+q.1.2)*q.2)

lemma contDiff_radialDilationInput : ContDiff ℝ ∞ (radialDilationInput (P:=P)) :=
  contDiff_fst.fst.prodMk ((contDiff_const.add contDiff_fst.snd).mul contDiff_snd)

lemma radialDilationInput_zero_parameter (p : P) (r : ℝ) :
    radialDilationInput ((p,0),r) = (p,r) := by simp only [radialDilationInput,add_zero,one_mul]

def radialDilationScalarInputL : ((P × ℝ) × ℝ) →L[ℝ] (ℝ × ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun q => (q.1.2,q.2)
      map_add' := by intro a b;rfl
      map_smul' := by intro c a;rfl }
    1 (by
      intro q
      change ‖(q.1.2,q.2)‖ ≤ 1*‖q‖
      simpa only [Prod.norm_def,one_mul] using max_le ((norm_snd_le q.1).trans (norm_fst_le q)) (norm_snd_le q))

lemma norm_radialDilationScalarInputL_le_one : ‖radialDilationScalarInputL (P:=P)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

def universalRadialDilation (q : ℝ × ℝ) : ℝ := (1+q.1)*q.2

lemma contDiff_universalRadialDilation : ContDiff ℝ ∞ universalRadialDilation :=
  (contDiff_const.add contDiff_fst).mul contDiff_snd

/-- All positive jets of the relative-radius input are bounded independently
    of the size of its parameter value. Only the fixed scalar polynomial
    is bounded on a compact set. -/
theorem uniform_radialDilationInput_positive_jet_bounds (N : ℕ) :
    ∃ D : ℝ,1 ≤ D ∧ ∀ p : P,∀ r : ℝ,|r| ≤ 1 → ∀ n : ℕ,1 ≤ n → n ≤ N →
      ‖iteratedFDeriv ℝ n (radialDilationInput (P:=P)) ((p,0),r)‖ ≤ D := by
  obtain ⟨C,hC,hScalar⟩ := exists_finite_jet_bound_on_compact universalRadialDilation
    (Metric.closedBall (0:ℝ × ℝ) 1) (isCompact_closedBall _ _)
    (fun _ _ => contDiff_universalRadialDilation.contDiffAt) N
  let D := 1+(N.factorial:ℝ)*C
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD : 1 ≤ D := by
    have hh : 0 ≤ (N.factorial:ℝ)*C := by positivity
    dsimp only [D]
    linarith only [hh]
  refine ⟨D,hD,?_⟩
  intro p r hr n hn hnN
  let x : (P × ℝ) × ℝ := ((p,0),r)
  have hMem : radialDilationScalarInputL x ∈ Metric.closedBall (0:ℝ × ℝ) 1 := by
    change (0,r) ∈ Metric.closedBall (0:ℝ × ℝ) 1
    simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,norm_zero,Real.norm_eq_abs,
      max_eq_right (abs_nonneg r)] using hr
  have hh := iteratedFDeriv_comp_common_bound (radialDilationScalarInputL (P:=P)) universalRadialDilation x
    (radialDilationScalarInputL (P:=P)).contDiff.contDiffAt contDiff_universalRadialDilation.contDiffAt N C 1 hC0 le_rfl
    (fun j hj => hScalar j hj _ hMem)
    (fun j hj _ => norm_iteratedFDeriv_clm_le_one (radialDilationScalarInputL (P:=P))
      (norm_radialDilationScalarInputL_le_one (P:=P)) x j hj) n hnN
  simp only [one_pow,mul_one] at hh
  have hRadius : ContDiffAt ℝ ∞ (fun q : (P × ℝ) × ℝ => (1+q.1.2)*q.2) x :=
    (contDiffAt_const.add contDiffAt_fst.snd).mul contDiffAt_snd
  let pi : ((P × ℝ) × ℝ) →L[ℝ] P :=
    (ContinuousLinearMap.fst ℝ P ℝ).comp (ContinuousLinearMap.fst ℝ (P × ℝ) ℝ)
  have hpi : ‖pi‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change ‖q.1.1‖ ≤ 1*‖q‖
    simpa only [one_mul] using (norm_fst_le q.1).trans (norm_fst_le q)
  change ‖iteratedFDeriv ℝ n (fun q : (P × ℝ) × ℝ => (q.1.1,(1+q.1.2)*q.2)) x‖ ≤ D
  rw [iteratedFDeriv_prodMk contDiffAt_fst.fst hRadius (i:=n) (by simp),ContinuousMultilinearMap.opNorm_prod]
  exact max_le ((norm_iteratedFDeriv_clm_le_one pi hpi x n hn).trans hD)
    (hh.trans (by change (N.factorial:ℝ)*C ≤ D;dsimp only [D];linarith))

end ShrinkingSpheres
