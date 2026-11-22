module

public import Proof.Manuscript.MovingTrace.ClassicalResidualReadout
public import Proof.CalderonN.LocalJetEnvelopeBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000

open CalderonN CalderonN.BallDirichlet Set Filter Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

namespace CalderonPaper

variable {dim : ℕ} [NeZero dim]
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Read the strong correction in ambient spatial jets along a smooth
angular chart, keeping geometry and angular derivatives in the same
Fréchet derivative. The bound uses operator-norm smoothness of the
closed-ball evaluation map. -/
theorem parametric_classicalBallRepresentative_angular_jets
    {V : Set P} (hV : IsOpen V)
    (w : E → X dim) (hw : ContDiff ℝ ∞ w)
    (hwB : ∀ x, w x ∈ closedBall (0 : X dim) 1)
    {K : Set E} (hK : IsCompact K) (k N : ℕ) :
    let s := k+N+dim+1
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (U : (s : ℕ) → P → StrongDirichletSpace dim s)
        (hU : ∀ s, ContDiffOn ℝ ∞ (U s) V)
        (hAgree : ∀ p ∈ V, ∀ s, strongDirichletProjectionL dim s (U s p) =
          strongDirichletProjectionL dim 0 (U 0 p)),
        ∃ b : P → X dim → ℝ, (∀ p, ContDiff ℝ ∞ (b p)) ∧
          (∀ p ∈ V, TauCeti.W1p.value
            (strongDirichletProjectionL dim 0 (U 0 p) : FixedBallH1 dim)
              =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] b p) ∧
          (∀ l : ℕ, ContDiffOn ℝ ∞ (fun q : P × X dim => iteratedFDeriv ℝ l (b q.1) q.2)
            (V ×ˢ closedBall (0 : X dim) 1)) ∧
          ∀ p ∈ V, ∀ x ∈ K, ∀ M : ℝ, 0 ≤ M →
            (∀ j ≤ N, ‖iteratedFDeriv ℝ j (U s) p‖ ≤ M) →
            ∀ j ≤ N, ‖iteratedFDeriv ℝ j
              (fun q : P × E => iteratedFDeriv ℝ k (b q.1) (w q.2)) (p,x)‖ ≤ C*M := by
  dsimp only
  let s := k+N+dim+1
  let m := s+2
  have hm : k+N+dim+3 ≤ m := by dsimp only [m,s]; omega
  let R : E → ClosedBallEval dim k m := fun x => closedBallEval dim k m (w x)
  have hR : ContDiff ℝ (N:ℕ∞ω) R := by
    apply contDiffOn_univ.mp
    exact (contDiffOn_closedBallEval_order m N k hm).comp (hw.of_le (by simp)).contDiffOn
      (fun x _ => hwB x)
  have hRcont (j : Fin (N+1)) :
      Continuous (fun x => ‖iteratedFDeriv ℝ j.val R x‖) :=
    (hR.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.mp j.isLt)).norm
  have hRbound (j : Fin (N+1)) : ∃ C ≥ 0, ∀ x ∈ K, ‖iteratedFDeriv ℝ j.val R x‖ ≤ C := by
    obtain ⟨r,hr⟩ := hK.bddAbove_image (hRcont j).continuousOn
    exact ⟨max 0 r,le_max_left _ _,fun x hx => (hr ⟨x,hx,rfl⟩).trans (le_max_right _ _)⟩
  choose C hC hCbound using hRbound
  let A := ∑ i : Fin (N+1), C i
  have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hC i)
  have hRA (i : ℕ) (hi : i ≤ N) (x : E) (hx : x ∈ K) : ‖iteratedFDeriv ℝ i R x‖ ≤ A := by
    let j : Fin (N+1) := ⟨i,Nat.lt_succ_of_le hi⟩
    exact (hCbound j x hx).trans (Finset.single_le_sum (fun l _ => hC l) (Finset.mem_univ j))
  refine ⟨(2:ℝ)^N*A,by positivity,?_⟩
  intro U hU hAgree
  obtain ⟨b,hb,hbVal,hbJet⟩ := exists_parametric_classicalBallRepresentative hV hU hAgree
  refine ⟨b,hb,hbVal,hbJet,?_⟩
  intro p hp x hx M hM hBound j hj
  let W (q : P) : ClosedBallSobolev dim m := denseSmoothBallSobolev dim m ⟨b q,hb q⟩
  let incA : ClosedBallSobolev dim m →ₗᵢ[ℝ] BallSobolev dim m :=
    ((closedBallSobolev dim) m).toSubmodule.subtypeₗᵢ
  let incS : StrongDirichletSpace dim s →ₗᵢ[ℝ] BallSobolev dim m :=
    ((strongDirichletSubmodule dim) s).toSubmodule.subtypeₗᵢ
  have hSame : EqOn (incA ∘ W) (incS ∘ U s) V := by
    intro q hq
    change smoothBallSobolev m ⟨b q,hb q⟩ = (U s q : BallSobolev dim m)
    apply TauCeti.Wkp.ext m
    apply Lp.ext
    refine (value_smoothBallSobolev_ae m ⟨b q,hb q⟩).trans ?_
    have hv := congrArg (fun u : FixedBallH1Zero dim =>
      TauCeti.W1p.value (u : FixedBallH1 dim)) (hAgree q hq s)
    change TauCeti.W1p.value (strongDirichletProjectionL dim s (U s q) : FixedBallH1 dim) = _ at hv
    rw [strongDirichletProjectionL_apply,TauCeti.Wkp.value_firstOrder] at hv
    change b q =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)]
      ⇑(TauCeti.Wkp.value m (U s q : BallSobolev dim m))
    rw [hv]
    exact (hbVal q hq).symm
  have hInc : ContDiffOn ℝ ∞ (incA ∘ W) V :=
    (incS.toContinuousLinearMap.contDiff.comp_contDiffOn (hU s)).congr hSame
  let : CompleteSpace (ClosedBallSobolev dim m) := completeSpace_closedBallSobolev dim m
  have hW : ContDiffOn ℝ ∞ W V := contDiffOn_top_of_closedRangeLinearIsometry hV incA W hInc
  have hNorm (j : ℕ) : ‖iteratedFDeriv ℝ j W p‖ = ‖iteratedFDeriv ℝ j (U s) p‖ := by
    have hEq : iteratedFDeriv ℝ j (incA ∘ W) p = iteratedFDeriv ℝ j (incS ∘ U s) p := by
      simpa only [iteratedFDerivWithin_of_isOpen j hV hp] using iteratedFDerivWithin_congr hSame hp j
    calc
      _ = ‖iteratedFDeriv ℝ j (incA ∘ W) p‖ :=
        (incA.norm_iteratedFDeriv_comp_left (hW.contDiffAt (hV.mem_nhds hp))
          (by simp : (j : ℕ∞ω) ≤ ∞)).symm
      _ = ‖iteratedFDeriv ℝ j (incS ∘ U s) p‖ := congrArg norm hEq
      _ = _ := incS.norm_iteratedFDeriv_comp_left ((hU s).contDiffAt (hV.mem_nhds hp))
        (by simp : (j : ℕ∞ω) ≤ ∞)
  let T := V ×ˢ (univ : Set E)
  have hT : IsOpen T := hV.prod isOpen_univ
  have hpT : (p,x) ∈ T := ⟨hp,mem_univ _⟩
  let Wp : P × E → ClosedBallSobolev dim m := W ∘ Prod.fst
  let Rx : (P × E) → (ClosedBallEval dim) k m := R ∘ Prod.snd
  have hWp : ContDiffOn ℝ (N:ℕ∞ω) Wp T :=
    (hW.of_le (by simp)).comp contDiffOn_fst (fun q hq => hq.1)
  have hRx : ContDiffOn ℝ (N:ℕ∞ω) Rx T := (hR.comp contDiff_snd).contDiffOn
  have hRead : EqOn (fun q : P × E => iteratedFDeriv ℝ k (b q.1) (w q.2))
      (fun q => Rx q (Wp q)) T := by
    intro q hq
    change iteratedFDeriv ℝ k (b q.1) (w q.2) = closedBallEval dim k m (w q.2) (W q.1)
    rw [show closedBallEval dim k m (w q.2) (W q.1) =
        closedBallJetL dim k m (W q.1) ⟨w q.2,hwB q.2⟩ from
      closedBallEval_apply k m (W q.1) ⟨w q.2,hwB q.2⟩]
    rw [show W q.1 = denseSmoothBallSobolev dim m ⟨b q.1,hb q.1⟩ from rfl,
      closedBallJetL_on_smooth k m (by omega)]
    rfl
  have hWJet (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDerivWithin ℝ i Wp T (p,x)‖ ≤ M := by
    let L := ContinuousLinearMap.fst ℝ P E
    have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (by
      intro q
      change ‖q.1‖ ≤ 1 * ‖q‖
      simpa only [one_mul] using norm_fst_le q)
    have hLT : L ⁻¹' V = T := by
      ext q
      exact ⟨fun hq => ⟨hq,mem_univ _⟩,fun hq => hq.1⟩
    have hEq := L.iteratedFDerivWithin_comp_right (hW.of_le (by simp)) hV.uniqueDiffOn
      (by rw [hLT]; exact hT.uniqueDiffOn) (show L (p,x) ∈ V from hp)
      (show (i:ℕ∞ω) ≤ ∞ by simp)
    rw [hLT] at hEq
    change iteratedFDerivWithin ℝ i Wp T (p,x) = _ at hEq
    rw [hEq]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const,Finset.card_fin]
    change ‖iteratedFDerivWithin ℝ i W V p‖ * ‖L‖ ^ i ≤ M
    rw [iteratedFDerivWithin_of_isOpen i hV hp,hNorm i]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)
      |>.trans (hBound i hi)
  have hRJet (i : ℕ) (hi : i ≤ N) :
      ‖iteratedFDerivWithin ℝ i Rx T (p,x)‖ ≤ A := by
    let L := ContinuousLinearMap.snd ℝ P E
    have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound L zero_le_one (by
      intro q
      change ‖q.2‖ ≤ 1 * ‖q‖
      simpa only [one_mul] using norm_snd_le q)
    rw [iteratedFDerivWithin_of_isOpen i hT hpT]
    change ‖iteratedFDeriv ℝ i (R ∘ L) (p,x)‖ ≤ A
    rw [L.iteratedFDeriv_comp_right hR (p,x) (by exact_mod_cast hi)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const,Finset.card_fin]
    change ‖iteratedFDeriv ℝ i R x‖ * ‖L‖ ^ i ≤ A
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)).trans (hRA i hi x hx)
  rw [← iteratedFDerivWithin_of_isOpen j hT hpT,iteratedFDerivWithin_congr hRead hpT j]
  refine (norm_iteratedFDerivWithin_clm_apply hRx hWp hT.uniqueDiffOn hpT (by exact_mod_cast hj)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * A * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hRJet i (Nat.le_of_lt_succ (Finset.mem_range.mp hi) |>.trans hj))
        (by positivity)) (hWJet (j-i) ((Nat.sub_le _ _).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2:ℝ)^j*A*M := by
      rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hA) hM

end CalderonPaper
