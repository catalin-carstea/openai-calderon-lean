module

public import Proof.CalderonPatch.CompactSecondJet

import Proof.CalderonPatch.PointLaplaceOrder
import Proof.CalderonPatch.FlatJetBounds
import Proof.CalderonN.CoordinateJets
import Proof.CalderonN.ChartSchwarzWords
import Mathlib.Tactic

public section

noncomputable section
open Filter Matrix Metric Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace CalderonPatch.GreenPole

open CalderonN (X I Mat hessian axis coordDeriv laplace MetricField christoffel chartDerivativeWord)

variable {d : ℕ} [NeZero d]

/-- Quadratic rescaling preserves a test's second derivative scale. -/
@[expose] def scaledTest (φ : X d → ℝ) (c : X d) (r : ℝ) (x : X d) : ℝ :=
  (r ^ 2) • φ (r⁻¹ • (x-c))

omit [NeZero d] in
theorem scaledTest_contDiff {φ : X d → ℝ} (hφ : ContDiff ℝ ∞ φ) (c : X d) (r : ℝ) :
    ContDiff ℝ ∞ (scaledTest φ c r) :=
  (hφ.comp ((contDiff_id.sub contDiff_const).const_smul _)).const_smul _

omit [NeZero d] in
theorem scaledTest_iteratedFDeriv {φ : X d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (c : X d) (r : ℝ) (j : ℕ) (x : X d) :
    iteratedFDeriv ℝ j (scaledTest φ c r) x =
      (r ^ 2 * (r⁻¹)^j) • iteratedFDeriv ℝ j φ (r⁻¹ • (x-c)) := by
  let f : X d → ℝ := fun z => φ (r⁻¹ • (z-c))
  have hf : ContDiff ℝ ∞ f := hφ.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have he := iteratedFDeriv_const_smul_apply (a := r ^ 2) (x := x)
    ((hf.of_le (by simp) : ContDiff ℝ j f).contDiffAt)
  change iteratedFDeriv ℝ j ((r ^ 2) • f) x = _
  rw [he]
  have heq : f = fun z => (fun z => φ (r⁻¹ • z)) (z-c) := rfl
  rw [heq,iteratedFDeriv_comp_sub (f := fun z : X d => φ (r⁻¹ • z)) j c x]
  have hs := congrFun (iteratedFDeriv_comp_const_smul (f := φ) (i := j) r⁻¹
    (hφ.of_le (by simp))) (x-c)
  rw [hs,smul_smul]

omit [NeZero d] in
theorem scaledTest_tsupport {φ : X d → ℝ} (hφ : tsupport φ ⊆ closedBall 0 1)
    (c : X d) {r : ℝ} (hr : 0 < r) :
    tsupport (scaledTest φ c r) ⊆ closedBall c r := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra! hnot
  have hdist : r < ‖x-c‖ := by simpa [mem_closedBall,dist_eq_norm,not_le] using hnot
  have hv : r⁻¹ • (x-c) ∉ closedBall (0 : X d) 1 := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    exact not_le.mpr (by
      calc
        1 = r⁻¹*r := (inv_mul_cancel₀ hr.ne').symm
        _ < _ := mul_lt_mul_of_pos_left hdist (inv_pos.mpr hr))
  exact hx (by
    unfold scaledTest
    rw [image_eq_zero_of_notMem_tsupport (fun hy => hv (hφ hy)),smul_zero])

theorem scaledTest_uniform_jets {φ : X d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∃ B ≥ (0 : ℝ), ∀ c r, 0 < r → r ≤ 1 → ∀ j ≤ 2, ∀ x,
      ‖iteratedFDeriv ℝ j (scaledTest φ c r) x‖ ≤ B := by
  obtain ⟨B,hB,hNorm⟩ := hφc.exists_bound_iteratedFDeriv hφ 2
  refine ⟨B,hB,fun c r hr hr1 j hj x => ?_⟩
  rw [scaledTest_iteratedFDeriv hφ c r j x,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hR : r^2 * (r⁻¹)^j ≤ 1 := by
    interval_cases j
    · simpa using pow_le_one₀ hr.le hr1 (n := 2)
    · simpa [pow_two,mul_assoc,mul_inv_cancel₀ hr.ne'] using hr1
    · rw [← mul_pow,mul_inv_cancel₀ hr.ne',one_pow]
  exact ((mul_le_mul_of_nonneg_left (hNorm j hj _) (by positivity)).trans
    (mul_le_mul_of_nonneg_right hR hB)).trans_eq (one_mul _)

theorem exists_compact_laplace_test {g : MetricField d} {c : X d} (hg : (g c).PosDef) :
    ∃ φ : X d → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ closedBall 0 1 ∧ φ 0 = 0 ∧
      ∀ r > (0 : ℝ), laplace g (scaledTest φ c r) c = (d : ℝ) := by
  let K : Compacts (X d) := ⟨closedBall 0 1,isCompact_closedBall _ _⟩
  let v : ScalarSecondJet d := (0,0,⟨g c,hg.isHermitian.isSymm.eq⟩)
  obtain ⟨f,hf⟩ := surjective_compactSecondJet (K := K) (closedBall_mem_nhds _ (by norm_num)) v
  have hφ0 : f 0 = 0 := congrArg Prod.fst hf
  refine ⟨f,f.contDiff,f.compact_supp,f.tsupport_subset,hφ0,fun r hr => ?_⟩
  let A := scaledTest (f : X d → ℝ) c r
  have hA : ContDiff ℝ ∞ A := scaledTest_contDiff f.contDiff c r
  have hD (j : ℕ) : iteratedFDeriv ℝ j A c =
      (r ^ 2 * (r⁻¹)^j) • iteratedFDeriv ℝ j f (0 : X d) := by
    rw [show A = scaledTest (f : X d → ℝ) c r from rfl,scaledTest_iteratedFDeriv f.contDiff,
      sub_self,smul_zero]
  have hWord (j : ℕ) (u : Fin j → I d) :
      chartDerivativeWord (List.ofFn u) A c =
        (r^2 * (r⁻¹)^j) * chartDerivativeWord (List.ofFn u) f 0 := by
    rw [congrFun (CalderonN.chartDerivativeWord_ofFn j u hA) c,
      congrFun (CalderonN.chartDerivativeWord_ofFn j u f.contDiff) 0,hD]
    rfl
  have hFirst (i : I d) : coordDeriv i A c = 0 := by
    have hEq : coordDeriv i (f : X d → ℝ) 0 = 0 := congrArg (fun z : ScalarSecondJet d => z.2.1 i) hf
    have := hWord 1 (fun _ => i)
    simpa only [List.ofFn_succ,List.ofFn_zero,chartDerivativeWord,List.foldr_cons,List.foldr_nil,
      hEq,mul_zero] using this
  have hSecond (i j : I d) : hessian A c i j = g c i j := by
    have hEq : hessian (f : X d → ℝ) 0 i j = g c i j :=
      congrArg (fun z : ScalarSecondJet d => z.2.2.val i j) hf
    have hR : r^2 * (r⁻¹)^2 = 1 := by rw [← mul_pow,mul_inv_cancel₀ hr.ne',one_pow]
    have hh : hessian A c i j = hessian (f : X d → ℝ) 0 i j := by
      change coordDeriv i (coordDeriv j A) c = coordDeriv i (coordDeriv j (f : X d → ℝ)) 0
      simpa only [List.ofFn_succ,List.ofFn_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
        Fin.succ_zero_eq_one,chartDerivativeWord,List.foldr_cons,List.foldr_nil,hR,one_mul]
        using hWord 2 ![i,j]
    exact hh.trans hEq
  have hLA : smoothSecondJet isOpen_univ (mem_univ c) A hA.contDiffOn = v := by
    refine Prod.ext ?_ (Prod.ext (funext hFirst) (Subtype.ext (Matrix.ext hSecond)))
    change A c = 0
    simp [A,scaledTest,hφ0]
  rw [← smoothSecondJet_laplace isOpen_univ (mem_univ c) g A hA.contDiffOn,hLA]
  change laplaceOnSecondJet g c (0,0,⟨g c,hg.isHermitian.isSymm.eq⟩) = _
  rw [laplaceOnSecondJet_zero_first, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hg.det_pos.ne'),
    Matrix.trace_one, Fintype.card_fin]

omit [NeZero d] in
/-- A uniform bound on a function's first and second derivatives
bounds its coordinate Laplacian on a compact smooth metric region. -/
theorem exists_laplace_bound_of_uniform_jets {U K : Set (X d)} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {g : MetricField d} (hg : CalderonN.SmoothMetric U g)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ C ≥ (0 : ℝ), ∀ f : X d → ℝ, ContDiff ℝ ∞ f →
      (∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) →
      ∀ x ∈ K, |laplace g f x| ≤ C := by
  let w (x : X d) := ∑ i : I d, ∑ j : I d, |(g x)⁻¹ i j| *
    (1 + ∑ k : I d, |christoffel g x k i j|)
  have hW : ContinuousOn w U :=
    continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
      (CalderonN.contDiffOn_metric_inv_entry hg i j).continuousOn.abs.mul
        (continuousOn_const.add (continuousOn_finsetSum _ fun k _ =>
          (CalderonN.contDiffOn_christoffel hU hg k i j).continuousOn.abs))
  obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn (hW.mono hKU)
  refine ⟨(max A 0)*B,by positivity,fun f hf hb x hx => ?_⟩
  have hd (k : I d) : |coordDeriv k f x| ≤ B := by
    have h := (CalderonN.norm_iteratedFDeriv_coordDeriv_le hf.contDiffAt k 0).trans (hb 1 (by decide) x)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h
  have hh (i j : I d) : |hessian f x i j| ≤ B := by
    have h := (CalderonN.norm_iteratedFDeriv_hessian_entry_le hf.contDiffAt i j 0).trans
      (hb 2 (by decide) x)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using h
  calc
    |laplace g f x| ≤ ∑ i : I d, ∑ j : I d, |(g x)⁻¹ i j| *
        (B + ∑ k : I d, |christoffel g x k i j| * B) := by
      unfold laplace
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [sub_eq_add_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg]
      refine add_le_add (hh i j) ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k _ => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hd k) (abs_nonneg _)
    _ = w x * B := by simp only [w,Finset.sum_mul,add_mul,one_mul,mul_assoc]
    _ ≤ _ := by
      have hAbs : |w x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x hx
      exact mul_le_mul_of_nonneg_right
        ((le_abs_self (w x)).trans (hAbs.trans (le_max_left _ _))) hB

end CalderonPatch.GreenPole
