module

public import Proof.CalderonPatch.CauchyNormalJets
public import Proof.CalderonPatch.PointLaplaceOrder
public import Proof.CalderonPatch.SmoothPasting

import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.CovariantHessian
import Proof.CalderonN.GreenWeak

public section

noncomputable section
open Filter Matrix Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis chartDerivativeWord coordDeriv laplace laplace_congrOn Harmonic)

variable {n : ℕ} [NeZero n] {U : Set (X n)} {i : I n}

/-- The strong elliptic equation in an open half-chart makes the
value and normal derivative determine all jets at its flat seam. -/
theorem laplace_cauchy_flatJets {γ : MetricField n} (hγ : CalderonN.SmoothMetric univ γ)
    (hU : IsOpen U) {u : X n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hH : EqOn (laplace γ u) 0 (U ∩ {x | 0 < x i}))
    (h0 : EqOn u 0 (boundaryFace U i)) (h1 : EqOn (coordDeriv i u) 0 (boundaryFace U i)) :
    ∀ x ∈ boundaryFace U i, ∀ k, iteratedFDeriv ℝ k u x = 0 := by
  classical
  let α := (I n × I n) ⊕ I n
  let ii : α := Sum.inl (i, i)
  let s : Finset α := Finset.univ.erase ii
  let c : α → X n → ℝ := Sum.elim (fun p x => (γ x)⁻¹ p.1 p.2) (fun k x => laplaceFirstCoeff γ x k)
  let W : α → List (I n) := Sum.elim (fun p => [p.1, p.2]) (fun k => [k])
  have hc (j : α) : ContDiff ℝ ∞ (c j) := by
    cases j with
    | inl p => exact contDiffOn_univ.mp (CalderonN.contDiffOn_metric_inv_entry hγ p.1 p.2)
    | inr k =>
      apply contDiffOn_univ.mp
      exact (ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
        (CalderonN.contDiffOn_metric_inv_entry hγ i j).mul
          (CalderonN.contDiffOn_christoffel isOpen_univ hγ k i j)))).neg
  have hW (j : α) (hj : j ∈ s) : (W j).count i ≤ 1 := by
    have hNe : j ≠ ii := (Finset.mem_erase.mp hj).1
    cases j with
    | inl p =>
      rcases p with ⟨j, k⟩
      have hne : j ≠ i ∨ k ≠ i := by
        by_contra h
        push Not at h
        exact hNe (by simp [ii, h.1, h.2])
      rcases hne with h | h <;> simp +decide [W, List.count_cons, h] <;> split <;> omega
    | inr k => simp +decide [W, List.count_cons]; split <;> omega
  apply cauchy_normal_jets_eq_zero hU hu (hc ii)
    (fun x _ => ((hγ.2 x (mem_univ x)).inv.diag_pos (i := i)).ne')
    s (fun j => -c j) W (fun j _ => (hc j).neg) hW _ h0 h1
  intro x hx
  have hLap := hH hx
  change laplace γ u x = 0 at hLap
  have hsum : ∑ j : α, c j x * chartDerivativeWord (W j) u x = laplace γ u x := by
    rw [Fintype.sum_sum_type, ← coordinateElliptic_eq_laplace γ u]
    simp only [c, W, Sum.elim_inl, Sum.elim_inr, coordinateElliptic, Pi.add_apply, Finset.sum_apply,
      Pi.mul_apply, Fintype.sum_prod_type]
  have h := Finset.sum_erase_add Finset.univ (fun j : α => c j x * chartDerivativeWord (W j) u x)
    (Finset.mem_univ ii)
  rw [hsum, hLap] at h
  change c ii x * chartDerivativeWord (W ii) u x = (∑ j ∈ s, -c j * chartDerivativeWord (W j) u) x
  simp only [Finset.sum_apply, Pi.neg_apply, Pi.mul_apply, neg_mul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left (by simpa only [s, add_comm] using h)

/-- Cauchy uniqueness on a flat measured patch, by smooth zero extension
and the checked interior scalar continuation theorem. -/
theorem laplace_eq_zero_of_flat_boundary_cauchy {γ : MetricField n} (hγ : CalderonN.SmoothMetric univ γ)
    (hU : IsOpen U) (hConn : IsConnected U) (hFace : (boundaryFace U i).Nonempty)
    {u : X n → ℝ} (hu : ContDiff ℝ ∞ u) (hH : EqOn (laplace γ u) 0 (U ∩ {x | 0 < x i}))
    (h0 : EqOn u 0 (boundaryFace U i)) (h1 : EqOn (coordDeriv i u) 0 (boundaryFace U i)) :
    EqOn u 0 (U ∩ {x | 0 < x i}) := by
  classical
  let S : Set (X n) := {x | 0 ≤ x i}
  let Upos : Set (X n) := U ∩ {x | 0 < x i}
  let Uneg : Set (X n) := U ∩ {x | x i < 0}
  let w : X n → ℝ := S.piecewise u 0
  have hUpos : IsOpen Upos := hU.inter (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous)
  have hUneg : IsOpen Uneg := hU.inter (isOpen_lt (EuclideanSpace.proj i).continuous continuous_const)
  have hFaceS : U ∩ frontier S = boundaryFace U i := by
    rw [show S = {x : X n | 0 ≤ x i} from rfl, frontier_halfSpace]
    ext x
    simp [boundaryFace, eq_comm]
  have hFlat := laplace_cauchy_flatJets hγ hU hu hH h0 h1
  have hSmooth : ContDiffOn ℝ ∞ w U := by
    apply contDiffOn_piecewise_of_matched_jets hU hu.contDiffOn contDiffOn_const
    intro k x hx
    have hs := hFlat x (hFaceS ▸ hx) k
    have hZ : iteratedFDeriv ℝ k (fun _ : X n => (0 : ℝ)) = 0 := iteratedFDeriv_fun_zero
    exact hs.trans (congrFun hZ x).symm
  have hPos : EqOn w u Upos := fun x hx => piecewise_eq_of_mem _ _ _ (show 0 ≤ x i from le_of_lt hx.2)
  have hNeg : EqOn w 0 Uneg := fun x hx => piecewise_eq_of_notMem _ _ _ (show ¬ 0 ≤ x i from not_le_of_gt hx.2)
  have hLapPos : EqOn (laplace γ w) 0 Upos := fun x hx =>
    (laplace_congrOn hUpos (g := γ) (fun _ _ => rfl) hPos hx).trans (hH hx)
  have hLapZero : EqOn (laplace γ 0) 0 U := by
    intro x _
    have h (j : I n) : coordDeriv j (0 : X n → ℝ) = 0 := by funext y; simp [coordDeriv, Pi.zero_def]
    simp only [laplace, h, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
  have hLapNeg : EqOn (laplace γ w) 0 Uneg := fun x hx =>
    (laplace_congrOn hUneg (g := γ) (fun _ _ => rfl) hNeg hx).trans (hLapZero hx.1)
  have hLap : EqOn (laplace γ w) 0 U := by
    intro x hx
    rcases lt_trichotomy (x i) 0 with h | h | h
    · exact hLapNeg ⟨hx, h⟩
    · have hcl : x ∈ closure Upos := boundaryFace_subset_closure_positive hU ⟨hx,h⟩
      have hcont := (contDiffOn_coordinateLaplace hU ⟨fun i j => (hγ.1 i j).mono (subset_univ _),
        fun x _ => hγ.2 x (mem_univ _)⟩ hSmooth).continuousOn
      exact hLapPos.of_subset_closure (hcont.mono inter_subset_left) continuousOn_const
        (fun _ hy => ⟨hy.1, subset_closure hy⟩) inter_subset_right ⟨hx, hcl⟩
    · exact hLapPos ⟨hx, h⟩
  have hNegne : Uneg.Nonempty := by
    obtain ⟨p, hp⟩ := hFace
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp.1)
    let x := p - (r / 2) • axis i
    have hx : x ∈ ball p r := by
      apply mem_ball_iff_norm.mpr
      simp [x, sub_sub_cancel_left, norm_smul, axis, abs_of_pos hr]
      linarith
    refine ⟨x, hrU hx, ?_⟩
    change (p - (r / 2) • axis i) i < 0
    have hp₀ : p i = 0 := hp.2
    simp [hp₀, axis, show 0 < r / 2 by positivity]
  have hγU : CalderonN.SmoothMetric U γ := ⟨fun i j => (hγ.1 i j).mono (subset_univ _),
    fun x _ => hγ.2 x (mem_univ _)⟩
  have hWzero := CalderonN.harmonic_eqOn_of_eqOn_open hU hConn hUneg hNegne inter_subset_left
    hγU ⟨hSmooth, hLap⟩ ⟨contDiffOn_const, hLapZero⟩ hNeg
  exact fun x hx => (hPos hx).symm.trans (hWzero hx.1)

end CalderonPatch
