module

public import Proof.CalderonPatch.HarmonicRieszPoint

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff RealInnerProductSpace Topology

namespace CalderonN

variable {d : ℕ} [NeZero d] {U : Set (X d)} (hU : IsOpen U)
  {g : MetricField d} (hg : SmoothMetric U g)

local notation "H" => harmonicL2Space hU hg
local notation "B" k => ContinuousMultilinearMap ℝ (fun _ : Fin k => X d) ℝ
local notation "Read" k => (H →L[ℝ] B k)
local notation "DRead" k => (X d →L[ℝ] Read k)

local instance jetReadingNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (H →L[ℝ] B k) := ContinuousLinearMap.toNormedAddCommGroup

local instance jetReadingNormedSpace (k : ℕ) :
    NormedSpace ℝ (H →L[ℝ] B k) := ContinuousLinearMap.toNormedSpace

local instance jetDerivativeNormedAddCommGroup (k : ℕ) :
    NormedAddCommGroup (X d →L[ℝ] B k) := ContinuousLinearMap.toNormedAddCommGroup

local instance jetDerivativeNormedSpace (k : ℕ) :
    NormedSpace ℝ (X d →L[ℝ] B k) := ContinuousLinearMap.toNormedSpace

private def harmonicEvalJetCurry (k : ℕ) : (Read (k+1)) →L[ℝ] (DRead k) :=
  let curry := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X d) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  (ContinuousLinearMap.flipₗᵢ ℝ H (X d) (B k)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.compL ℝ H _ _ curry)

private def harmonicEvalJetDeriv (k : ℕ) (x : X d) : DRead k :=
  harmonicEvalJetCurry hU hg k (harmonicEvalJets hU hg (k+1) x)

private theorem harmonicEvalJetDeriv_apply (k : ℕ) {x : X d} (hx : x ∈ U)
    (v : X d) (u : H) :
    harmonicEvalJetDeriv hU hg k x v u = fderiv ℝ
      (iteratedFDeriv ℝ k (harmonicRepresentative u)) x v := by
  unfold harmonicEvalJetDeriv harmonicEvalJetCurry
  change continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X d) ℝ
    (harmonicEvalJets hU hg (k+1) x u) v = _
  rw [harmonicEvalJets_apply hU hg _ hx, fderiv_iteratedFDeriv]
  rfl

omit [NeZero d] in
include hU in
private theorem contDiffOn_iteratedFDeriv_open {f : X d → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) :
    ContDiffOn ℝ ∞ (iteratedFDeriv ℝ k f) U := by
  induction k with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact (continuousMultilinearCurryFin0 ℝ (X d) ℝ).symm.contDiff.comp_contDiffOn hf
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X d) ℝ).symm.toContinuousLinearEquiv
    exact L.contDiff.comp_contDiffOn (ih.fderiv_of_isOpen hU (by simp))

set_option maxHeartbeats 2400000 in
/-- Local uniform bounds for one additional derivative give a
quadratic remainder in the operator norm of harmonic evaluation. -/
private theorem hasFDerivAt_harmonicEvalJets (k : ℕ) {x : X d} (hx : x ∈ U) :
    HasFDerivAt (harmonicEvalJets hU hg k) (harmonicEvalJetDeriv hU hg k x) x := by
  obtain ⟨r,hr,hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let K₀ := Metric.closedBall x (r/2)
  have hK : K₀ ⊆ U := (Metric.closedBall_subset_ball (by linarith)).trans hBall
  have hxx : x ∈ K₀ := Metric.mem_closedBall_self (by positivity)
  obtain ⟨A,hA,hBound⟩ := harmonicInteriorJets_of_smoothMetric hU hg K₀
    (isCompact_closedBall _ _) hK (k + 2)
  have hE (y : X d) (hy : y ∈ K₀) :
      ‖harmonicEvalJets hU hg k y - harmonicEvalJets hU hg k x -
           harmonicEvalJetDeriv hU hg k x (y-x)‖ ≤ A * ‖y-x‖ ^ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound
      (harmonicEvalJets hU hg k y - harmonicEvalJets hU hg k x -
        harmonicEvalJetDeriv hU hg k x (y-x)) (by positivity) ?_
    intro u
    simp only [sub_apply, harmonicEvalJets_apply hU hg k (hK hy),
      harmonicEvalJets_apply hU hg k hx, harmonicEvalJetDeriv_apply hU hg k hx]
    let v := iteratedFDeriv ℝ k (harmonicRepresentative u)
    let K₁ := Metric.closedBall x ‖y - x‖
    have hy1 : y ∈ K₁ := by exact le_of_eq (dist_eq_norm _ _)
    have hx1 : x ∈ K₁ := Metric.mem_closedBall_self (norm_nonneg _)
    have hK₁ : K₁ ⊆ K₀ := Metric.closedBall_subset_closedBall (by simpa [K₀,dist_eq_norm] using hy)
    have hv : ContDiffOn ℝ ∞ v U :=
      contDiffOn_iteratedFDeriv_open hU (harmonicRepresentative_spec u).1.1 k
    have hv' : ContDiffOn ℝ ∞ (fderiv ℝ v) U := hv.fderiv_of_isOpen hU (by simp)
    have hB (z : X d) (hz : z ∈ K₀) : ‖fderiv ℝ (fderiv ℝ v) z‖ ≤ A * ‖u‖ := by
      change ‖fderiv ℝ (fderiv ℝ (iteratedFDeriv ℝ k (harmonicRepresentative u))) z‖ ≤ _
      have he : fderiv ℝ (iteratedFDeriv ℝ k (harmonicRepresentative u)) =
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X d) ℝ)
            ∘ iteratedFDeriv ℝ (k+1) (harmonicRepresentative u)) := fderiv_iteratedFDeriv
      let L := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => X d) ℝ).toLinearIsometry
      have hs := contDiffOn_iteratedFDeriv_open hU (harmonicRepresentative_spec u).1.1 (k+1)
      have hd := (hs.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hK hz))
      have heq := (L.toContinuousLinearMap.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
      rw [he]
      change ‖fderiv ℝ (L.toContinuousLinearMap ∘ iteratedFDeriv ℝ (k+1) (harmonicRepresentative u)) z‖ ≤ _
      rw [heq]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      calc
        _ ≤ 1 * ‖fderiv ℝ (iteratedFDeriv ℝ (k+1) (harmonicRepresentative u)) z‖ :=
          mul_le_mul_of_nonneg_right L.norm_toContinuousLinearMap_le (norm_nonneg _)
        _ ≤ _ := by
          rw [one_mul,norm_fderiv_iteratedFDeriv]
          exact hBound u.1 _ (harmonicRepresentative_spec u).1
            (harmonicRepresentative_spec u).2 z hz
    have hDiff (z : X d) (hz : z ∈ K₁) : ‖fderiv ℝ v z - fderiv ℝ v x‖ ≤
        (A * ‖u‖) * ‖y-x‖ := by
      refine ((convex_closedBall x (r/2)).norm_image_sub_le_of_norm_fderiv_le
        (fun t ht => hv'.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds (hK ht)))
        hB hxx (hK₁ hz)).trans ?_
      exact mul_le_mul_of_nonneg_left (by simpa [K₁,dist_eq_norm] using hz)
        (mul_nonneg hA (norm_nonneg _))
    have hR := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hv.differentiableOn (by simp) |>.differentiableAt (hU.mem_nhds (hK (hK₁ hz))))
      hDiff hx1 hy1
    change ‖v y - v x - fderiv ℝ v x (y-x)‖ ≤ _
    exact hR.trans_eq (by ring)
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hSmall : ∀ᶠ y in 𝓝 x, A * ‖y-x‖ < ε := by
    have hcont : Continuous (fun y : X d => A * ‖y-x‖) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm)
    have hAt : A * ‖x-x‖ < ε := by simpa using hε
    exact hcont.continuousAt.eventually (gt_mem_nhds hAt)
  filter_upwards [Metric.closedBall_mem_nhds x (by positivity : 0 < r/2), hSmall] with y hy hs
  exact (hE y hy).trans (by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hs.le (norm_nonneg _))

/-- Harmonic evaluation is smooth as a function with values in the
dual Hilbert space, with strong operator-norm derivatives. -/
theorem contDiffOn_harmonicEvalJets (k : ℕ) :
    ContDiffOn ℝ ∞ (harmonicEvalJets hU hg k) U := by
  rw [contDiffOn_infty]
  suffices ∀ n k : ℕ, ContDiffOn ℝ n (harmonicEvalJets hU hg k) U by
    exact fun n => this n k
  intro n
  induction n with
  | zero =>
    intro j
    rw [Nat.cast_zero,contDiffOn_zero]
    exact fun x hx => (hasFDerivAt_harmonicEvalJets hU hg j hx).continuousAt.continuousWithinAt
  | succ n ih =>
    intro j
    rw [Nat.cast_succ,contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (hasFDerivAt_harmonicEvalJets hU hg j hx).differentiableAt.differentiableWithinAt,
      by simp,?_⟩
    exact (((harmonicEvalJetCurry hU hg j).contDiff).comp_contDiffOn (ih (j+1))).congr fun x hx =>
      (hasFDerivAt_harmonicEvalJets hU hg j hx).fderiv

theorem contDiffOn_harmonicRiesz :
    ContDiffOn ℝ ∞ (harmonicRiesz hU hg) U := by
  let L₀ : (B 0) →L[ℝ] ℝ := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => X d) ℝ 0
  have hL : ContDiffOn ℝ ∞ (fun x => L₀.comp (harmonicEvalJets hU hg 0 x)) U :=
    (contDiffOn_const (c := L₀)).clm_comp (contDiffOn_harmonicEvalJets hU hg 0)
  unfold harmonicRiesz
  exact (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hL

end CalderonN
