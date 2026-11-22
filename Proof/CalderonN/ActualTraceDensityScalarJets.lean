module

public import Proof.CalderonN.SmoothSupportedHorizontalAdjoint
public import Proof.CalderonN.UniformMetricInverseEntryJets

import Proof.CalderonN.CoordinateJets
import Proof.CalderonN.CompactLocalJetBounds
import Proof.CalderonN.NormalizedRadialInverseJets
import Mathlib.Tactic

/-! The logarithmic density term in the coordinate adjoint has
ordinary background metric jets. -/

public section

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3800000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem uniform_background_metricScalar_jet_budget
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {m N : ℕ} (hNm : N ≤ m)
    (K : ℝ) (M : Fin (m+1) → ℝ) (hK : 0 < K)
    (f : Mat dim → ℝ) (hf : ∀ A : Mat dim,0 < A.det → ContDiffAt ℝ ∞ f A) :
    ∃ C : ℝ,1 ≤ C ∧ ∀ (g : MetricField dim),Elliptic Ω K g →
      (∀ (k : Fin (m+1)) i j,∀ y ∈ Ω,‖iteratedFDeriv ℝ k.val (fun x => g x i j) y‖ ≤ M k) →
      ∀ x ∈ Ω,LocalSmoothJetBudget (f ∘ g) x N C := by
  let D := backgroundAllMetricJetBudget M
  have hD := backgroundAllMetricJetBudget_ge_one M
  let J := ellipticMatrixLocus dim K D
  have hJ : IsCompact J := isCompact_ellipticMatrixLocus dim K D
  have hf' (A : Mat dim) (hA : A ∈ J) : ContDiffAt ℝ ∞ f A :=
    hf A (ellipticMatrixLocus_posDef hK hA).det_pos
  obtain ⟨B,hB,hfB⟩ := exists_uniform_local_finite_jet_bound hJ hf' N
  have hFac : (1:ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_pos N
  refine ⟨(N.factorial:ℝ)*B*D^N,one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hFac hB) (one_le_pow₀ hD),?_⟩
  intro g hg hJets x hx
  have hSmooth : ContDiffAt ℝ ∞ g x := contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j =>
    (hg.1 i j).contDiffAt (hΩ.mem_nhds hx)
  have hgJ : LocalSmoothJetBudget g x N D := by
    refine ⟨hSmooth,fun k hk => ?_⟩
    have hE : ‖iteratedFDeriv ℝ k g x‖ ≤ |M ⟨k,by omega⟩| := by
      apply norm_iteratedFDeriv_matrix_le_of_entries g x k hSmooth (abs_nonneg _)
      exact fun a b => (hJets ⟨k,by omega⟩ a b x hx).trans (le_abs_self _)
    exact hE.trans (abs_metricJet_le_all_budget M _)
  have hMem : g x ∈ J :=
    ⟨mem_closedBall_zero_iff.mpr hgJ.value_norm_le,(hg.2 x hx).1,fun v => ((hg.2 x hx).2 v).1⟩
  exact hgJ.comp ⟨hf' (g x) hMem,fun n hn => hfB (g x) hMem n hn⟩ hD

theorem uniform_actualTraceDensity_scalar_jets [Nontrivial (Fin dim)]
    {Ω : Set (X dim)} (hΩ : IsOpen Ω) {m N : ℕ} (hm : N+1 ≤ m) (K : ℝ) (hK : 0 < K)
    (M : Fin (m+1) → ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (g g₁ g₂ : MetricField dim) (e : Frame dim),
      Background Ω K M g g₁ g₂ e → ∀ x ∈ Ω,∀ i : I dim,
        LocalSmoothJetBudget (traceDensityDivergence (metricDensity g) (fun _ => axis i)) x N C := by
  let f (A : Mat dim) := Real.sqrt A.det
  have hf (A : Mat dim) (hA : 0 < A.det) : ContDiffAt ℝ ∞ f A := by
    apply ContDiffAt.sqrt _ hA.ne'
    exact (contDiffOn_univ.mp (contDiffOn_det_of_entries
      (fun i j => (matrixEntryL (dim:=dim) i j).contDiff.contDiffOn))).contDiffAt
  have hf' (A : Mat dim) (hA : 0 < A.det) : ContDiffAt ℝ ∞ (fun A => (f A)⁻¹) A :=
    (hf A hA).inv (Real.sqrt_pos.mpr hA).ne'
  obtain ⟨P,hP,hμ⟩ := uniform_background_metricScalar_jet_budget hΩ hm K M hK f hf
  obtain ⟨Q,hQ,hμi⟩ := uniform_background_metricScalar_jet_budget hΩ (by omega : N ≤ m) K M hK _ hf'
  let C := (2:ℝ)^N*‖ContinuousLinearMap.mul ℝ ℝ‖*P*Q
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro g g₁ g₂ e hBg x hx i
  let μ := metricDensity g
  have hM := hBg.2.2.2.2.1 g (by simp)
  have hg : LocalSmoothJetBudget μ x (N+1) P := hμ g hBg.1 hM x hx
  have hgi : LocalSmoothJetBudget (fun y => (μ y)⁻¹) x N Q := hμi g hBg.1 hM x hx
  have hDer : LocalSmoothJetBudget (coordDeriv i μ) x N P :=
    ⟨(hg.smooth.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const,
      fun n hn => (norm_iteratedFDeriv_coordDeriv_le hg.smooth i n).trans (hg.bound (n+1) (by omega))⟩
  have hPos (y : X dim) (hy : y ∈ Ω) : 0 < μ y := Real.sqrt_pos.mpr (hBg.1.posDef hK hy).det_pos
  have he : traceDensityDivergence μ (fun _ => axis i) =ᶠ[𝓝 x] fun y => coordDeriv i μ y*(μ y)⁻¹ := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [traceDensityDivergence_eq_coordinate_sum hΩ μ (hBg.1.contDiffOn_density hK) hPos _ contDiffOn_const hy]
    simp [coordDeriv,axis,PiLp.single_apply,div_eq_mul_inv,ite_mul]
  exact (hDer.real_mul hgi).congr_germ he

end CalderonN
