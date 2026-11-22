module

public import Proof.CalderonN.ParametricMetricBallDirichlet
public import Proof.CalderonN.ConormalDecomposition

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ChartUniqueContinuation
import Proof.CalderonN.HarmonicL2Space
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

/-! Adapted from `ParametricBallConormal` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 1600000

noncomputable section
open Set Filter Metric
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- A specified ambient classical solution on the fixed unit ball. -/
@[expose] def FixedBallSolution (g : (MetricField dim)) (d b : (X dim) → ℝ) : Prop :=
  ContDiff ℝ ∞ b ∧ EqOn b d (standardSphere dim) ∧ ∀ z ∈ ball (0 : (X dim)) 1, laplace g b z = 0

open scoped Classical in
/-- Interior derivatives of the chosen solution are independent of the
choice of extension across the sphere. -/
@[expose] def fixedBallPoisson (g : (MetricField dim)) (d : (X dim) → ℝ) : (X dim) → ℝ :=
  if h : ∃ b, FixedBallSolution g d b then Classical.choose h else fun _ => 0

theorem fixedBallPoisson_solution
    {S : Set (X dim)} (hS : IsOpen S) (hC : closedBall (0 : (X dim)) 1 ⊆ S)
    {g : (MetricField dim)} (hg : SmoothMetric S g)
    {d : (X dim) → ℝ} (hd : smoothNear d (standardSphere dim)) : FixedBallSolution g d (fixedBallPoisson g d) := by
  have h : ∃ b, FixedBallSolution g d b := exists_classical_fixedBallDirichlet hS hC hg hd
  rw [fixedBallPoisson,dite_eq_left h]
  exact Classical.choose_spec h

theorem eqOn_fixedBallSolution
    {S : Set (X dim)} (hS : IsOpen S) (hC : closedBall (0 : (X dim)) 1 ⊆ S)
    {g : (MetricField dim)} (hg : SmoothMetric S g) {d e b c : (X dim) → ℝ}
    (hB : FixedBallSolution g d b) (hD : FixedBallSolution g e c)
    (he : EqOn d e (standardSphere dim)) : EqOn b c (closedBall (0 : (X dim)) 1) := by
  have hb : ContDiffOn ℝ ∞ b S := hB.1.contDiffOn
  have hc : ContDiffOn ℝ ∞ c S := hD.1.contDiffOn
  have h := eqOn_closedUnitBall_of_laplace_eq_zero hS hC hg (hb.sub hc)
    (by
      intro z hz
      rw [laplace_sub hS g hb hc (hC (ball_subset_closedBall hz)),hB.2.2 z hz,hD.2.2 z hz,sub_self])
    (by
      intro z hz
      change b z - c z = 0
      rw [hB.2.1 hz,hD.2.1 hz,he hz,sub_self])
  exact fun z hz => sub_eq_zero.mp (h hz)

theorem eqOn_fderiv_closedUnitBall
    {b c : (X dim) → ℝ} (hb : ContDiff ℝ ∞ b) (hc : ContDiff ℝ ∞ c)
    (he : EqOn b c (closedBall (0 : (X dim)) 1)) :
    EqOn (fderiv ℝ b) (fderiv ℝ c) (closedBall (0 : (X dim)) 1) := by
  intro x hx
  have hUnique : UniqueDiffOn ℝ (closedBall (0 : (X dim)) 1) :=
    uniqueDiffOn_convex (convex_closedBall _ _) (by rw [interior_closedBall _ one_ne_zero]; exact ⟨0,by simp⟩)
  rw [← ((hb.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt).fderivWithin (hUnique x hx),
    ← ((hc.differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt).fderivWithin (hUnique x hx)]
  exact fderivWithin_congr he (he hx)

@[expose] def sphereNormalize (w : (X dim)) : (X dim) := ‖w‖⁻¹ • w

theorem sphereNormalize_mem_sphere {w : (X dim)} (hw : w ≠ 0) : sphereNormalize w ∈ (standardSphere dim) := by
  apply mem_sphere_zero_iff_norm.mpr
  rw [sphereNormalize,norm_smul,norm_inv,norm_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

theorem sphereNormalize_eq_of_sphere {w : (X dim)} (hw : w ∈ (standardSphere dim)) : sphereNormalize w = w := by
  rw [sphereNormalize,mem_sphere_zero_iff_norm.mp hw,inv_one,one_smul]

theorem contDiffOn_sphereNormalize : ContDiffOn ℝ ∞ sphereNormalize ({0}ᶜ : Set (X dim)) := by
  intro w hw
  have hw' : w ≠ 0 := hw
  exact (((contDiffAt_norm ℝ hw').inv (norm_ne_zero_iff.mpr hw')).smul contDiffAt_id).contDiffWithinAt

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- Angular extension of the Dirichlet conormal along radial rays. -/
@[expose] def parametricBallConormal (g : P × (X dim) → (Mat dim)) (d : P × (X dim) → ℝ) (q : P × (X dim)) : ℝ :=
  let G := fun z => g (q.1,z)
  let b := fixedBallPoisson G (fun z => d (q.1,z))
  ballConormal G b (sphereNormalize q.2)

omit [FiniteDimensional ℝ P] in
theorem contDiffOn_product_ballConormalVector
    {U : Set (P × (X dim))} {g : P × (X dim) → (Mat dim)}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) :
    ContDiffOn ℝ ∞ (fun q : P × (X dim) => ballConormalVector (fun z => g (q.1,z)) q.2) U := by
  apply (contDiffOn_piLp 2).mpr
  intro j
  change ContDiffOn ℝ ∞ (fun q : P × (X dim) => ∑ i, q.2 i *
    (Real.sqrt (g q).det * (g q)⁻¹ i j)) U
  have hDet : ∀ q ∈ U, (g q).det ≠ 0 := fun q hq => (hPos q hq).det_pos.ne'
  exact ContDiffOn.sum fun i _ =>
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).contDiffOn).mul
      (((contDiffOn_det_of_entries hg).sqrt hDet).mul (contDiffOn_inv_entry_of_entries hg hDet i j))

set_option maxHeartbeats 1600000 in
/-- The actual conormal of the chosen Poisson solution is jointly
smooth, including at the limiting signed radius when the metric and
data extend there. -/
theorem exists_contDiffOn_parametricBallConormal
    {U T : Set (P × (X dim))} (hU : IsOpen U) (hT : IsOpen T) (p₀ : P)
    (hCU : {p₀} ×ˢ closedBall (0 : (X dim)) 1 ⊆ U)
    (hST : {p₀} ×ˢ (standardSphere dim) ⊆ T)
    {g : P × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hPos : ∀ q ∈ U, (g q).PosDef) {d : P × (X dim) → ℝ} (hd : ContDiffOn ℝ ∞ d T) :
    ∃ V : Set P, IsOpen V ∧ p₀ ∈ V ∧ ContDiffOn ℝ ∞ (parametricBallConormal g d)
      (V ×ˢ ({0}ᶜ : Set (X dim))) := by
  let C := closedBall (0 : (X dim)) 1
  let S := (standardSphere dim)
  obtain ⟨V₁,W,hV₁,hW,hpW,hCW,hVW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p₀)) (isCompact_closedBall (0 : (X dim)) 1) hU hCU
  obtain ⟨V₂,Z,hV₂,hZ,hpZ,hSZ,hVZ⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p₀)) (isCompact_sphere (0 : (X dim)) 1) hT hST
  obtain ⟨V₀,hV₀,hp₀,b,hb,hB,_,hbD⟩ := exists_local_parametric_metricBallDirichlet
    hU hT p₀ hCU hST hg hPos hd
  let V := V₀ ∩ (V₁ ∩ V₂)
  have hV : IsOpen V := hV₀.inter (hV₁.inter hV₂)
  have hPV (q : P × (X dim)) (hq : q ∈ V ×ˢ C) : q ∈ U :=
    hVW ⟨hq.1.2.1,hCW hq.2⟩
  have hEq (p : P) (hp : p ∈ V) :
      EqOn (fderiv ℝ (fixedBallPoisson (fun z => g (p,z)) (fun z => d (p,z))))
        (fderiv ℝ (b p)) C := by
    have hgW : SmoothMetric W (fun z => g (p,z)) := by
      refine ⟨fun i j => (hg i j).comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ hz => hVW ⟨hp.2.1,hz⟩),fun z hz => hPos _ (hVW ⟨hp.2.1,hz⟩)⟩
    have hdZ : smoothNear (fun z => d (p,z)) S :=
      ⟨Z,hZ,hSZ,hd.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ hz => hVZ ⟨hp.2.2,hz⟩)⟩
    have hP := fixedBallPoisson_solution hW hCW hgW hdZ
    have hbSol : FixedBallSolution (fun z => g (p,z)) (fun z => d (p,z)) (b p) :=
      ⟨hb p,(hB p hp.1).1,(hB p hp.1).2⟩
    exact eqOn_fderiv_closedUnitBall hP.1 (hb p)
      (eqOn_fixedBallSolution hW hCW hgW hP hbSol (fun _ _ => rfl))
  have hN : ContDiffOn ℝ ∞ (fun q : P × (X dim) => (q.1,sphereNormalize q.2))
      (V ×ˢ ({0}ᶜ : Set (X dim))) :=
    contDiff_fst.contDiffOn.prodMk (contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn
      (fun q hq => hq.2))
  have hMap : MapsTo (fun q : P × (X dim) => (q.1,sphereNormalize q.2))
      (V ×ˢ ({0}ᶜ : Set (X dim))) (V ×ˢ C) :=
    fun q hq => ⟨hq.1,sphere_subset_closedBall (sphereNormalize_mem_sphere hq.2)⟩
  have hDer : ContDiffOn ℝ ∞ (fun q : P × (X dim) => fderiv ℝ (b q.1) q.2) (V ×ˢ C) :=
    hbD.mono (fun q hq => ⟨hq.1.1,hq.2⟩)
  have hN' := (hDer.clm_apply ((contDiffOn_product_ballConormalVector hg hPos).mono hPV)).comp hN hMap
  refine ⟨V,hV,⟨hp₀,hpW (mem_singleton _),hpZ (mem_singleton _)⟩,hN'.congr ?_⟩
  intro q hq
  unfold parametricBallConormal
  rw [ballConormal_eq_fderiv_conormalVector,hEq q.1 hq.1 (hMap hq).2]
  rfl

end CalderonN
