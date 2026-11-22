module

public import Proof.CalderonN.DilationHarmonic
public import Proof.CalderonN.StrictMetricWeight

import Proof.CalderonN.MetricCalculus
public import Proof.CalderonN.MetricDivergence
import Proof.CalderonN.ParameterJets
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set
open scoped ContDiff

namespace CalderonN.FixedTube

variable {dim : ℕ} [NeZero dim]

theorem contDiff_dilatedMetric_entry {g : (MetricField dim)} (hg : SmoothMetric univ g) (i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => dilatedMetric g q.1 q.2 i j) :=
  (contDiffOn_univ.mp (hg.1 i j)).comp (contDiff_fst.smul contDiff_snd)

theorem smoothMetric_dilatedMetric {g : (MetricField dim)} (hg : SmoothMetric univ g) (lam : ℝ) :
    SmoothMetric univ (dilatedMetric g lam) :=
  ⟨fun i j => ((contDiff_dilatedMetric_entry hg i j).comp
    (contDiff_const.prodMk contDiff_id)).contDiffOn, fun x _ => hg.2 (lam • x) (mem_univ _)⟩

theorem contDiff_dilatedMetric_divergenceCoeff {g : (MetricField dim)} (hg : SmoothMetric univ g)
    (i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => divergenceCoeff (dilatedMetric g q.1) q.2 i j) :=
  (contDiffOn_univ.mp (contDiffOn_divergenceCoeff hg i j)).comp (contDiff_fst.smul contDiff_snd)

theorem contDiff_dilatedMetric_inv_entry {g : (MetricField dim)} (hg : SmoothMetric univ g) (i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => (dilatedMetric g q.1 q.2)⁻¹ i j) :=
  contDiffOn_univ.mp (contDiffOn_inv_entry_of_entries (V := univ) (g := fun q : ℝ × (X dim) => dilatedMetric g q.1 q.2)
    (fun i j => (contDiff_dilatedMetric_entry hg i j).contDiffOn)
    (fun q _ => (hg.2 (q.1 • q.2) (mem_univ _)).det_pos.ne') i j)

theorem contDiff_dilatedMetric_christoffel {g : (MetricField dim)} (hg : SmoothMetric univ g)
    (k i j : (I dim)) :
    ContDiff ℝ ∞ (fun q : ℝ × (X dim) => christoffel (dilatedMetric g q.1) q.2 k i j) := by
  let F (a b : (I dim)) (q : ℝ × (X dim)) := dilatedMetric g q.1 q.2 a b
  have hf (a b : (I dim)) : ContDiffOn ℝ ∞ (F a b) univ :=
    (contDiff_dilatedMetric_entry hg a b).contDiffOn
  have hder (l a b : (I dim)) :
      ContDiff ℝ ∞ (fun q : ℝ × (X dim) =>
        coordDeriv l (fun y => dilatedMetric g q.1 y a b) q.2) := by
    have he : (fun q : ℝ × (X dim) => coordDeriv l (fun y => dilatedMetric g q.1 y a b) q.2) =
        baseCoordDeriv l (F a b) := by
      funext q
      exact (baseCoordDeriv_eq isOpen_univ (hf a b) (mem_univ q) l).symm
    rw [he]
    exact contDiffOn_univ.mp (contDiffOn_baseCoordDeriv isOpen_univ (hf a b) l)
  simp only [christoffel]
  exact (ContDiff.sum fun l _ => (contDiff_dilatedMetric_inv_entry hg k l).mul
    (((hder i l j).add (hder j i l)).sub (hder l i j))).div_const 2

set_option maxHeartbeats 700000 in
theorem continuousAt_dilatedMetric_connection {D : Type*} [TopologicalSpace D]
    {g : (MetricField dim)} (hg : SmoothMetric univ g) {p : D} {lam : D → ℝ} {x v w : D → (X dim)}
    (hlam : ContinuousAt lam p) (hx : ContinuousAt x p) (hv : ContinuousAt v p)
    (hw : ContinuousAt w p) :
    ContinuousAt (fun q => connection (dilatedMetric g (lam q)) (x q) (v q) (w q)) p := by
  unfold connection
  apply (PiLp.continuous_toLp 2 (fun _ : (I dim) => ℝ)).continuousAt.comp
  apply continuousAt_pi'
  intro k
  have c (i j : (I dim)) : ContinuousAt (fun q =>
      christoffel (dilatedMetric g (lam q)) (x q) k i j) p :=
    show ContinuousAt ((fun t : ℝ × (X dim) => christoffel (dilatedMetric g t.1) t.2 k i j) ∘
      (fun q : D => (lam q,x q))) p from
      (contDiff_dilatedMetric_christoffel hg k i j).continuous.continuousAt.comp (hlam.prodMk hx)
  have hv' (i : (I dim)) : ContinuousAt (fun q => v q i) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt.comp hv
  have hw' (i : (I dim)) : ContinuousAt (fun q => w q i) p :=
    (EuclideanSpace.proj (𝕜 := ℝ) i : (X dim) →L[ℝ] ℝ).continuous.continuousAt.comp hw
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    ((c i j).mul (hv' i)).mul (hw' j)

theorem continuousAt_dilatedMetric_gradient {D : Type*} [TopologicalSpace D]
    {g : (MetricField dim)} (hg : SmoothMetric univ g) {p : D}
    {lam : D → ℝ} {x : D → (X dim)} {f : D → (X dim) → ℝ}
    (hlam : ContinuousAt lam p) (hx : ContinuousAt x p)
    (hc : ∀ j, ContinuousAt (fun q => coordDeriv j (f q) (x q)) p) :
    ContinuousAt (fun q => chartMetricGradient (dilatedMetric g (lam q)) (f q) (x q)) p := by
  unfold chartMetricGradient
  apply (PiLp.continuous_toLp 2 (fun _ : (I dim) => ℝ)).continuousAt.comp
  apply continuousAt_pi'
  intro i
  have hG (j : (I dim)) : ContinuousAt (fun q => (dilatedMetric g (lam q) (x q))⁻¹ i j) p :=
    show ContinuousAt ((fun t : ℝ × (X dim) => (dilatedMetric g t.1 t.2)⁻¹ i j) ∘
      (fun q : D => (lam q,x q))) p from
      (contDiff_dilatedMetric_inv_entry hg i j).continuous.continuousAt.comp (hlam.prodMk hx)
  exact tendsto_finsetSum _ fun j _ => (hG j).mul (hc j)

end CalderonN.FixedTube
