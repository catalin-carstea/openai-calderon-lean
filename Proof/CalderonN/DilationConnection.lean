module

public import Proof.CalderonN.DilationHarmonic
public import Proof.CalderonN.CovariantHessian

import Proof.CalderonN.MetricCalculus
import Proof.CalderonN.ParameterJets
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section
open Set
open scoped BigOperators ContDiff

namespace CalderonN

variable {dim : ℕ}

/-- Reference metric after dilation and the prescribed scalar change. -/
def conformalReference (σ : X dim → ℝ) (g : MetricField dim) (lam : ℝ) (y : X dim) : Mat dim :=
  σ y • dilatedMetric g lam y

theorem contDiffOn_conformalReference_family_entry {Ω : Set (X dim)} {g : (MetricField dim)}
    (hg : SmoothMetric Ω g) {σ : (X dim) → ℝ} (hσ : ContDiff ℝ ∞ σ) (i j : (I dim)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => conformalReference σ g q.1 q.2 i j)
      {q | q.1 • q.2 ∈ Ω} :=
  (hσ.comp contDiff_snd).contDiffOn.mul ((hg.1 i j).comp
    (contDiff_fst.smul contDiff_snd).contDiffOn (fun _ hq => hq))

theorem contDiffOn_christoffel_slice {U : Set (ℝ × (X dim))} (hU : IsOpen U)
    {g : ℝ × (X dim) → (Mat dim)} (hg : ∀ i j, ContDiffOn ℝ ∞ (fun q => g q i j) U)
    (hpos : ∀ q ∈ U, (g q).PosDef) (k i j : (I dim)) :
    ContDiffOn ℝ ∞ (fun q => christoffel (fun y => g (q.1, y)) q.2 k i j) U := by
  let G (a b : (I dim)) (q : ℝ × (X dim)) := g q a b
  let Γ (q : ℝ × (X dim)) := (∑ l, (g q)⁻¹ k l *
    (baseCoordDeriv i (G l j) q + baseCoordDeriv j (G i l) q -
      baseCoordDeriv l (G i j) q)) / 2
  have hΓ : ContDiffOn ℝ ∞ Γ U := by
    refine (ContDiffOn.sum fun l _ => (contDiffOn_inv_entry_of_entries hg
      (fun q hq => (hpos q hq).det_pos.ne') k l).mul ?_).div_const 2
    exact ((contDiffOn_baseCoordDeriv hU (hg l j) i).add
      (contDiffOn_baseCoordDeriv hU (hg i l) j)).sub (contDiffOn_baseCoordDeriv hU (hg i j) l)
  apply hΓ.congr
  rintro ⟨lam, y⟩ hy
  change christoffel (fun z => g (lam, z)) y k i j = Γ (lam, y)
  simp only [christoffel, Γ, G, fun (a b c : (I dim)) => baseCoordDeriv_eq hU (hg a b) hy c]

theorem contDiffOn_covectorSq_conformalReference_family {Ω : Set (X dim)}
    {g : (MetricField dim)} (hg : SmoothMetric Ω g) {σ f : (X dim) → ℝ}
    (hσ : ContDiff ℝ ∞ σ) (hσpos : ∀ y, 0 < σ y) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => covectorSq (conformalReference σ g q.1) f q.2)
      {q | q.1 • q.2 ∈ Ω} := by
  let U : Set (ℝ × (X dim)) := {q | q.1 • q.2 ∈ Ω}
  have hpos (q : ℝ × (X dim)) (hq : q ∈ U) : (conformalReference σ g q.1 q.2).PosDef :=
    (hg.2 (q.1 • q.2) hq).smul (hσpos q.2)
  have hinv := contDiffOn_inv_entry_of_entries (contDiffOn_conformalReference_family_entry hg hσ)
    (fun q hq => (hpos q hq).det_pos.ne')
  have hD (i : (I dim)) : ContDiffOn ℝ ∞ (fun q : ℝ × (X dim) => coordDeriv i f q.2) U := by
    have hsm : ContDiff ℝ ∞ (coordDeriv i f) :=
      (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (hsm.comp contDiff_snd).contDiffOn
  unfold covectorSq
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ((hinv i j).mul (hD i)).mul (hD j)

end CalderonN
