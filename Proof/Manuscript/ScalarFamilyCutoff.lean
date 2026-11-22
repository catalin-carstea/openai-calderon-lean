module

public import Proof.Manuscript.ScalarElliptic

import Proof.CalderonN.EllipticCalculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic

@[expose] public section

noncomputable section
open Set Filter CalderonN
open scoped ContDiff Topology

namespace CalderonPaper.ScalarElliptic

variable {n : ℕ}

/-- A parameter-independent truncation of a chart operator to a
global positive metric, with lower terms cut off by the same function. -/
def cutoffOperator (χ : X n → ℝ) (L : ScalarElliptic n) : ScalarElliptic n where
  metric x := χ x • L.metric x + (1 - χ x) • (1 : Mat n)
  first x i := χ x * L.first x i
  zeroth x := χ x * L.zeroth x

theorem cutoffOperator_metric_germ {χ : X n → ℝ} {L : ScalarElliptic n} {x : X n}
    (h : χ =ᶠ[𝓝 x] fun _ => 1) : (cutoffOperator χ L).metric =ᶠ[𝓝 x] L.metric :=
  h.mono fun y hy => by simp [cutoffOperator,hy]

theorem cutoffOperator_apply_of_one {χ : X n → ℝ} {L : ScalarElliptic n} {x : X n}
    (h : χ x = 1) (u : X n → ℝ) : (cutoffOperator χ L).apply u x = L.apply u x := by
  simp [ScalarElliptic.apply,ScalarElliptic.principalMatrix,cutoffOperator,h]

theorem exists_scalar_operator_cutoff {D K : Set (X n)}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ χ : X n → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ D ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨f,hf,_,hfD,hfK⟩ := Elliptic.exists_plateau_cutoff hD hK hKD
  let χ := Real.smoothTransition ∘ f
  refine ⟨χ,Real.smoothTransition.contDiff.comp hf,?_ ,
    fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩,?_⟩
  · apply (closure_mono ?_).trans hfD
    intro x hx
    exact fun hz => hx (Real.smoothTransition.zero_of_nonpos hz.le)
  · intro x hx
    exact (hfK x hx).mono fun y hy =>
      Real.smoothTransition.one_of_one_le (by rw [hy])

private theorem smooth_cutoff_mul_joint {D : Set (X n)} (hD : IsOpen D)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχD : tsupport χ ⊆ D)
    {F : ℝ × X n → ℝ} (hF : ContDiffOn ℝ ∞ F (univ ×ˢ D)) :
    ContDiff ℝ ∞ (fun q : ℝ × X n => χ q.2 * F q) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  by_cases hq : q.2 ∈ D
  · exact ((hχ.comp contDiff_snd).contDiffAt (x := q)).mul
      (hF.contDiffAt ((isOpen_univ.prod hD).mem_nhds ⟨mem_univ _,hq⟩))
  · have hN : ∀ᶠ r : ℝ × X n in 𝓝 q, r.2 ∉ tsupport χ :=
      continuous_snd.continuousAt.preimage_mem_nhds
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds
          (show q.2 ∉ tsupport χ from fun h => hq (hχD h)))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hN] with r hr
    change χ r.2 * F r = 0
    rw [image_eq_zero_of_notMem_tsupport hr,zero_mul]

theorem smoothFamilyOn_cutoffOperator {D : Set (X n)} (hD : IsOpen D)
    {χ : X n → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχD : tsupport χ ⊆ D)
    (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {L : ℝ → ScalarElliptic n} (hL : SmoothFamilyOn L D) :
    SmoothFamilyOn (fun t => cutoffOperator χ (L t)) univ := by
  have hG (i j : I n) : ContDiff ℝ ∞
      (fun q : ℝ × X n => (cutoffOperator χ (L q.1)).metric q.2 i j) := by
    have h := smooth_cutoff_mul_joint hD hχ hχD (hL.2.1 i j)
    exact h.add ((contDiff_const.sub (hχ.comp contDiff_snd)).mul contDiff_const)
  have hB (i : I n) : ContDiff ℝ ∞
      (fun q : ℝ × X n => (cutoffOperator χ (L q.1)).first q.2 i) :=
    smooth_cutoff_mul_joint hD hχ hχD (hL.2.2.1 i)
  have hC : ContDiff ℝ ∞ (fun q : ℝ × X n => (cutoffOperator χ (L q.1)).zeroth q.2) :=
    smooth_cutoff_mul_joint hD hχ hχD hL.2.2.2
  refine ⟨?_,fun i j => (hG i j).contDiffOn,fun i => (hB i).contDiffOn,hC.contDiffOn⟩
  intro t
  refine ⟨⟨fun i j => ((hG i j).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,?_⟩,
    fun i => ((hB i).comp (contDiff_const.prodMk contDiff_id)).contDiffOn,
    (hC.comp (contDiff_const.prodMk contDiff_id)).contDiffOn⟩
  intro x _
  by_cases hx : x ∈ D
  · obtain ⟨hzero,hone⟩ := hχ01 x
    rcases eq_or_lt_of_le hzero with hz | hz
    · simpa [cutoffOperator, ← hz] using (Matrix.PosDef.one : (1 : Mat n).PosDef)
    rcases eq_or_lt_of_le hone with h1 | h1
    · simpa [cutoffOperator,h1] using (hL.1 t).1.2 x hx
    exact (((hL.1 t).1.2 x hx).smul hz).add (Matrix.PosDef.one.smul (sub_pos.mpr h1))
  · have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hχD h))
    simpa [cutoffOperator,hzero] using (Matrix.PosDef.one : (1 : Mat n).PosDef)

theorem smoothFamilyOn_const {L : ScalarElliptic n} {D : Set (X n)} (hL : L.SmoothOn D) :
    SmoothFamilyOn (fun _ => L) D :=
  ⟨fun _ => hL,
    fun i j => (hL.1.1 i j).comp contDiff_snd.contDiffOn (fun _ h => h.2),
    fun i => (hL.2.1 i).comp contDiff_snd.contDiffOn (fun _ h => h.2),
    hL.2.2.comp contDiff_snd.contDiffOn (fun _ h => h.2)⟩

end CalderonPaper.ScalarElliptic
