module

public import Proof.CalderonN.WkpCalculus
import Proof.ReleasedAnalysis.TauCeti.Analysis.Sobolev.CompactSupport
import Mathlib.Tactic

/-! The multiplication induction of the released `CollaboratorFixedSobolevCalculusOct17`,
retaining the Sobolev witness and product rule needed for interior regularity. -/
public section

noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal ContDiff Gradient InnerProductSpace

namespace CalderonN.SobolevMultiplication
open WkpCalculus TauCeti
variable {n : ℕ} {Ω : Opens (X n)}

set_option maxHeartbeats 2000000 in
theorem exists_mul (k : ℕ) {φ : X n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (u : Wkp (volume : Measure (X n)) Ω 2 k) :
    ∃ V : Wkp (volume : Measure (X n)) Ω 2 k,
      ⇑(Wkp.value k V) =ᵐ[(volume : Measure (X n)).restrict Ω]
        (fun x => φ x * Wkp.value k u x) := by
  induction k generalizing φ with
  | zero =>
    obtain ⟨M, hM⟩ := hφ.continuous.norm.bddAbove_range_of_hasCompactSupport (hc.comp_left norm_zero)
    let v := Wkp.value 0 u
    have hp : MemLp (fun x => φ x * v x) 2 ((volume : Measure (X n)).restrict Ω) :=
      MemLp.of_le_mul (Lp.memLp v) (hφ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable v))
        (Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hM ⟨x, rfl⟩) (norm_nonneg _))
    refine ⟨hp.toLp _, ?_⟩
    simpa only [v, Wkp.value_zero] using hp.coeFn_toLp
  | succ k ih =>
    obtain ⟨M, hM, hφM, hgradM⟩ :=
      (hφ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hc
    let u₁ := Wkp.firstOrder k u
    let w := W1p.contDiffSMul φ hφ hM (fun x _ => hφM x) (fun x _ => hgradM x) u₁
    let ψ := fun (i : Fin n) (x : X n) => fderiv ℝ φ x (WkpCalculus.e i)
    have hψ (i : Fin n) : ContDiff ℝ ∞ (ψ i) :=
      (hφ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hψc (i : Fin n) : HasCompactSupport (ψ i) := hc.fderiv_apply ℝ (WkpCalculus.e i)
    choose V hV using fun i : Fin n => ih hφ hc (d i k u)
    choose Z hZ using fun i : Fin n => ih (hψ i) (hψc i) (Wkp.lowerOrder k u)
    let g := fun (i : Fin n) => V i + Z i
    have hg (i : Fin n) : ⇑(Wkp.value k (g i)) =ᵐ[(volume : Measure (X n)).restrict Ω]
        (fun x => W1p.gradient w x i) := by
      filter_upwards [Lp.coeFn_add (Wkp.value k (V i)) (Wkp.value k (Z i)),
        hV i, hZ i, value_d i k u,
        W1p.gradient_contDiffSMul_ae hφ hM (fun x _ => hφM x) (fun x _ => hgradM x) u₁]
        with x h1 h2 h3 h4 h5
      have hv : W1p.value u₁ = Wkp.value k (Wkp.lowerOrder k u) := by
        rw [Wkp.value_firstOrder, Wkp.value_succ]
      have hψx : gradient φ x i = ψ i x := by
        unfold ψ
        rw [← inner_gradient_left (𝕜 := ℝ)]
        simp only [WkpCalculus.e, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
      simp only [g, Wkp.value_add]
      change _ = W1p.gradient (W1p.contDiffSMul φ hφ hM (fun x _ => hφM x) (fun x _ => hgradM x) u₁) x i
      rw [h1, Pi.add_apply, h2, h3, h4, h5, hv, PiLp.add_apply, PiLp.smul_apply,
        PiLp.smul_apply, hψx]
      simp only [smul_eq_mul, u₁]
      ring
    refine ⟨ofPartials k w g hg, ?_⟩
    rw [value_ofPartials]
    filter_upwards [W1p.value_contDiffSMul_ae hφ hM (fun x _ => hφM x) (fun x _ => hgradM x) u₁]
      with x hx
    change W1p.value (W1p.contDiffSMul φ hφ hM (fun x _ => hφM x) (fun x _ => hgradM x) u₁) x = _
    rw [hx, Wkp.value_firstOrder, smul_eq_mul]

end CalderonN.SobolevMultiplication
