module

public import Proof.CalderonPatch.ConvexPoincare
public import Proof.CalderonPatch.BoundaryGreenBox

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff ENNReal Interval Topology

namespace CalderonPatch

open CalderonN (X axis norm_axis)

variable {m : ℕ}

private theorem insertNth_zero_affine (s : ℝ) (z : Fin m → ℝ) :
    (WithLp.toLp 2 (Fin.insertNth (0 : Fin (m + 1)) s z) : X (m + 1)) =
      s • axis 0 + WithLp.toLp 2 (Fin.insertNth (0 : Fin (m + 1)) 0 z) := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [axis,PiLp.smul_apply,PiLp.add_apply]
  · simp [axis,PiLp.smul_apply,PiLp.add_apply]

private theorem continuous_normal_insertNth :
    Continuous (fun p : ℝ × (Fin m → ℝ) => Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) 0 p.1 p.2) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using (continuous_fst (X := ℝ) (Y := Fin m → ℝ))
  · simpa only [Fin.insertNth_zero',Fin.cons_succ,Function.comp_def] using (continuous_apply i).comp (continuous_snd (X := ℝ) (Y := Fin m → ℝ))

/-- Integrating along the normal fibers of a closed rectangular box. -/
private theorem integral_box_insertNth
    (a b : Fin (m + 1) → ℝ) {f : (Fin (m + 1) → ℝ) → ℝ} (hf : Continuous f) :
    (∫ y in Icc a b, f y) =
      ∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0),
        ∫ s in Icc (a 0) (b 0), f (Fin.insertNth (0 : Fin (m + 1)) s z) := by
  let P := Icc (a 0) (b 0)
  let Q := Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hE : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 0
  have hF : ∀ p : ℝ × (Fin m → ℝ), e.symm p = Fin.insertNth (0 : Fin (m + 1)) p.1 p.2 := fun _ => rfl
  have hP : e ⁻¹' (P ×ˢ Q) = Icc a b := by
    ext y
    constructor
    · intro hy
      have hb : e y ∈ P ×ˢ Q := hy
      have h := insertNth_mem_box 0 hb.1 hb.2
      rw [← hF, e.symm_apply_apply] at h
      exact h
    · intro hy
      exact ⟨⟨hy.1 0,hy.2 0⟩,⟨fun i => hy.1 (Fin.succAbove 0 i),
        fun i => hy.2 (Fin.succAbove 0 i)⟩⟩
  have hC : Continuous (fun p : ℝ × (Fin m → ℝ) => f (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2)) :=
    hf.comp (continuous_normal_insertNth)
  have hI : Integrable (fun p : ℝ × (Fin m → ℝ) => f (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2))
      ((volume.restrict P).prod (volume.restrict Q)) := by
    rw [Measure.prod_restrict]
    exact hC.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  calc
    _ = ∫ p in P ×ˢ Q, f (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2) := by
      have hh := hE.setIntegral_preimage_emb e.measurableEmbedding (f ∘ e.symm) (P ×ˢ Q)
      rw [hP] at hh
      simpa only [Function.comp_apply,e.symm_apply_apply,hF] using hh
    _ = _ := by
      change (∫ p, f (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2)
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).restrict (P ×ˢ Q)) = _
      rw [← Measure.prod_restrict,integral_prod_symm _ hI]

/-- A zero trace along the bottom of the half-box controls the
squared function by the squared differential throughout the
box. The constant is the square of its height. -/
theorem integral_sq_le_height_sq_integral_fderiv_of_box_zero_trace
    {a b : Fin (m + 1) → ℝ} (hab : a ≤ b) (ha : a 0 = 0)
    {u : X (m + 1) → ℝ} (hu : ContDiff ℝ 1 u)
    (hZero : EqOn (fun z => u (WithLp.toLp 2 (Fin.insertNth (0 : Fin (m + 1)) 0 z))) 0
      (Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0))) :
    (∫ y in Icc a b, u (WithLp.toLp 2 y)^2) ≤
      (b 0)^2 * ∫ y in Icc a b, ‖fderiv ℝ u (WithLp.toLp 2 y)‖^2 := by
  let P := Icc (a 0) (b 0)
  let Q := Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0)
  let f (y : Fin (m + 1) → ℝ) := u (WithLp.toLp 2 y)^2
  let q (y : Fin (m + 1) → ℝ) := ‖fderiv ℝ u (WithLp.toLp 2 y)‖^2
  have hTo : Continuous (WithLp.toLp 2 : (Fin (m + 1) → ℝ) → X (m + 1)) :=
    (WithLp.linearEquiv 2 ℝ _).symm.toContinuousLinearEquiv.continuous
  have hf : Continuous f := (hu.continuous.comp hTo).pow 2
  have hq : Continuous q := ((hu.continuous_fderiv one_ne_zero).comp hTo).norm.pow 2
  have hb : 0 ≤ b 0 := ha ▸ hab 0
  have hFibre (z : Fin m → ℝ) (hz : z ∈ Q) :
      (∫ s in P, f (Fin.insertNth (0 : Fin (m + 1)) s z)) ≤ (b 0)^2 * ∫ s in P, q (Fin.insertNth (0 : Fin (m + 1)) s z) := by
    let γ (s : ℝ) : X (m + 1) := WithLp.toLp 2 (Fin.insertNth (0 : Fin (m + 1)) s z)
    let v (s : ℝ) := u (γ s)
    let d (s : ℝ) := fderiv ℝ u (γ s) (axis 0)
    let w (s : ℝ) := q (Fin.insertNth (0 : Fin (m + 1)) s z)
    have hγd (s : ℝ) : HasDerivAt γ (axis 0) s := by
      rw [show γ = _ from funext (fun t => insertNth_zero_affine t z)]
      simpa only [id_eq,one_smul] using
        ((hasDerivAt_id s).smul_const (axis (0 : Fin (m+1)))).add_const
          (WithLp.toLp 2 (Fin.insertNth (0 : Fin (m + 1)) 0 z))
    have hγ : Continuous γ := continuous_iff_continuousAt.mpr fun s => (hγd s).continuousAt
    have hD (s : ℝ) : HasDerivAt v (d s) s :=
      (hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s (hγd s)
    have hd : Continuous d := ((hu.continuous_fderiv one_ne_zero).comp hγ).clm_apply continuous_const
    have hw : Continuous w := ((hu.continuous_fderiv one_ne_zero).comp hγ).norm.pow 2
    have hz₀ : v 0 = 0 := hZero hz
    have hPoint (t : ℝ) (ht : t ∈ P) : (v t)^2 ≤ b 0 * ∫ s in P, w s := by
      have ht₀ : 0 ≤ t := ha ▸ ht.1
      have hQ : (∫ s in Icc (0 : ℝ) t, (d s)^2) ≤ ∫ s in P, w s := by
        calc
          _ ≤ ∫ s in Icc (0 : ℝ) t, w s := by
            apply setIntegral_mono_on ((hd.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
              (hw.continuousOn.integrableOn_compact isCompact_Icc) measurableSet_Icc
            intro s _
            have hN := (fderiv ℝ u (γ s)).le_opNorm (axis 0)
            rw [norm_axis,mul_one] at hN
            change (d s)^2 ≤ w s
            rw [← sq_abs (d s)]
            exact pow_le_pow_left₀ (abs_nonneg _) hN 2
          _ ≤ _ := setIntegral_mono_set (hw.continuousOn.integrableOn_compact isCompact_Icc)
            (Eventually.of_forall fun _ => sq_nonneg _)
            (Eventually.of_forall fun _ hs => ⟨ha ▸ hs.1,hs.2.trans ht.2⟩)
      have h₁ := sq_sub_le_mul_integral_sq_of_hasDerivAt ht₀ hD hd
      rw [hz₀,sub_zero,sub_zero] at h₁
      exact h₁.trans ((mul_le_mul_of_nonneg_left hQ ht₀).trans
        (mul_le_mul_of_nonneg_right ht.2 (integral_nonneg fun _ => sq_nonneg _)))
    have hv₂ : Continuous (fun s => (v s)^2) := (hu.continuous.comp hγ).pow 2
    calc
      _ ≤ ∫ _ in P, b 0 * ∫ s in P, w s := setIntegral_mono_on
        (hv₂.continuousOn.integrableOn_compact isCompact_Icc) (integrable_const _)
        measurableSet_Icc hPoint
      _ = _ := by
        have hm : (volume : Measure ℝ).real P = b 0 := by
          rw [Measure.real,show P = Icc (a 0) (b 0) from rfl,Real.volume_Icc,ha,sub_zero,
            ENNReal.toReal_ofReal hb]
        rw [setIntegral_const,smul_eq_mul,hm,pow_two,mul_assoc]
  change (∫ y in Icc a b, f y) ≤ (b 0)^2 * ∫ y in Icc a b, q y
  rw [integral_box_insertNth a b hf,integral_box_insertNth a b hq,← integral_const_mul]
  have hC : Continuous (fun p : ℝ × (Fin m → ℝ) => Fin.insertNth (α := fun _ : Fin (m + 1) => ℝ) 0 p.1 p.2) :=
    continuous_normal_insertNth
  have hI {g : (Fin (m + 1) → ℝ) → ℝ} (hg : Continuous g) :
      Integrable (fun p : ℝ × (Fin m → ℝ) => g (Fin.insertNth (0 : Fin (m + 1)) p.1 p.2))
        ((volume.restrict P).prod (volume.restrict Q)) := by
    rw [Measure.prod_restrict]
    exact (hg.comp hC).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact setIntegral_mono_on (hI hf).integral_prod_right
    ((hI hq).integral_prod_right.const_mul _) measurableSet_Icc hFibre

end CalderonPatch
