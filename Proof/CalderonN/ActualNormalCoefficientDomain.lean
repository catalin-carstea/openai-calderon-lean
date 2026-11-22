module

public import Proof.CalderonN.JointNormalCoefficientJets

import Proof.CalderonN.AffineNormalizedCenterJets
import Proof.CalderonN.FirstDensityJetBounds
import Mathlib.Tactic

/-! A common open smooth neighborhood for the actual first coefficient
on the controlled normal-coordinate tube. -/

public section

noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

theorem smoothNear_actual_firstNormalVelocityCoefficient
    {Y Ω : Set (X dim)} (hΩ : IsOpen Ω) {m : ℕ} {K ρ c₀ floor ε : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data dim}
    (hK : 0 < K) (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) :
    smoothNear (fun p : X dim × X dim => firstNormalVelocityCoefficient d p.1 p.2)
      {p | p.1 ∈ Y ∧ p.2 ∈ disk d.γ p.1 (max ρ (d.radius p.1)) ∧
        ‖normalVerticalJacobian d.expMap p.1 p.2-ContinuousLinearMap.id ℝ (X dim)‖ < 1} := by
  let P := X dim × X dim
  let E := d.expMap
  let V (q : P) := normalVerticalJacobian E q.1 q.2
  let F (q : P) := frameVectorLinear d.frame q.1
  let A (q : P) := d.g₁ (E q)
  let T (q : P) := (V q).comp (F q)
  let Q (q : P) : PullbackCoefficientData dim := (A q,T q)
  obtain ⟨W,hW,hTube,hE⟩ := hd.2.1.1
  let U₀ : Set P := W ∩ Prod.fst ⁻¹' Ω ∩ E ⁻¹' Ω
  have hU₁ : IsOpen (W ∩ Prod.fst ⁻¹' Ω) := hW.inter (hΩ.preimage continuous_fst)
  have hE₁ : ContDiffOn ℝ ∞ E (W ∩ Prod.fst ⁻¹' Ω) := hE.mono inter_subset_left
  have hU₀ : IsOpen U₀ := hE₁.continuousOn.isOpen_inter_preimage hU₁ hΩ
  have hSubW : U₀ ⊆ W := fun _ hx => hx.1.1
  have hSubO : MapsTo Prod.fst U₀ Ω := fun _ hx => hx.1.2
  have hSubE : MapsTo E U₀ Ω := fun _ hx => hx.2
  have hV : ContDiffOn ℝ ∞ V U₀ := by
    let R := (ContinuousLinearMap.compL ℝ (X dim) P (X dim)).flip
      (ContinuousLinearMap.inr ℝ (X dim) (X dim))
    have he : V = R ∘ fderiv ℝ E := funext fun _ => rfl
    rw [he]
    exact R.contDiff.comp_contDiffOn ((hE.fderiv_of_isOpen (m:=∞) hW (by simp)).mono hSubW)
  have hF : ContDiffOn ℝ ∞ F U₀ := by
    have hFrame (i : I dim) : ContDiffOn ℝ ∞ (fun q : P => d.frame q.1 i) U₀ :=
      (hd.1.2.2.2.2.2.2.1 i).comp contDiff_fst.contDiffOn hSubO
    unfold F frameVectorLinear
    exact ContDiffOn.sum (fun i _ => ((ContinuousLinearMap.smulRightL ℝ (X dim) (X dim))
      (EuclideanSpace.proj i)).contDiff.comp_contDiffOn (hFrame i))
  have hA : ContDiffOn ℝ ∞ A U₀ := by
    have hG : ContDiffOn ℝ ∞ d.g₁ Ω := contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => hd.1.2.1.1 i j
    exact hG.comp (hE.mono hSubW) hSubE
  have hT : ContDiffOn ℝ ∞ T U₀ := hV.clm_comp hF
  have hQ : ContDiffOn ℝ ∞ Q U₀ := hA.prodMk hT
  let R (q : P) := ‖V q-ContinuousLinearMap.id ℝ (X dim)‖
  let U := U₀ ∩ R ⁻¹' Iio 1
  have hU : IsOpen U := ((hV.continuousOn.sub continuousOn_const).norm).isOpen_inter_preimage hU₀ isOpen_Iio
  have hb : ContDiffOn ℝ ∞ (fun q : P => centerInverseDensity d q.1) U₀ :=
    (hd.1.contDiffOn_centerInverseDensity hK).comp contDiff_fst.contDiffOn hSubO
  refine ⟨U,hU,?_ ,?_⟩
  · intro q hq
    have hq' : q.1 ∈ Y ∧ q.2 ∈ disk d.γ q.1 (max ρ (d.radius q.1)) ∧ R q < 1 := hq
    exact ⟨⟨⟨hTube ⟨hq'.1,hq'.2.1⟩,hd.2.1.center_mem hq'.1⟩,
      (hd.2.1.2 q.1 hq'.1).2.2 q.2 hq'.2.1 |>.1⟩, hq'.2.2⟩
  · intro q hq
    have hq₀ : q ∈ U₀ := hq.1
    have hFrame := hd.1.2.2.2.2.2.2.2 q.1 (hSubO hq₀)
    have hFi : Function.Injective (F q) := by
      intro x y hxy
      have h0 : F q (x-y) = 0 := by rw [map_sub,hxy,sub_self]
      have hLow := (hd.1.1.frameVector_norm_sq_bounds hK (hSubO hq₀) d.frame hFrame (x-y)).1
      rw [← frameVectorLinear_apply] at hLow
      change ‖x-y‖^2 ≤ K*‖F q (x-y)‖^2 at hLow
      rw [h0,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] at hLow
      exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x-y)] : ‖x-y‖ = 0))
    have hVi : Function.Injective (V q) := by
      intro x y hxy
      let u := x-y
      have h0 : V q u = 0 := by
        change V q (x-y) = 0
        rw [map_sub,hxy,sub_self]
      have h := (V q-ContinuousLinearMap.id ℝ (X dim)).le_opNorm u
      rw [ContinuousLinearMap.sub_apply,ContinuousLinearMap.id_apply,h0,zero_sub,norm_neg] at h
      have hR : R q < 1 := hq.2
      by_contra hne
      have hu : 0 < ‖u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have hn := mul_lt_mul_of_pos_right hR hu
      exact (not_lt_of_ge h) (hn.trans_eq (one_mul _))
    have hAp : (A q).PosDef := hd.1.2.1.posDef hK (hSubE hq₀)
    have hTinj : Function.Injective (T q) := hVi.comp hFi
    have hOuter := contDiffAt_pullbackDivergenceMatrix_of_posDef (Q q) (pullbackMetricMatrix_posDef hAp hTinj)
    have hLocal : ContDiffAt ℝ ∞ (fun q => centerInverseDensity d q.1 • pullbackDivergenceMatrix (Q q)) q :=
      (hb.contDiffAt (hU₀.mem_nhds hq₀)).smul (hOuter.comp q (hQ.contDiffAt (hU₀.mem_nhds hq₀)))
    exact hLocal.contDiffWithinAt

end CalderonN
