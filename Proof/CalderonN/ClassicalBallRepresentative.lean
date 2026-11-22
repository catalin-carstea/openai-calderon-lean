module

public import Proof.CalderonN.SobolevClosedBallRepresentative
public import Proof.CalderonN.ClosedBallSmoothExtension
public import Proof.CalderonN.BallRegularity.NativeSmoothBallSobolev

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic

public section

noncomputable section
open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ContDiff ENNReal

set_option maxHeartbeats 1800000

namespace CalderonN

variable {dim : ℕ} [NeZero dim]



open CalderonN.BallDirichlet

/-- A single ambient smooth representative of a function in all the
native fixed-ball Sobolev orders. -/
theorem exists_smooth_ballRepresentative {w : (X dim) → ℝ}
    (hW : ∀ m, ∃ u : (BallSobolev dim) m,
      TauCeti.Wkp.value m u =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] w) :
    ∃ b : (X dim) → ℝ, ContDiff ℝ ∞ b ∧ b =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] w := by
  let B := ball (0 : (X dim)) 1
  let μ := (volume : Measure (X dim)).restrict (fixedBallOpens dim)
  obtain ⟨b,hb,hv⟩ := exists_contDiffOn_ae_eq (O := B) isOpen_ball (w := w) (by
    intro x hx
    let r := 1-‖x‖
    have hr : 0 < r := sub_pos.mpr (mem_ball_zero_iff.mp hx)
    let V : Opens (X dim) := ⟨ball x r,isOpen_ball⟩
    have hv : (V : Set (X dim)) ⊆ B := by
      apply ball_subset_ball'
      simp [r,dist_zero_right]
    have hVB : V ≤ (fixedBallOpens dim) := hv
    refine ⟨r,hr,hv,fun m => ?_⟩
    obtain ⟨u,hu⟩ := hW m
    refine ⟨TauCeti.Wkp.restrictL hVB m u,?_⟩
    exact (TauCeti.Wkp.value_restrictL_ae hVB m u).trans
      (ae_restrict_of_ae_restrict_of_subset hv hu))
  have hMem (k : ℕ) : MemLp (iteratedFDeriv ℝ k b) 2 μ := by
    obtain ⟨u,hu⟩ := hW k
    exact (eLpNorm_iteratedFDeriv_le (fixedBallOpens dim) k u hb (hu.trans hv.symm) k le_rfl).trans_lt
      ENNReal.ofReal_lt_top
  obtain ⟨F,hF,hFE⟩ := exists_contDiffOn_closedUnitBall_of_bulk_jets hb hMem
  let χ : ContDiffBump (0 : ℝ) :=
    {rIn := 1,rOut := 2,rIn_pos := one_pos,rIn_lt_rOut := by norm_num}
  let f (q : ℝ × (X dim)) := χ q.1 * F q.2
  have hf : ContDiffOn ℝ ∞ f (univ ×ˢ closedBall (0 : (X dim)) 1) :=
    (χ.contDiff.comp contDiff_fst).contDiffOn.mul
      (hF.comp contDiff_snd.contDiffOn (fun _ h => h.2))
  obtain ⟨G,hG,hGE⟩ := exists_smooth_extension_prod_closedUnitBall hf
    χ.hasCompactSupport.isCompact (by
      intro p hp z
      simp [f,image_eq_zero_of_notMem_tsupport hp])
  let u (z : (X dim)) := G (0,z)
  refine ⟨u,hG.comp (contDiff_const.prodMk contDiff_id),?_⟩
  filter_upwards [hv,ae_restrict_mem measurableSet_ball] with z hz hzB
  change G (0,z) = w z
  rw [hGE (show (0,z) ∈ univ ×ˢ closedBall (0 : (X dim)) 1 from ⟨mem_univ _,ball_subset_closedBall hzB⟩)]
  change χ 0 * F z = w z
  rw [χ.one_of_mem_closedBall (by simp [χ]),one_mul,hFE hzB,hz]

set_option maxHeartbeats 1500000 in
/-- Apply the all-order agreement of the strong inverses to obtain one
ambient smooth representative at the selected parameter. -/
theorem exists_smooth_strongBallRepresentative {U : (s : ℕ) → (StrongDirichletSpace dim) s}
    (hU : ∀ s, (strongDirichletProjectionL dim) s (U s) = (strongDirichletProjectionL dim) 0 (U 0)) :
    ∃ b : (X dim) → ℝ, ContDiff ℝ ∞ b ∧
      TauCeti.W1p.value ((strongDirichletProjectionL dim) 0 (U 0) : FixedBallH1 dim)
        =ᵐ[(volume : Measure (X dim)).restrict (fixedBallOpens dim)] b := by
  obtain ⟨b,hb,hbv⟩ := exists_smooth_ballRepresentative
    (w := ⇑(TauCeti.W1p.value ((strongDirichletProjectionL dim) 0 (U 0) : FixedBallH1 dim))) (by
      intro k
      let W : (BallSobolev dim) (k+2) := U k
      have hk : TauCeti.Wkp.value (k+2) W =
          TauCeti.W1p.value ((strongDirichletProjectionL dim) 0 (U 0) : FixedBallH1 dim) := by
        have h := congrArg (fun v : FixedBallH1Zero dim => TauCeti.W1p.value (v : FixedBallH1 dim)) (hU k)
        change TauCeti.W1p.value ((strongDirichletProjectionL dim) k (U k) : FixedBallH1 dim) = _ at h
        rw [strongDirichletProjectionL_apply,TauCeti.Wkp.value_firstOrder] at h
        exact h
      obtain ⟨v,_,hv⟩ := exists_lower (fixedBallOpens dim) (k+2) W k (by omega)
      exact ⟨v,by rw [hv,hk]⟩)
  exact ⟨b,hb,hbv.symm⟩

end CalderonN
