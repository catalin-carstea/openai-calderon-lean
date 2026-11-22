module

public import Proof.CalderonN.NativeCoefficientBallPoisson

import Proof.CalderonN.ClassicalBallDirichlet
import Mathlib.Tactic

public section

noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The fixed-ball strong inverse, applied to smooth forcing, gives
the classically smooth zero-Dirichlet solution for that coefficient. -/
theorem exists_native_classical_zeroDirichlet
    (F : SmoothCoefficientMatrix dim 2) {lo hi : ℝ}
    (hEll : TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (coefficientMatrixField 2 F) lo hi)
    (g : SmoothData dim) :
    ∃ v : SmoothData dim,
      EqOn v.1 0 (standardSphere dim) ∧
      EqOn (negativeBallDivergence (coefficientMatrixField 2 F) v.1) g.1 (ball (0 : X dim) 1) ∧
      smoothBallSobolev 2 v =
        (((strongDirichletSubmodule dim) 0).toSubmodule.subtypeL.comp
          (strongDirichletOperator fixedSobolevCalculus 0 F).inverse)
          (smoothBallSobolev 0 g) := by
  obtain ⟨a,ha,K,hK,hS,rfl,hA⟩ := exists_constantFamily_of_coefficientMatrix 2 F
  let χ := unitBallSmoothCutoff dim
  let f : ℝ × X dim → ℝ := fun p => χ p.2 * g.1 p.2
  have hf : ContDiff ℝ ∞ f := (χ.contDiff.mul g.2).comp contDiff_snd
  let J := tsupport (χ : X dim → ℝ)
  have hJ : IsCompact J := χ.hasCompactSupport
  have hSupp (p : ℝ) (z : X dim) (hz : z ∉ J) : f (p,z) = 0 := by
    change χ z * g.1 z = 0
    rw [image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have hfEq (z : X dim) (hz : z ∈ fixedBallOpens dim) : f (0,z) = g.1 z := by
    change χ z * g.1 z = _
    rw [unitBallSmoothCutoff_one_of_mem hz,one_mul]
  have hEllParam (p : ℝ) (_ : p ∈ univ) :
      TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
        (fun z => (coefficientMatrixField 2 F ∘ Prod.snd) (p,z)) lo hi := hEll
  obtain ⟨U,_,hU⟩ := exists_parametric_ballStrongSolution univ _ ha K hK hS
    f hf J hJ hSupp (fun _ => lo) (fun _ => hi) hEllParam
  have hSols (s : ℕ) := hU 0 (mem_univ 0) s
  obtain ⟨v,hv,hVal⟩ := exists_smooth_strongBallRepresentative (U := fun s => U s 0)
    (fun s => (hSols s).1)
  let w := (strongDirichletProjectionL dim) 0 (U 0 0)
  have hAs : ContDiff ℝ ∞ (coefficientMatrixField 2 F) :=
    ha.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  have hFs : ContDiff ℝ ∞ (fun z => f (0,z)) :=
    hf.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  have hL := negativeBallDivergence_eq_of_ballWeakSolution hAs hFs hv w hVal _
    (ballForcingFamily_value 0 f hf J hJ hSupp 0) (hSols 0).2.1
  refine ⟨⟨v,hv⟩,eqOn_zero_sphere_of_ballH1Zero hv w hVal,fun z hz => (hL hz).trans (hfEq z hz),?_⟩
  have hRep : (U 0 0 : BallSobolev dim 2) = smoothBallSobolev 2 ⟨v,hv⟩ := by
    apply TauCeti.Wkp.ext 2
    apply Lp.ext
    have he : TauCeti.Wkp.value 2 (U 0 0 : BallSobolev dim 2) = TauCeti.W1p.value (w : FixedBallH1 dim) := by
      change TauCeti.Wkp.value 2 (U 0 0 : BallSobolev dim 2) =
        TauCeti.W1p.value (((strongDirichletProjectionL dim) 0 (U 0 0)) : FixedBallH1 dim)
      rw [strongDirichletProjectionL_apply,TauCeti.Wkp.value_firstOrder]
    rw [he]
    exact hVal.trans (value_smoothBallSobolev_ae 2 ⟨v,hv⟩).symm
  have hForce : ballForcingFamily 0 f hf J hJ hSupp 0 = smoothBallSobolev 0 g := by
    apply TauCeti.Wkp.ext 0
    apply Lp.ext
    have hM := ae_restrict_mem (μ := (volume : Measure (X dim))) (fixedBallOpens dim).isOpen.measurableSet
    filter_upwards [ballForcingFamily_value 0 f hf J hJ hSupp 0,value_smoothBallSobolev_ae 0 g,hM]
      with z hz hz' hM
    exact hz.trans ((hfEq z hM).trans hz'.symm)
  have hInv := (hSols 0).2.2
  rw [hA 0,hForce] at hInv
  rw [← hRep,hInv]
  rfl

end CalderonN
