module

public import Proof.CalderonN.ClassicalBallRepresentative
public import Proof.CalderonN.SmoothClosedRangeLift
public import Mathlib.Topology.ContinuousMap.Compact

import Proof.CalderonN.ClosedBallPointwise
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-! Adapted from `ClosedBallJetEvaluation` in the checked Theorem 3.1 release. -/

public section

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal

namespace CalderonN

variable {dim : ℕ} [NeZero dim]


open CalderonN.BallDirichlet

/-- Scalar ambient smooth data, with pointwise linear operations. -/
@[expose] def smoothBallDataSubmodule (dim : ℕ) : Submodule ℝ ((X dim) → ℝ) where
  carrier := {u | ContDiff ℝ ∞ u}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : (X dim) => (0:ℝ))
    exact contDiff_const
  add_mem' := fun {u v} hu hv => (show ContDiff ℝ ∞ u from hu).add
    (show ContDiff ℝ ∞ v from hv)
  smul_mem' := fun a u hu => (show ContDiff ℝ ∞ u from hu).const_smul a

theorem smoothBallData_contDiff (u : (smoothBallDataSubmodule dim)) : ContDiff ℝ ∞ u.1 := u.2

/-- Lift ambient smooth data into each native graph space. -/
@[expose] def smoothBallSobolevLinear (dim : ℕ) [NeZero dim] (m : ℕ) :
    (smoothBallDataSubmodule dim) →ₗ[ℝ] (BallSobolev dim) m where
  toFun u := smoothBallSobolev m ⟨u.1,smoothBallData_contDiff u⟩
  map_add' u v := by
    apply TauCeti.Wkp.ext m
    simp only [← TauCeti.Wkp.valueL_apply,map_add]
    simp only [TauCeti.Wkp.valueL_apply]
    apply Lp.ext
    filter_upwards [value_smoothBallSobolev_ae m ⟨(u+v).1,smoothBallData_contDiff (u+v)⟩,
      value_smoothBallSobolev_ae m ⟨u.1,smoothBallData_contDiff u⟩,
      value_smoothBallSobolev_ae m ⟨v.1,smoothBallData_contDiff v⟩,Lp.coeFn_add
        (TauCeti.Wkp.value m (smoothBallSobolev m ⟨u.1,smoothBallData_contDiff u⟩))
        (TauCeti.Wkp.value m (smoothBallSobolev m ⟨v.1,smoothBallData_contDiff v⟩))] with z huv hu hv hsum
    simp only [hsum,Pi.add_apply,hu,hv,huv]
    rfl
  map_smul' a u := by
    apply TauCeti.Wkp.ext m
    simp only [← TauCeti.Wkp.valueL_apply,map_smul]
    simp only [TauCeti.Wkp.valueL_apply]
    apply Lp.ext
    filter_upwards [value_smoothBallSobolev_ae m ⟨(a • u).1,smoothBallData_contDiff (a • u)⟩,
      value_smoothBallSobolev_ae m ⟨u.1,smoothBallData_contDiff u⟩,Lp.coeFn_smul a
        (TauCeti.Wkp.value m (smoothBallSobolev m ⟨u.1,smoothBallData_contDiff u⟩))] with z hau hu hsmul
    simp only [RingHom.id_apply,hsmul,Pi.smul_apply,hau,hu]
    rfl

abbrev BallJet (dim : ℕ) (k : ℕ) := (X dim) [×k]→L[ℝ] ℝ
abbrev UnitClosedBall (dim : ℕ) := ↥(closedBall (0 : (X dim)) 1)

instance : CompactSpace (UnitClosedBall dim) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : (X dim)) 1)

/-- The closed span of ambient smooth functions in a fixed Sobolev order. -/
@[expose] def closedBallSobolev (dim : ℕ) [NeZero dim] (m : ℕ) := ((smoothBallSobolevLinear dim) m).range.closure

abbrev ClosedBallSobolev (dim : ℕ) [NeZero dim] (m : ℕ) := ↥((closedBallSobolev dim) m)

instance completeSpace_closedBallSobolev (dim : ℕ) [NeZero dim] (m : ℕ) : CompleteSpace ((ClosedBallSobolev dim) m) := inferInstance

/-- The dense smooth inclusion into the closed Sobolev space. -/
@[expose] def denseSmoothBallSobolev (dim : ℕ) [NeZero dim] (m : ℕ) : (smoothBallDataSubmodule dim) →ₗ[ℝ] (ClosedBallSobolev dim) m :=
  ((smoothBallSobolevLinear dim) m).codRestrict ((closedBallSobolev dim) m).toSubmodule
    (fun u => Submodule.le_topologicalClosure _ ⟨u,rfl⟩)

theorem denseRange_denseSmoothBallSobolev (dim : ℕ) [NeZero dim] (m : ℕ) : DenseRange ((denseSmoothBallSobolev dim) m) := by
  refine Dense.mono ?_
    ((denseRange_inclusion_iff (Submodule.le_topologicalClosure ((smoothBallSobolevLinear dim) m).range)).mpr
      (by rw [Submodule.topologicalClosure_coe]))
  rintro _ ⟨x,rfl⟩
  obtain ⟨u,hu⟩ := x.2
  exact ⟨u,Subtype.ext hu⟩

/-- Evaluation of the spatial k-jet as a continuous function on the closed ball. -/
@[expose] def smoothBallJetLinear (dim : ℕ) [NeZero dim] (k : ℕ) : (smoothBallDataSubmodule dim) →ₗ[ℝ] C((UnitClosedBall dim),(BallJet dim) k) where
  toFun u := ⟨fun z => iteratedFDeriv ℝ k u.1 z,
    ((smoothBallData_contDiff u).continuous_iteratedFDeriv (by simp)).comp continuous_subtype_val⟩
  map_add' u v := by
    apply ContinuousMap.ext
    intro z
    change iteratedFDeriv ℝ k (u.1 + v.1) (z : (X dim)) = _
    exact iteratedFDeriv_add_apply ((smoothBallData_contDiff u).contDiffAt.of_le (by simp)) ((smoothBallData_contDiff v).contDiffAt.of_le (by simp))
  map_smul' a u := by
    apply ContinuousMap.ext
    intro z
    change iteratedFDeriv ℝ k (a • u.1) (z : (X dim)) = _
    exact iteratedFDeriv_const_smul_apply ((smoothBallData_contDiff u).contDiffAt.of_le (by simp))

/-- A single embedding constant works for all orders after dim + 1 more
spatial derivatives are included in the graph norm. -/
@[expose] def ballJetEmbeddingConstant (dim : ℕ) : ℝ :=
  ((dim : ℝ)+2) * ((2:ℝ)^(dim+1) / Real.sqrt (volume.real (closedBall (0 : (X dim)) 1)))

theorem ballJetEmbeddingConstant_nonneg (dim : ℕ) : 0 ≤ (ballJetEmbeddingConstant dim) := by
  unfold ballJetEmbeddingConstant
  positivity

set_option maxHeartbeats 2200000 in
theorem norm_smoothBallJetLinear_le (k m : ℕ) (hm : k+dim+1 ≤ m) (u : (smoothBallDataSubmodule dim)) :
    ‖(smoothBallJetLinear dim) k u‖ ≤ (ballJetEmbeddingConstant dim) * ‖(denseSmoothBallSobolev dim) m u‖ := by
  apply (ContinuousMap.norm_le ((smoothBallJetLinear dim) k u)
    (mul_nonneg (ballJetEmbeddingConstant_nonneg dim) (norm_nonneg _))).mpr
  intro z
  let W := smoothBallSobolev m ⟨u.1,smoothBallData_contDiff u⟩
  let f := iteratedFDeriv ℝ k u.1
  let μ := (volume : Measure (X dim)).restrict (ball (0 : (X dim)) 1)
  let C := closedBall (0 : (X dim)) 1
  let M : ℝ := (2:ℝ)^(dim+1) / Real.sqrt (volume.real C)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hW : ‖(denseSmoothBallSobolev dim) m u‖ = ‖W‖ := rfl
  have hf : ContDiff ℝ ∞ f := (smoothBallData_contDiff u).iteratedFDeriv_right (by simp)
  have hL (j : ℕ) (hj : j ∈ Finset.range (dim+2)) :
      Real.sqrt (∫ y in C, ‖iteratedFDeriv ℝ j f y‖^2) ≤ ‖W‖ := by
    have hD : eLpNorm (iteratedFDeriv ℝ j f) 2 μ ≤ ENNReal.ofReal ‖W‖ := by
      have hEq : eLpNorm (iteratedFDeriv ℝ j f) 2 μ = eLpNorm (iteratedFDeriv ℝ (j+k) u.1) 2 μ :=
        eLpNorm_congr_norm_ae
          ((hf.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
          (((smoothBallData_contDiff u).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
          (Eventually.of_forall (norm_iteratedFDeriv_iteratedFDeriv u.1 k j))
      rw [hEq]
      exact eLpNorm_iteratedFDeriv_le (fixedBallOpens dim) m W (smoothBallData_contDiff u).contDiffOn
        (value_smoothBallSobolev_ae m ⟨u.1,smoothBallData_contDiff u⟩) (j+k)
          (by have := Finset.mem_range.mp hj; omega)
    have hMem : MemLp (iteratedFDeriv ℝ j f) 2 μ :=
      hD.trans_lt ENNReal.ofReal_lt_top
    change Real.sqrt (∫ y, ‖iteratedFDeriv ℝ j f y‖^2 ∂(volume.restrict C)) ≤ ‖W‖
    rw [volume_restrict_closedUnitBall_eq,sqrt_integral_norm_sq_eq_eLpNorm_toReal hMem]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hD).trans_eq
      (ENNReal.toReal_ofReal (norm_nonneg _))
  change ‖f z‖ ≤ _
  rw [hW]
  have hfin : ((dim+1 : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr le_top
  refine (norm_le_unitBall_L2_jets (hf.of_le hfin) z.property).trans ?_
  calc
    _ ≤ M * ∑ j ∈ Finset.range (dim+2), ‖W‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hL) hM
    _ = _ := by simp [ballJetEmbeddingConstant,M,C]; ring

/-- The k-jet operator on the completion of smooth data. -/
@[expose] def closedBallJetL (dim : ℕ) [NeZero dim] (k m : ℕ) :
    (ClosedBallSobolev dim) m →L[ℝ] C((UnitClosedBall dim),(BallJet dim) k) :=
  LinearMap.extendOfNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (σ₁₂ := RingHom.id ℝ)
    (F := C((UnitClosedBall dim),(BallJet dim) k))
    ((smoothBallJetLinear dim) k) ((denseSmoothBallSobolev dim) m)

theorem closedBallJetL_on_smooth (k m : ℕ) (hm : k+dim+1 ≤ m) (u : (smoothBallDataSubmodule dim)) :
    (closedBallJetL dim) k m ((denseSmoothBallSobolev dim) m u) = (smoothBallJetLinear dim) k u :=
  LinearMap.extendOfNorm_eq ((denseRange_denseSmoothBallSobolev dim) m)
    ⟨_,norm_smoothBallJetLinear_le k m hm⟩ u

theorem norm_closedBallJetL_apply_le (k m : ℕ) (hm : k+dim+1 ≤ m)
    (u : (ClosedBallSobolev dim) m) (z : (UnitClosedBall dim)) :
    ‖(closedBallJetL dim) k m u z‖ ≤ (ballJetEmbeddingConstant dim) * ‖u‖ := by
  let L := (ContinuousMap.evalCLM ℝ z).comp ((closedBallJetL dim) k m)
  have hClosed : IsClosed {v : (ClosedBallSobolev dim) m |
      ‖L v‖ ≤ (ballJetEmbeddingConstant dim) * ‖v‖} :=
    isClosed_le L.continuous.norm (continuous_const.mul continuous_norm)
  have hMem : ∀ v ∈ Set.range ((denseSmoothBallSobolev dim) m),
      ‖L v‖ ≤ (ballJetEmbeddingConstant dim) * ‖v‖ := by
    rintro v ⟨b,rfl⟩
    change ‖(closedBallJetL dim) k m ((denseSmoothBallSobolev dim) m b) z‖ ≤ _
    rw [closedBallJetL_on_smooth k m hm]
    exact (ContinuousMap.norm_coe_le_norm _ z).trans (norm_smoothBallJetLinear_le k m hm b)
  exact ((denseRange_denseSmoothBallSobolev dim) m).induction hMem hClosed u

end CalderonN
