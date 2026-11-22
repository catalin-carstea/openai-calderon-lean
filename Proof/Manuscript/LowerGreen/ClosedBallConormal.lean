module

public import Proof.CalderonN.ClosedBallJetSmooth
public import Proof.CalderonN.ParametricBallConormal

public import Proof.CalderonN.BallRotationConormal
import Proof.Manuscript.LowerGreen.ContinuousCompactIntegral
import Mathlib.Tactic

public section

noncomputable section

open Set Metric Filter MeasureTheory CalderonN CalderonN.BallDirichlet
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]

set_option maxHeartbeats 1600000

local instance : NormedAddCommGroup (BallJet n 1 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance : NormedSpace ℝ (BallJet n 1 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- Contract the boundary gradient jet with the outward Euclidean normal
and the divergence coefficient. -/
@[expose] def conormalJetL (a : Mat n) (w : X n) : BallJet n 1 →L[ℝ] ℝ :=
  ∑ i : I n, ∑ j : I n, (w i * a i j) •
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => X n) ℝ (fun _ => axis j)

theorem conormalJetL_apply (a : Mat n) (w : X n) (b : BallJet n 1) :
    conormalJetL a w b = ∑ i : I n, ∑ j : I n, (w i * a i j) * b (fun _ => axis j) := by
  simp [conormalJetL,smul_eq_mul]

theorem contDiff_conormalJetL :
    ContDiff ℝ ∞ (fun q : Mat n × X n => conormalJetL q.1 q.2) := by
  unfold conormalJetL
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd).mul
    (((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).contDiff.comp contDiff_fst)).smul contDiff_const

/-- The conormal of a function in the closed Sobolev model at a given
boundary point, with no ambient extension of that function. -/
@[expose] def closedBallConormal (a : X n → Mat n) (s : ℕ) (u : ClosedBallSobolev n s)
    (w : ↥(standardSphere n)) : ℝ :=
  conormalJetL (a w) w ((closedBallJetL n 1 s u) ⟨w,sphere_subset_closedBall w.property⟩)

theorem closedBallConormal_smooth (a : X n → Mat n) (s : ℕ) (hs : 1+n+1 ≤ s)
    (u : smoothBallDataSubmodule n) (w : ↥(standardSphere n)) :
    closedBallConormal a s (denseSmoothBallSobolev n s u) w = smoothBallConormal a u.1 w := by
  rw [closedBallConormal,closedBallJetL_on_smooth 1 s hs]
  rw [smoothBallConormal,EuclideanSpace.inner_eq_star_dotProduct]
  simp only [conormalJetL_apply,star_trivial,dotProduct,smoothBallFlux_apply,
    smoothBallJetLinear,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.coe_mk,
    iteratedFDeriv_one_apply,Fin.isValue,coordDeriv,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Evaluate the closed-ball conormal after projecting the angular
coordinate radially onto the sphere, on an open parameter domain. -/
@[expose] def radialClosedBallConormal (a : P × X n → Mat n) (s : ℕ)
    (u : P → ClosedBallSobolev n s) (q : P × X n) : ℝ :=
  conormalJetL (a (q.1,sphereNormalize q.2)) (sphereNormalize q.2)
    (closedBallEval n 1 s (sphereNormalize q.2) (u q.1))

theorem radialClosedBallConormal_eq_on_sphere (a : P × X n → Mat n) (s : ℕ)
    (u : P → ClosedBallSobolev n s) (p : P) (w : ↥(standardSphere n)) :
    radialClosedBallConormal a s u (p,w) = closedBallConormal (fun z => a (p,z)) s (u p) w := by
  unfold radialClosedBallConormal closedBallConormal
  rw [sphereNormalize_eq_of_sphere w.property]
  rw [closedBallEval_apply 1 s _ (⟨w,sphere_subset_closedBall w.property⟩ : UnitClosedBall n)]

theorem contDiffOn_radialClosedBallConormal
    {a : P × X n → Mat n} (ha : ContDiff ℝ ∞ a) {s k : ℕ} (hs : 1+k+n+3 ≤ s)
    {u : P → ClosedBallSobolev n s} {V : Set P} (hu : ContDiffOn ℝ ∞ u V) :
    ContDiffOn ℝ k (radialClosedBallConormal a s u) (V ×ˢ ({0}ᶜ : Set (X n))) := by
  let Ω := V ×ˢ ({0}ᶜ : Set (X n))
  have hz : ContDiffOn ℝ ∞ (fun q : P × X n => sphereNormalize q.2) Ω :=
    contDiffOn_sphereNormalize.comp contDiff_snd.contDiffOn (fun _ h => h.2)
  have hBall q (hq : q ∈ Ω) : sphereNormalize q.2 ∈ closedBall (0 : X n) 1 :=
    sphere_subset_closedBall (sphereNormalize_mem_sphere hq.2)
  have hW := contDiffOn_closedBallEval_order s k 1 hs
  have hU : ContDiffOn ℝ k (fun q : P × X n => u q.1) Ω :=
    (hu.comp contDiff_fst.contDiffOn (fun _ h => h.1)).of_le (by simp)
  have hPair := contDiff_fst.contDiffOn.prodMk hz
  exact ((contDiff_conormalJetL.comp_contDiffOn
    ((ha.comp_contDiffOn hPair).prodMk hz)).of_le (by simp)).clm_apply
      ((hW.comp (hz.of_le (by simp)) hBall).clm_apply hU)

/-- Integration against a fixed smooth trace is continuous in the
Sobolev data, because the conormal-jet evaluation is continuous on
the closed sphere. -/
theorem continuous_integral_closedBallConormal (a : X n → Mat n) (ha : Continuous a)
    (s : ℕ) (v : SmoothData n) :
    Continuous (fun u : ClosedBallSobolev n s =>
      ∫ w : ↥(standardSphere n), closedBallConormal a s u w * v.1 w ∂(chartSurfaceMeasure n)) := by
  let U := ↥(standardSphere n)
  let : CompactSpace U := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : X n) 1)
  let I : U → UnitClosedBall n := fun w => ⟨w,sphere_subset_closedBall w.property⟩
  have hI : Continuous I := continuous_subtype_val.subtype_mk _
  have hW : Continuous (fun q : ClosedBallSobolev n s × U => (q.2 : X n)) :=
    continuous_subtype_val.comp continuous_snd
  have hEval : Continuous (fun q : C(UnitClosedBall n,BallJet n 1) × UnitClosedBall n => q.1 q.2) :=
    continuous_eval
  let G (q : ClosedBallSobolev n s × U) := closedBallJetL n 1 s q.1 (I q.2)
  have hG : Continuous G := hEval.comp (((closedBallJetL n 1 s).continuous.comp continuous_fst).prodMk
    (hI.comp continuous_snd))
  have hCV : Continuous (fun q : ClosedBallSobolev n s × U =>
      closedBallConormal a s q.1 q.2 * v.1 q.2) := by
    unfold closedBallConormal
    simp_rw [conormalJetL_apply]
    apply Continuous.mul _ (v.2.continuous.comp hW)
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    have hB : Continuous (fun q : ClosedBallSobolev n s × U => G q (fun _ => axis j)) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 => X n) ℝ (fun _ => axis j)).continuous.comp hG
    exact ((((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hW)).mul
      (((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap).continuous.comp (ha.comp hW))).mul hB
  exact continuous_integral_of_joint_continuous (chartSurfaceMeasure n) hCV

end CalderonPaper.LowerGreen

end
