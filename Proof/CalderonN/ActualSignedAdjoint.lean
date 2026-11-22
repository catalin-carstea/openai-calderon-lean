module

public import Proof.CalderonN.SignedNormalAdjoint
public import Proof.CalderonN.ActualMovingTraceAdjoint
public import Proof.CalderonN.ConstantMovingTraceAlgebra

import Proof.CalderonN.BallVelocityDatumCongruence
import Mathlib.Tactic

/-! Adapted from `ActualSignedAdjoint` in the checked Theorem 3.1 release. -/

public section

set_option maxHeartbeats 2200000

noncomputable section
open Set Metric
open scoped ContDiff

namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

/-- The signed parameter of an actual shrinking radius at a center. -/
@[expose] def actualSignedNormalParameter (lam : ℝ) (r : (X dim) → ℝ) (y : (X dim)) :
    (SignedNormalParameter dim) :=
  (lam,(y,(r y,fun k => coordDeriv k r y)))

/-- On a real sphere datum, the actual moving adjoint multiplied by its
radius agrees with the signed fixed-ball adjoint. -/
theorem scaled_actualMovingTraceAdjoint_eq_signed {Y : Set (X dim)}
    {γ g : ℝ → (MetricField dim)} {E : ℝ → (X dim) × (X dim) → (X dim)} {e : ℝ → (Frame dim)}
    {lam : ℝ} {r : (X dim) → ℝ} {y : (X dim)} (hy : y ∈ Y) (hR : r y ≠ 0)
    (he : ∀ i j, metricPair (γ lam) y (e lam y i) (e lam y j) = if i=j then 1 else 0)
    (i : (I dim)) (v : (Field dim)) (hv : smoothNear v (bundle Y (γ lam)))
    (φ : (SignedNormalParameter dim) × (X dim) → ℝ)
    {U T : Set (X dim)} (hU : IsOpen U) (hT : IsOpen T)
    (hCU : closedBall (0 : (X dim)) 1 ⊆ U)
    (hST : (standardSphere dim) ⊆ T) (hTU : T ⊆ U) (hT₀ : (0 : (X dim)) ∉ T)
    (hm : SmoothMetric U (fun z => signedNormalMetric g E e (actualSignedNormalParameter lam r y,z)))
    (hV : ContDiffOn ℝ ∞
      (fun z => signedNormalVelocity γ E e i (actualSignedNormalParameter lam r y,z)) T)
    (hφ : ContDiffOn ℝ ∞ (fun z => φ (actualSignedNormalParameter lam r y,z)) T)
    (hdata : ∀ z ∈ (standardSphere dim), v (y,frameVector (e lam) y z) =
      (φ (actualSignedNormalParameter lam r y,z) : ℂ))
    {w : (X dim)} (hw : w ∈ (standardSphere dim)) :
    (r y : ℂ) * adjointField (actualMovingTraceAdjoint (γ lam) (g lam) (E lam) (e lam) r) i v
        (y,frameVector (e lam) y w) =
      (parametricBallVelocityAdjoint (signedNormalMetric g E e) (signedNormalVelocity γ E e i)
        φ (actualSignedNormalParameter lam r y,w) : ℂ) := by
  let p := actualSignedNormalParameter lam r y
  let m := signedNormalMetric g E e
  let V := signedNormalVelocity γ E e i
  let a := movingBallMetric (g lam) (E lam) (e lam) r
  let B := movingBallScaledVelocity (γ lam) (E lam) (e lam) r i
  let F (z : (X dim)) := (y,frameVector (e lam) y z)
  have hF : ContDiff ℝ ∞ F := contDiff_const.prodMk
    (by simpa only [show ⇑(frameVectorL (e lam y)) = frameVector (e lam) y from
      funext (frameVectorL_apply_frame (e lam) y)] using (frameVectorL (e lam y)).contDiff (n := ∞))
  obtain ⟨S,hS,hBS,hvs⟩ := hv
  let J := T ∩ F ⁻¹' S
  have hJ : IsOpen J := hT.inter (hS.preimage hF.continuous)
  have hSJ : (standardSphere dim) ⊆ J :=
    fun z hz => ⟨hST hz,hBS ⟨hy,frameVector_mem_sphere (γ lam) (e lam) y he ⟨z,hz⟩⟩⟩
  have hvJ : ContDiffOn ℝ ∞ (v ∘ F) J := hvs.comp hF.contDiffOn (fun _ hz => hz.2)
  have ha : (fun z => a (y,z)) = (fun z => m (p,z)) := rfl
  have hb : (fun z => B (y,z)) = (fun z => V (p,z)) := rfl
  have hva : ContDiffOn ℝ ∞ (fun z => B (y,z)) J := by
    rw [hb]
    exact hV.mono inter_subset_left
  have hma : SmoothMetric U (fun z => a (y,z)) := ha.symm ▸ hm
  have hre := parametricBallVelocityAdjoint_congr_slice
    (φ := realMovingVelocityDatum (e lam) v) (ψ := φ) ha hb hU hJ hCU hSJ
    (inter_subset_left.trans hTU) (fun hz => hT₀ hz.1) hma hva
    (Complex.reCLM.contDiff.comp_contDiffOn hvJ) (hφ.mono inter_subset_left)
    (fun z hz => by
      change (v (y,frameVector (e lam) y z)).re = _
      rw [hdata z hz,Complex.ofReal_re]) hw
  have him := parametricBallVelocityAdjoint_congr_slice
    (φ := imagMovingVelocityDatum (e lam) v) (ψ := fun _ => 0) ha hb hU hJ hCU hSJ
    (inter_subset_left.trans hTU) (fun hz => hT₀ hz.1) hma hva
    (Complex.imCLM.contDiff.comp_contDiffOn hvJ) contDiffOn_const
    (fun z hz => by
      change (v (y,frameVector (e lam) y z)).im = 0
      rw [hdata z hz,Complex.ofReal_im]) hw
  rw [parametricBallVelocityAdjoint_zero V p hU hCU hm hw] at him
  have hFrame : movingBallToFrame (γ lam) (e lam) (y,frameVector (e lam) y w) = (y,w) :=
    movingBallToFrame_fromFrame he
  rw [adjointField_actualMovingTraceAdjoint,hFrame]
  change (r y : ℂ) * ⟨(r y)⁻¹ * parametricBallVelocityAdjoint a B
    (realMovingVelocityDatum (e lam) v) (y,w),(r y)⁻¹ * parametricBallVelocityAdjoint a B
    (imagMovingVelocityDatum (e lam) v) (y,w)⟩ = _
  rw [hre,him,mul_zero]
  change (r y : ℂ) * ⟨(r y)⁻¹ * parametricBallVelocityAdjoint m V φ (p,w),0⟩ =
    (parametricBallVelocityAdjoint m V φ (p,w) : ℂ)
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,← mul_assoc,hR]

end CalderonN
