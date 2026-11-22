module

public import Proof.CalderonN.SmoothTraceFiniteExt
public import Proof.CalderonN.SmoothTraceFlatDegree

import Proof.CalderonN.SmoothTraceRotationGraph
import Proof.CalderonN.HarmonicRotationCasimir
import Proof.CalderonN.FiniteHarmonicPackets
import Proof.CalderonN.SmoothAngularCasimir
import Mathlib.Tactic

/-! Exact smooth-core degree identities from the finite solid harmonics
and the genuine flat radial adjunction. -/

public section

noncomputable section
open scoped DirectSum Classical InnerProductSpace ENNReal
set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet OAI.AnisotropicCalderon SphereHarmonic
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

abbrev smoothHarmonicSingle (k : ℕ) :=
  (finiteHarmonicSmoothTraceL (dim:=dim)).comp
    (DirectSum.lof ℝ ℕ (fun k => ↥(harmonicSphereSubspace dim k)) k)

theorem smoothSphereTraceL2_harmonicSingle (hn : 3 ≤ dim) (k : ℕ) (v : harmonicSphereSubspace dim k) :
    smoothSphereTraceL2 hn (smoothHarmonicSingle k v) = (v : SphereL2 dim) := by
  rw [smoothHarmonicSingle,LinearMap.comp_apply,finiteHarmonicSmoothTraceL_apply,
    smoothSphereTraceL2_apply,← finiteHarmonicSphereL_apply hn,finiteHarmonicSphereL_eq_sobolev]
  apply (sphereSobolevZeroEquiv (dim:=dim)).injective
  rw [LinearIsometryEquiv.apply_symm_apply,sphereSobolevZeroEquiv_harmonic,harmonicBoundaryFiniteL,
    DirectSum.toModule_lof]
  rfl

variable {hn : 3 ≤ dim} {B : Module.End ℝ (SmoothSphereTrace dim)}
  (hSym : SmoothTraceAdjoint hn B B)
  (hB : ∀ f, B (finiteHarmonicSmoothTraceL f) = finiteHarmonicSmoothTraceL (finiteHarmonicDegreeL f))

include hB in
theorem smoothTraceDegree_harmonicSingle (k : ℕ) (v : harmonicSphereSubspace dim k) :
    B (smoothHarmonicSingle k v) = (k:ℝ) • smoothHarmonicSingle k v := by
  simp only [smoothHarmonicSingle,LinearMap.comp_apply,hB,finiteHarmonicDegreeL_lof,map_smul]

theorem smoothTraceRotation_harmonicSingle (i j : Fin dim) (k : ℕ) (v : harmonicSphereSubspace dim k) :
    smoothSphereTraceRotation i j (smoothHarmonicSingle k v) =
      smoothHarmonicSingle k (harmonicSphereRotation k i j v) := by
  simp only [smoothHarmonicSingle,LinearMap.comp_apply,finiteHarmonicSmoothTraceL_rotation,
    finiteHarmonicRotationL_lof]

include hSym hB in
theorem smoothTraceDegree_projection (u : SmoothSphereTrace dim) (k : ℕ) :
    harmonicProjection k (smoothSphereTraceL2 hn (B u)) =
      (k:ℝ) • harmonicProjection k (smoothSphereTraceL2 hn u) := by
  apply ext_inner_right ℝ
  intro v
  rw [real_inner_smul_left _ v (k:ℝ), harmonicProjection_inner, harmonicProjection_inner,
    ← smoothSphereTraceL2_harmonicSingle hn k v,
    hSym u (smoothHarmonicSingle k v), smoothTraceDegree_harmonicSingle hB,
    map_smul,real_inner_smul_right]

include hSym hB in
theorem norm_smoothTraceDegree_le (s : ℝ) (hs : s+1 ≤ 2) (u : SmoothSphereTrace dim) :
    ‖smoothSphereTraceSobolev hn s (by linarith) (B u)‖ ≤ ‖smoothSphereTraceSobolev hn (s+1) hs u‖ := by
  let U := smoothSphereTraceSobolev hn (s+1) hs u
  let V := smoothSphereTraceSobolev hn s (by linarith) (B u)
  have hTerm (k : ℕ) : ‖V k‖ ≤ ‖U k‖ := by
    dsimp only [V,U]
    rw [smoothSphereTraceSobolev_succ_coordinate,smoothSphereTraceSobolev_coordinate,
      smoothSphereTraceSobolev_coordinate,smoothTraceDegree_projection hSym hB,
      ← smul_comm (k:ℝ)]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k),
      abs_of_nonneg (show (0:ℝ) ≤ 1+k by positivity)]
    rw [mul_left_comm (k:ℝ),mul_left_comm (1+(k:ℝ))]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith : (k:ℝ) ≤ 1+k) (norm_nonneg _)) (abs_nonneg _)
  change ‖V‖ ≤ ‖U‖
  apply lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2:ℝ≥0∞).toReal) (norm_nonneg U)
  intro t
  exact (Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (norm_nonneg _) (hTerm k) (by norm_num)).trans
    (lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) U t)

include hSym hB in
theorem smoothTraceDegree_casimir :
    B*B+((dim:ℝ)-2) • B =
      (-1/2:ℝ) • ∑ i : Fin dim, ∑ j : Fin dim, smoothSphereTraceRotation i j*smoothSphereTraceRotation i j := by
  let K := smoothSphereTraceRotation (dim:=dim)
  let A := B*B+((dim:ℝ)-2) • B
  let C := (-1/2:ℝ) • ∑ i : Fin dim,∑ j : Fin dim,K i j*K i j
  have hA : SmoothTraceAdjoint hn A A := (hSym.mul hSym).add (hSym.const_smul _)
  have hK (i j : Fin dim) : SmoothTraceAdjoint hn (K i j*K i j) (K i j*K i j) := by
    have hNeg : (-K i j)*(-K i j) = K i j*K i j := by
      ext u : 1
      simp only [Module.End.mul_apply,LinearMap.neg_apply,map_neg,neg_neg]
    have hPair : SmoothTraceAdjoint hn (K i j*K i j) ((-K i j)*(-K i j)) :=
      (smoothTraceRotation_skew hn i j).mul (smoothTraceRotation_skew hn i j)
    rwa [hNeg] at hPair
  have hC : SmoothTraceAdjoint hn C C :=
    (SmoothTraceAdjoint.sum _ _ _ fun i _ => SmoothTraceAdjoint.sum _ _ _ fun j _ => hK i j).const_smul _
  apply SmoothTraceAdjoint.eq_of_finite hA hC
  have hEq : A.comp (finiteHarmonicSmoothTraceL (dim:=dim)) = C.comp finiteHarmonicSmoothTraceL := by
    ext k v : 2
    change A (smoothHarmonicSingle k v) = C (smoothHarmonicSingle k v)
    simp only [A,C,K,LinearMap.add_apply,Module.End.mul_apply,LinearMap.smul_apply,
      LinearMap.sum_apply,smoothTraceDegree_harmonicSingle hB,smoothTraceRotation_harmonicSingle,
      map_smul,smul_smul,← map_sum]
    rw [sum_harmonicSphereRotation_twice,map_smul,smul_smul,← add_smul]
    congr 1
    ring
  exact fun f => congrArg (fun L : HarmonicFiniteCoefficients dim →ₗ[ℝ] SmoothSphereTrace dim => L f) hEq

end CalderonN
