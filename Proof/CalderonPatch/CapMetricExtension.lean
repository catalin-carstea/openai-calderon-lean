module

public import Proof.CalderonN.ClosedHalfSpaceExtension
public import Proof.CalderonN.Coordinates
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Ring
import Proof.CalderonN.MetricPair

@[expose] public section

noncomputable section
open Matrix Metric Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X Mat lowerHalfSpace metricPair metricPair_eq_dotProduct
  metricPair_smul_same metricPair_pos_of_posDef)

variable {n : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Extend matrix coefficients across a one-sided collar using the
checked half-space extension. Symmetrization preserves the original
values and ensures that the extension remains symmetric. -/
theorem exists_symmetric_extension_lowerHalfSpace
    {g : Z × ℝ → Mat n}
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) (lowerHalfSpace Z))
    (hSym : ∀ p ∈ lowerHalfSpace Z, (g p).transpose = g p)
    (hSupport : ∀ (i j : I n) (k : ℕ), HasCompactSupport (fun z : Z =>
      iteratedFDerivWithin ℝ k (fun p => g p i j) (lowerHalfSpace Z) (z, 0) (fun _ => (0, 1)))) :
    ∃ G : Z × ℝ → Mat n,
      (∀ i j, ContDiff ℝ ∞ (fun p => G p i j)) ∧
      (∀ p, (G p).transpose = G p) ∧ EqOn G g (lowerHalfSpace Z) := by
  choose F hF hEq using fun i j =>
    CalderonN.exists_contDiff_extension_lowerHalfSpace (hg i j) (hSupport i j)
  let G (p : Z × ℝ) (i j : I n) := (F i j p + F j i p) / 2
  refine ⟨G, fun i j => ((hF i j).add (hF j i)).div_const _, ?_, ?_⟩
  · intro p
    ext i j
    change (F j i p + F i j p) / 2 = (F i j p + F j i p) / 2
    exact congrArg (· / 2) (add_comm _ _)
  · intro p hp
    ext i j
    have h := congrArg (fun A : Mat n => A i j) (hSym p hp)
    change g p j i = g p i j at h
    change (F i j p + F j i p) / 2 = g p i j
    rw [hEq i j hp, hEq j i hp]
    change (g p i j + g p j i) / 2 = g p i j
    rw [h]
    ring

set_option maxHeartbeats 650000 in
/-- A symmetric continuous extension with a positive metric on a compact
boundary slice remains positive in a uniform narrow collar. -/
theorem posDef_near_compact_slice {g : Z × ℝ → Mat n} {A : Set Z}
    (hA : IsCompact A) (hSym : ∀ p, (g p).transpose = g p)
    (hCont : ∀ i j, Continuous (fun p => g p i j))
    (hPos : ∀ z ∈ A, Matrix.PosDef (g (z, 0))) :
    ∃ δ > 0, ∀ z ∈ A, ∀ t ∈ ball (0 : ℝ) δ, Matrix.PosDef (g (z, t)) := by
  let Q (p : Z × ℝ) (v : X n) := metricPair (fun _ => g p) 0 v v
  have hQ : Continuous (fun p : (Z × ℝ) × X n => Q p.1 p.2) := by
    unfold Q metricPair
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((hCont i j).comp continuous_fst).mul ((EuclideanSpace.proj i).continuous.comp continuous_snd)).mul
        ((EuclideanSpace.proj j).continuous.comp continuous_snd)
  let K := A ×ˢ ({0} : Set ℝ)
  let S := sphere (0 : X n) 1
  let U : Set ((Z × ℝ) × X n) := {p | 0 < Q p.1 p.2}
  have hKS : K ×ˢ S ⊆ U := by
    rintro ⟨⟨z,t⟩, v⟩ ⟨⟨hz, ht⟩, hv⟩
    have hvne : v ≠ 0 := by
      intro h
      have hv' := mem_sphere_zero_iff_norm.mp hv
      simp [h] at hv'
    simp only [mem_singleton_iff] at ht
    subst t
    exact metricPair_pos_of_posDef (hPos z hz) hvne
  obtain ⟨V, D, hV, _, hKV, hSD, hVD⟩ :=
    generalized_tube_lemma (hA.prod isCompact_singleton) (isCompact_sphere (0 : X n) 1)
      (isOpen_lt continuous_const hQ) hKS
  obtain ⟨A', T, _, hT, hAA', h0T, hAT⟩ :=
    generalized_tube_lemma hA isCompact_singleton hV hKV
  obtain ⟨δ, hδ, hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds (h0T (mem_singleton _)))
  refine ⟨δ, hδ, fun z hz t ht => ?_⟩
  have hp : (z,t) ∈ V := hAT ⟨hAA' hz, hδT ht⟩
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · change (g (z,t))ᴴ = g (z,t)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hSym (z,t)
  · intro v hv
    let w : X n := WithLp.toLp 2 v
    have hw : w ≠ 0 := fun he => hv (congrArg WithLp.ofLp he)
    let u := ‖w‖⁻¹ • w
    have hu : u ∈ S := mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm hw)
    have hqU : ((z,t), u) ∈ U := hVD (show ((z,t), u) ∈ V ×ˢ D from ⟨hp, hSD hu⟩)
    have huQ : 0 < Q (z,t) u := hqU
    have hwu : ‖w‖ • u = w := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
    have hwQ : 0 < Q (z,t) w := calc
      0 < ‖w‖ ^ 2 * Q (z,t) u := mul_pos (pow_pos (norm_pos_iff.mpr hw) 2) huQ
      _ = Q (z,t) (‖w‖ • u) := (metricPair_smul_same _ _ _ _).symm
      _ = _ := congrArg (Q (z,t)) hwu
    simpa only [star_trivial, Q, metricPair_eq_dotProduct] using hwQ

end CalderonPatch
