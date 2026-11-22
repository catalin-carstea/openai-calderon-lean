module

public import Proof.CalderonPatch.FrontierLocalExtension

import Proof.CalderonN.Hessian
import Proof.CalderonN.MetricCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

public section

noncomputable section
open Filter Matrix Set
open scoped ContDiff Matrix.Norms.Elementwise Topology

namespace CalderonPatch

open CalderonN (Mat X hessian)

private theorem eventually_span_eq_kernel
    {S V ι : Type*} [TopologicalSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι]
    {x₀ : S} {v : S → ι → V} {L : S → V →ₗ[ℝ] ℝ}
    (hCont : ContinuousAt v x₀) (hIndep : LinearIndependent ℝ (v x₀))
    (hSpan : Submodule.span ℝ (range (v x₀)) = (L x₀).ker)
    (hSurj : ∀ᶠ x in 𝓝 x₀, Function.Surjective (L x))
    (hZero : ∀ᶠ x in 𝓝 x₀, ∀ a, L x (v x a) = 0) :
    ∀ᶠ x in 𝓝 x₀, Submodule.span ℝ (range (v x)) = (L x).ker := by
  have hdim (x : S) (hx : Function.Surjective (L x)) :
      Module.finrank ℝ (L x).ker + 1 = Module.finrank ℝ V := by
    have h := (L x).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hx, finrank_top, Module.finrank_self] at h
    omega
  have hm : Fintype.card ι + 1 = Module.finrank ℝ V := by
    have h := finrank_span_eq_card hIndep
    rw [hSpan] at h
    exact h ▸ hdim x₀ hSurj.self_of_nhds
  filter_upwards [hCont.tendsto.eventually hIndep.eventually, hSurj, hZero] with x hLI hx hL
  apply Submodule.eq_of_le_of_finrank_le
  · exact Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hL a)
  · rw [finrank_span_eq_card hLI]
    have h := hdim x hx
    omega

variable {n : ℕ}

private def symmetricMatrices (n : ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | A.transpose = A}
  zero_mem' := Matrix.transpose_zero
  add_mem' := by
    intro A B ha hb
    change A.transpose = A at ha
    change B.transpose = B at hb
    change (A + B).transpose = A + B
    rw [Matrix.transpose_add, ha, hb]
  smul_mem' := by
    intro c A ha
    change A.transpose = A at ha
    change (c • A).transpose = c • A
    rw [Matrix.transpose_smul, ha]

private def symmetricPart (A : Mat n) : symmetricMatrices n :=
  ⟨(1 / 2 : ℝ) • (A + A.transpose), by
    change ((1 / 2 : ℝ) • (A + A.transpose)).transpose = _
    rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]⟩

private theorem symmetricPart_of_symm {A : Mat n} (hA : A.transpose = A) :
    (symmetricPart A : Mat n) = A := by
  change (1 / 2 : ℝ) • (A + A.transpose) = A
  rw [hA, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem continuous_symmetricPart : Continuous (symmetricPart (n := n)) := by
  apply Continuous.subtype_mk
  change Continuous (fun A : Mat n => (1 / 2 : ℝ) • (A + A.transpose))
  have htr : Continuous (fun A : Mat n => A.transpose) :=
    continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)
  exact (continuous_id.add htr).const_smul (1 / 2 : ℝ)

private def traceAgainst (A : Mat n) : symmetricMatrices n →ₗ[ℝ] ℝ where
  toFun H := (A * (H : Mat n)).trace
  map_add' := by intro H K; simp [Matrix.mul_add]
  map_smul' := by intro c H; simp

private theorem traceAgainst_inv_surjective (hn : n ≠ 0) {A : Mat n} (hA : A.PosDef) :
    Function.Surjective (traceAgainst A⁻¹) := by
  intro t
  have hs : A ∈ symmetricMatrices n := hA.isHermitian.isSymm.eq
  let H : symmetricMatrices n := (t / n : ℝ) • ⟨A, hs⟩
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine ⟨H, ?_⟩
  change (A⁻¹ * ((t / n : ℝ) • A)).trace = t
  rw [Matrix.mul_smul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    Matrix.trace_smul, smul_eq_mul, Matrix.trace_one, Fintype.card_fin, div_mul_cancel₀ _ hnR]

private theorem traceAgainst_map_ker (A : Mat n) (H : Mat n) :
    H ∈ (traceAgainst A).ker.map (symmetricMatrices n).subtype ↔
      H.transpose = H ∧ (A * H).trace = 0 := by
  constructor
  · rintro ⟨⟨K, hK⟩, htrace, rfl⟩
    exact ⟨hK, htrace⟩
  · rintro ⟨hH, htrace⟩
    exact ⟨⟨H, hH⟩, htrace, rfl⟩

/-- A finite harmonic Hessian basis stays spanning near its reference point.
The hyperplane changes with the metric, but its codimension in the
symmetric matrices remains one. -/
theorem hessianSpanningAt_eventually (hn : n ≠ 0) {m : ℕ} {g : CalderonN.MetricField n}
    {u : Fin m → X n → ℝ} {q : X n}
    (hCont : ContinuousAt (fun x a => hessian (u a) x) q)
    (hIndep : LinearIndependent ℝ (fun a => hessian (u a) q))
    (hSpan : HessianSpanningAt g u q)
    (hPos : ∀ᶠ x in 𝓝 q, (g x).PosDef)
    (hHess : ∀ᶠ x in 𝓝 q, ∀ a,
      (hessian (u a) x).transpose = hessian (u a) x ∧ ((g x)⁻¹ * hessian (u a) x).trace = 0) :
    ∀ᶠ x in 𝓝 q, HessianSpanningAt g u x := by
  let v (x : X n) (a : Fin m) := symmetricPart (hessian (u a) x)
  let L (x : X n) := traceAgainst (g x)⁻¹
  have hVCont : ContinuousAt v q := continuousAt_pi.2 fun a =>
    continuous_symmetricPart.continuousAt.comp ((continuous_apply a).continuousAt.comp hCont)
  have hVMap (x : X n) (hx : ∀ a, (hessian (u a) x).transpose = hessian (u a) x) :
      ⇑(symmetricMatrices n).subtype ∘ v x = fun a => hessian (u a) x :=
    funext fun a => symmetricPart_of_symm (hx a)
  have hMapSpan (x : X n) (hx : ∀ a, (hessian (u a) x).transpose = hessian (u a) x) :
      (Submodule.span ℝ (range (v x))).map (symmetricMatrices n).subtype =
        Submodule.span ℝ (range fun a => hessian (u a) x) := by
    rw [Submodule.map_span, ← range_comp, hVMap x hx]
  have qsym (a : Fin m) := (hHess.self_of_nhds a).1
  have hLI : LinearIndependent ℝ (v q) := by
    apply LinearIndependent.of_comp (f := (symmetricMatrices n).subtype)
    rwa [hVMap q qsym]
  have hK : Submodule.span ℝ (range (v q)) = (L q).ker := by
    apply Submodule.map_injective_of_injective (symmetricMatrices n).injective_subtype
    rw [hMapSpan q qsym]
    ext H
    exact (hSpan H).trans (traceAgainst_map_ker (g q)⁻¹ H).symm
  have hLSurj : ∀ᶠ x in 𝓝 q, Function.Surjective (L x) :=
    hPos.mono fun _ hx => traceAgainst_inv_surjective hn hx
  have hZero : ∀ᶠ x in 𝓝 q, ∀ a, L x (v x a) = 0 :=
    hHess.mono fun x hx a => by
      change ((g x)⁻¹ * (v x a : Mat n)).trace = 0
      rw [symmetricPart_of_symm (hx a).1]
      exact (hx a).2
  filter_upwards [eventually_span_eq_kernel hVCont hLI hK hLSurj hZero, hHess] with x hx hsym H
  rw [← hMapSpan x (fun a => (hsym a).1), hx]
  exact traceAgainst_map_ker (g x)⁻¹ H

/-- A Hessian basis assembled from harmonic functions in a harmonic chart
persists on one open neighborhood for that same finite list of functions. -/
theorem exists_harmonic_hessianSpanning_neighborhood [NeZero n]
    {Ω : Set (X n)} (hΩ : IsOpen Ω) {q : X n} (hq : q ∈ Ω)
    {g : CalderonN.MetricField n} (hg : CalderonN.SmoothMetric Ω g)
    (hchart : CalderonN.HarmonicCoordinates Ω g)
    {m : ℕ} {u : Fin m → X n → ℝ} (hu : ∀ a, CalderonN.Harmonic Ω g (u a))
    (hIndep : LinearIndependent ℝ (fun a => hessian (u a) q))
    (hSpan : HessianSpanningAt g u q) :
    ∃ V : Set (X n), IsOpen V ∧ q ∈ V ∧ V ⊆ Ω ∧ ∀ x ∈ V, HessianSpanningAt g u x := by
  have hCont : ContinuousAt (fun x a => hessian (u a) x) q := by
    apply continuousAt_pi.2
    intro a
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    exact (CalderonN.contDiffOn_coordDeriv
      (CalderonN.contDiffOn_coordDeriv (hu a).1 hΩ j) hΩ i).continuousOn.continuousAt
        (hΩ.mem_nhds hq)
  have hNear : Ω ∈ 𝓝 q := hΩ.mem_nhds hq
  have hEvent := hessianSpanningAt_eventually (NeZero.ne n) hCont hIndep hSpan
    (Filter.mem_of_superset hNear fun _ hx => hg.2 _ hx)
    (Filter.mem_of_superset hNear fun _ hx a =>
      ⟨CalderonN.hessian_transpose hΩ (hu a).1 hx, CalderonN.trace_hessian_eq_zero hΩ hchart (hu a) hx⟩)
  obtain ⟨V, hSub, hV, hqV⟩ := mem_nhds_iff.mp (inter_mem hNear hEvent)
  exact ⟨V, hV, hqV, fun _ hx => (hSub hx).1, fun _ hx => (hSub hx).2⟩

end CalderonPatch
