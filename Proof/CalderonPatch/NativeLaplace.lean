module

public import Proof.CalderonPatch.ChartChange
public import Proof.CalderonPatch.InteriorChartBasis

import Proof.CalderonN.ChartGeometry
import Proof.CalderonN.GreenWeak
import Proof.CalderonN.MetricCalculus

@[expose] public section

noncomputable section
open Set
open scoped ContDiff Manifold

namespace CalderonPatch

open CalderonN (I X laplace chartVolume divergenceFlux coordDeriv laplace_congrOn
  contDiffOn_coordDeriv contDiffOn_divergenceFlux chartVolume_mul_laplace_eq_divergence)

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M]

local notation "J" => 𝓡∂ n
local notation "K" => 𝓘(ℝ, X n)
local notation "R" => 𝓘(ℝ, ℝ)

theorem exists_smooth_interiorChart (p : M) (hp : p ∈ (𝓡∂ n).interior M) :
    ∃ e : OpenPartialHomeomorph M (X n), p ∈ e.source ∧
      ContMDiffOn J K ∞ e e.source ∧ ContMDiffOn K J ∞ e.symm e.target := by
  obtain ⟨e, hpe, _, _, he, hes⟩ :=
    exists_interiorChart p hp isOpen_univ (mem_univ p)
  exact ⟨e, hpe, he, hes⟩

/-- The scalar Laplace–Beltrami operator at interior points. The weak
interior kernel law uses its extension by zero at boundary points. -/
def nativeLaplace (g : SmoothMetric n M) (u : M → ℝ) (p : M) : ℝ :=
  open scoped Classical in
  if h : p ∈ (𝓡∂ n).interior M then
    let e := (exists_smooth_interiorChart p h).choose
    laplace (coordinateMetric g e) (u ∘ e.symm) (e p)
  else 0

/-- The ambient operator realizes the actual coordinate Laplacian on
every smooth interior chart. Smoothness of the function is local. -/
theorem nativeLaplace_eq_coordinate (g : SmoothMetric n M)
    (e : OpenPartialHomeomorph M (X n)) (hI : e.source ⊆ (𝓡∂ n).interior M)
    (he : ContMDiffOn J K ∞ e e.source) (hes : ContMDiffOn K J ∞ e.symm e.target)
    {u : M → ℝ} (hu : ContMDiffOn J R ∞ u e.source)
    {p : M} (hp : p ∈ e.source) :
    nativeLaplace g u p = laplace (coordinateMetric g e) (u ∘ e.symm) (e p) := by
  unfold nativeLaplace
  rw [dite_eq_left (hI hp)]
  let t := exists_smooth_interiorChart p (hI hp)
  exact laplace_coordinateMetric_change g e t.choose he hes t.choose_spec.2.1 t.choose_spec.2.2
    e.open_source Subset.rfl hu hp t.choose_spec.1

/-- Compactly supported tests stay supported in the same region after
application of the native Laplace–Beltrami operator. -/
theorem tsupport_nativeLaplace_subset (g : SmoothMetric n M) (u : M → ℝ) :
    tsupport (nativeLaplace g u) ⊆ tsupport u := by
  classical
  apply closure_minimal _ isClosed_closure
  intro p hp
  by_contra hout
  apply hp
  unfold nativeLaplace
  split
  · rename_i hint
    let s := exists_smooth_interiorChart p hint
    let e := s.choose
    let V := e.target ∩ e.symm ⁻¹' (tsupport u)ᶜ
    have hV : IsOpen V := e.continuousOn_symm.isOpen_inter_preimage e.open_target isClosed_closure.isOpen_compl
    have hpx : e p ∈ V := by
      refine ⟨e.map_source s.choose_spec.1, ?_⟩
      change e.symm (e p) ∉ tsupport u
      rwa [e.left_inv s.choose_spec.1]
    have hzero : EqOn (u ∘ e.symm) 0 V := by
      intro x hx
      change u (e.symm x) = 0
      exact image_eq_zero_of_notMem_tsupport hx.2
    rw [laplace_congrOn hV (fun _ _ => rfl) hzero hpx]
    have hD (i : I n) : coordDeriv i (0 : X n → ℝ) = 0 := by
      funext x
      simp [coordDeriv, Pi.zero_def]
    simp [laplace, hD]
  · rfl

omit [NeZero n] in
/-- Smoothness of the scalar coordinate Laplacian on an open set. -/
theorem contDiffOn_coordinateLaplace {U : Set (X n)} (hU : IsOpen U)
    {γ : CalderonN.MetricField n} (hγ : CalderonN.SmoothMetric U γ)
    {u : X n → ℝ} (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (laplace γ u) U := by
  have hFlux : ContDiffOn ℝ ∞
      (fun x => ∑ i : I n, coordDeriv i (fun z => divergenceFlux γ u z i) x) U :=
    ContDiffOn.sum fun i _ => contDiffOn_coordDeriv (contDiffOn_divergenceFlux hU hγ hu i) hU i
  have hD := CalderonN.contDiffOn_metric_volume hγ
  have hpos (x : X n) (hx : x ∈ U) : chartVolume γ x ≠ 0 :=
    (Real.sqrt_pos.mpr (hγ.2 x hx).det_pos).ne'
  refine (hFlux.div hD hpos).congr ?_
  intro x hx
  change laplace γ u x = (∑ i : I n, coordDeriv i (fun z => divergenceFlux γ u z i) x) / chartVolume γ x
  rw [← chartVolume_mul_laplace_eq_divergence hU hγ hu hx, mul_comm, mul_div_cancel_right₀ _ (hpos x hx)]

end CalderonPatch
