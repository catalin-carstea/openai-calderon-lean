module

public import Proof.CalderonN.HarmonicL2Space
public import Proof.CalderonN.InteriorJetCutoff
public import Mathlib.Analysis.Calculus.Taylor

import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic

public section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace CalderonN

variable {dim : ℕ} [NeZero dim]

/-- A representative of a harmonic L² class, unique on its open domain. -/
def harmonicRepresentative {D : Set (X dim)} {hD : IsOpen D} {g : (MetricField dim)}
    {hg : SmoothMetric D g}
    (u : harmonicL2Space hD hg) : (X dim) → ℝ :=
  Classical.choose (harmonicL2Space_representative hD hg u)

theorem harmonicRepresentative_spec {D : Set (X dim)} {hD : IsOpen D} {g : (MetricField dim)}
    {hg : SmoothMetric D g}
    (u : harmonicL2Space hD hg) :
    Harmonic D g (harmonicRepresentative u) ∧
      (u.1 : (X dim) → ℝ) =ᵐ[(volume : Measure (X dim)).restrict D] harmonicRepresentative u :=
  Classical.choose_spec (harmonicL2Space_representative hD hg u)

section Evaluation

variable {D : Set (X dim)} (hD : IsOpen D) {g : (MetricField dim)} (hg : SmoothMetric D g)

private theorem harmonicRep_add (u v : harmonicL2Space hD hg) :
    EqOn (harmonicRepresentative (u+v))
      (fun x => harmonicRepresentative u x + harmonicRepresentative v x) D := by
  apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (X dim))) _ hD
    (harmonicRepresentative_spec (u+v)).1.1.continuousOn
    ((harmonicRepresentative_spec u).1.1.continuousOn.add
      (harmonicRepresentative_spec v).1.1.continuousOn)
  filter_upwards [(harmonicRepresentative_spec (u+v)).2,
    Lp.coeFn_add u.1 v.1, (harmonicRepresentative_spec u).2, (harmonicRepresentative_spec v).2]
    with x hx hsum hu hv
  calc
    harmonicRepresentative (u+v) x = (u.1 + v.1) x := hx.symm
    _ = _ := by
      rw [hsum, Pi.add_apply, hu, hv]
      rfl

private theorem harmonicRep_smul (a : ℝ) (u : harmonicL2Space hD hg) :
    EqOn (harmonicRepresentative (a • u))
      (a • harmonicRepresentative u) D := by
  apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure (X dim))) _ hD
    (harmonicRepresentative_spec (a • u)).1.1.continuousOn
    ((harmonicRepresentative_spec u).1.1.continuousOn.const_smul a)
  filter_upwards [(harmonicRepresentative_spec (a • u)).2,
    Lp.coeFn_smul a u.1, (harmonicRepresentative_spec u).2] with x hx hmul hu
  calc
    harmonicRepresentative (a • u) x = (a • u.1) x := hx.symm
    _ = _ := by
      rw [hmul, Pi.smul_apply, hu]
      rfl

theorem harmonicRep_contDiffAt (u : harmonicL2Space hD hg) (k : ℕ) {x : (X dim)} (hx : x ∈ D) :
    ContDiffAt ℝ k (harmonicRepresentative u) x :=
  ((harmonicRepresentative_spec u).1.1.contDiffAt (hD.mem_nhds hx)).of_le (by simp)

private theorem harmonicRep_iteratedFDeriv_add (k : ℕ) {x : (X dim)} (hx : x ∈ D)
    (u v : harmonicL2Space hD hg) :
    iteratedFDeriv ℝ k (harmonicRepresentative (u+v)) x =
      iteratedFDeriv ℝ k (harmonicRepresentative u) x +
      iteratedFDeriv ℝ k (harmonicRepresentative v) x := by
  have he : harmonicRepresentative (u+v) =ᶠ[𝓝 x]
      (fun y => harmonicRepresentative u y + harmonicRepresentative v y) :=
    Filter.eventually_of_mem (hD.mem_nhds hx) (harmonicRep_add hD hg u v)
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  exact iteratedFDeriv_add_apply (harmonicRep_contDiffAt hD hg u k hx)
    (harmonicRep_contDiffAt hD hg v k hx)

private theorem harmonicRep_iteratedFDeriv_smul (k : ℕ) {x : (X dim)} (hx : x ∈ D)
    (a : ℝ) (u : harmonicL2Space hD hg) :
    iteratedFDeriv ℝ k (harmonicRepresentative (a • u)) x =
      a • iteratedFDeriv ℝ k (harmonicRepresentative u) x := by
  have he : harmonicRepresentative (a • u) =ᶠ[𝓝 x] a • harmonicRepresentative u :=
    Filter.eventually_of_mem (hD.mem_nhds hx) (harmonicRep_smul hD hg a u)
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  exact iteratedFDeriv_const_smul_apply (harmonicRep_contDiffAt hD hg u k hx)

/-- Derivative evaluation is continuous linear on the actual harmonic space. -/
def harmonicJetCLM (hjet : HarmonicInteriorJets D g) (k : ℕ) (x : (X dim)) (hx : x ∈ D) :
    harmonicL2Space hD hg →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => (X dim)) ℝ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun u => iteratedFDeriv ℝ k (harmonicRepresentative u) x
      map_add' := fun u v => harmonicRep_iteratedFDeriv_add hD hg k hx u v
      map_smul' := fun a u => harmonicRep_iteratedFDeriv_smul hD hg k hx a u }
    (by
      obtain ⟨C, _, hC⟩ := hjet {x} isCompact_singleton (singleton_subset_iff.mpr hx) k
      exact ⟨C, fun u => hC u.1 _ (harmonicRepresentative_spec u).1
        (harmonicRepresentative_spec u).2 x (mem_singleton x)⟩)

theorem harmonicJetCLM_apply (hjet : HarmonicInteriorJets D g) (k : ℕ) (x : (X dim)) (hx : x ∈ D)
    (u : harmonicL2Space hD hg) :
    harmonicJetCLM hD hg hjet k x hx u =
      iteratedFDeriv ℝ k (harmonicRepresentative u) x := by
  unfold harmonicJetCLM
  rfl

end Evaluation

end CalderonN
