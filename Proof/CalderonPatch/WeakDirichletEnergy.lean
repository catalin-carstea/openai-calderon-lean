module

public import Proof.CalderonPatch.DirichletWeakGreen

import Proof.CalderonPatch.MeasuredPolarization
import Mathlib.Tactic

public section

noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace CalderonPatch.DirichletData

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (m + 1)) M] [IsManifold (𝓡∂ (m + 1)) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

local notation "J" => 𝓡∂ (m + 1)
local notation "R" => 𝓘(ℝ, ℝ)

variable (D : DirichletData m M)

local notation "Q[" f "]" =>
  (∫ x, covectorEnergy D.metric x (mfderiv J R f x) ∂D.volume)

/-- The energy of every smooth competitor differs from the minimum
of the completed Dirichlet form by a squared energy norm. -/
theorem energy_add_zeroTrace_eq (f : M → ℝ) (hf : ContMDiff J R ∞ f)
    (v : DirichletTest D) :
    Q[f + (v : M → ℝ)] = Q[f] - ‖D.weakHarmonicCorrection f hf‖ ^ 2 +
      ‖(v : DirichletHilbert D) - D.weakHarmonicCorrection f hf‖ ^ 2 := by
  let w := D.weakHarmonicCorrection f hf
  have hI (a b : M → ℝ) (ha : ContMDiff J R ∞ a) (hb : ContMDiff J R ∞ b) :=
    integrable_energyPairingDensity D.metric D.volume D.metric_volume ha hb
  have hE := integral_energy_add D.metric D.volume hf v.smooth hI
  have hV : Q[(v : M → ℝ)] = ‖(v : DirichletHilbert D)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,inner_dirichletHilbert_coe]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => (energyPairingDensity_self D.metric v x).symm)
  have hX := D.weakHarmonicCorrection_on_test f hf v
  rw [hE,hV,norm_sub_sq_real,real_inner_comm w (v : DirichletHilbert D)]
  linarith

/-- The measured infimum of smooth Dirichlet energies equals the
energy at the completed minimizer. This uses only the weak inverse. -/
theorem dirichletQuadraticEnergy_eq_weak (f : M → ℝ) (hf : ContMDiff J R ∞ f) :
    dirichletQuadraticEnergy D.metric D.volume f =
      Q[f] - ‖D.weakHarmonicCorrection f hf‖ ^ 2 := by
  let w := D.weakHarmonicCorrection f hf
  let B := Q[f] - ‖w‖ ^ 2
  let S : Set ℝ := {c | ∃ u : M → ℝ, ContMDiff J R ∞ u ∧
    EqOn u f ((J).boundary M) ∧ c = Q[u]}
  have hS : S.Nonempty := ⟨Q[f],f,hf,fun _ _ => rfl,rfl⟩
  have hLower : ∀ c ∈ S, B ≤ c := by
    rintro c ⟨u,hu,hTrace,rfl⟩
    let v : DirichletTest D := DirichletTest.ofSmooth (u - f) (hu.sub hf) (fun x hx => by
      change u x - f x = 0
      rw [hTrace hx,sub_self])
    have huv : f + (v : M → ℝ) = u := by
      funext x
      change f x + (u x - f x) = u x
      ring
    rw [← huv,D.energy_add_zeroTrace_eq f hf v]
    exact le_add_of_nonneg_right (sq_nonneg _)
  change sInf S = B
  refine le_antisymm ?_ (le_csInf hS hLower)
  have hB : BddBelow S := ⟨B,hLower⟩
  have hBound (v : DirichletTest D) :
      sInf S ≤ B + ‖(v : DirichletHilbert D) - w‖ ^ 2 := by
    rw [← D.energy_add_zeroTrace_eq f hf v]
    apply csInf_le hB
    refine ⟨f + (v : M → ℝ),hf.add v.smooth,?_,rfl⟩
    intro x hx
    change f x + (v x) = f x
    rw [v.zero_trace hx]
    exact add_zero _
  have hc : IsClosed {z : DirichletHilbert D | sInf S ≤ B + ‖z - w‖ ^ 2} :=
    isClosed_le continuous_const ((continuous_id.sub continuous_const).norm.pow 2 |>.const_add B)
  have hW : sInf S ≤ B + ‖w - w‖ ^ 2 :=
    UniformSpace.Completion.induction_on (p := fun z => sInf S ≤ B + ‖z - w‖ ^ 2) w hc hBound
  simpa only [sub_self,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero] using hW

/-- A trial extension with small positive Laplacian in the metric L²
norm already approximates the measured boundary energy. -/
theorem abs_dirichletQuadraticEnergy_sub_trial_le (f : M → ℝ) (hf : ContMDiff J R ∞ f) :
    |dirichletQuadraticEnergy D.metric D.volume f - Q[f]| ≤
      ‖D.l2Value‖ ^ 2 * ‖D.positiveLaplaceLp f hf‖ ^ 2 := by
  rw [D.dirichletQuadraticEnergy_eq_weak f hf,sub_sub_cancel_left,abs_neg,
    abs_of_nonneg (sq_nonneg _)]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (D.norm_weakHarmonicCorrection_le f hf) 2

end CalderonPatch.DirichletData
