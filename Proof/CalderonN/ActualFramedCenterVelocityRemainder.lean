module

public import Proof.CalderonN.ActualParallelCenterRadialRemainder
public import Proof.CalderonN.ActualFramedCoefficientRemainder
public import Proof.CalderonN.ActualMovingVelocityTaylor

import Mathlib.Tactic

/-! The quadratic center velocity in the moving orthonormal sphere
coordinates, using the same signed radius collar as the coefficient. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxSynthPendingDepth 24
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

@[expose] def actualFramedCenterVelocityRemainder (d : Data dim)
    (p : FramedRadialParameter dim) : X dim →L[ℝ] X dim :=
  actualParallelCenterRadialRemainder d (actualFramedRadialInput d p)

theorem uniform_actual_framedCenterVelocity_radialRemainder
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) (hYc : IsCompact (closure Y))
    {m : ℕ} (N : ℕ) (hm : N+4 ≤ m) (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ floor ≥ 1, ∀ ε, 0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d →
      (∀ y i, d.frame y i = smoothMetricFrame (d.γ y) i) →
      ∀ y ∈ Y, ∀ s : ℝ, |s| ≤ 2*d.radius y → ∀ z ∈ closedBall (0:X dim) L,
        LocalSmoothJetBudget (actualFramedCenterVelocityRemainder d) ((y,s),z) N C ∧
        ∀ a : X dim,∀ b : ℝ, scaledNormalTraceVelocity d.γ d.expMap d.frame y s b z a =
          frameCoordinatesL d.γ y (d.frame y) a+b • z+
            s^2 • frameCoordinatesL d.γ y (d.frame y) (actualFramedCenterVelocityRemainder d ((y,s),z) a) := by
  obtain ⟨η,hη,hGeom⟩ := uniform_actual_normal_radial_segment_enlarged (Y:=Y) hΩ
    (by omega : 2 ≤ m) K ρ c₀ M Cj hK hρ L hL
  obtain ⟨ηR,CR,hηR,hCR,hR⟩ := uniform_actual_parallelCenter_radialRemainder hY hΩ hYc N hm
    K ρ c₀ M Cj hK hρ L hL
  obtain ⟨CI,hCI,hInput⟩ := uniform_actual_framedRadialInput_jets hΩ hYc N
    (by omega) K ρ c₀ M Cj hK L
  let C := (N.factorial:ℝ)*CR*CI^N
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCR)
    (pow_nonneg (zero_le_one.trans hCI) _)
  refine ⟨min η ηR,C,lt_min hη hηR,hC,?_⟩
  intro floor hf ε he hs d hd hdFrame y hy s hsR z hz
  let w := frameVector d.frame y z
  have hFrame := hd.1.2.2.2.2.2.2.2 y (hd.2.1.center_mem hy)
  have hw : w ∈ disk d.γ y L := frameVector_mem_disk d.γ d.frame y z L hFrame hz
  obtain ⟨hs₁,_,hRay⟩ := hGeom floor hf ε he (hs.trans (min_le_left _ _)) d hd y hy s hsR w hw
  obtain ⟨hRj,hEq⟩ := hR floor hf ε he (hs.trans (min_le_right _ _)) d hd y hy s hsR w hw
  have hIn := hInput floor ε d hd hdFrame y hy s hs₁ z hz
  refine ⟨hIn.comp hRj hCI,?_⟩
  intro a b
  have hMem : s • w ∈ disk d.γ y (max ρ (d.radius y)) := by
    simpa only [one_mul] using (hRay 1 (by simp)).1
  rw [scaledNormalTraceVelocity_eq_center_add_radius hd.2.1 d.frame hy hFrame s b z a hMem,hEq]
  simp only [add_apply,smul_apply,ContinuousLinearMap.id_apply,map_add,map_smul]
  simp only [actualFramedCenterVelocityRemainder,actualFramedRadialInput,w]
  abel

end CalderonN
