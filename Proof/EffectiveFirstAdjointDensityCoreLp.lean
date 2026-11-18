import Proof.EffectiveFirstAdjointDensityCore
import Proof.EffectiveFirstAdjointFiveHalfLp
import Proof.EffectiveFirstAdjointCoreSupport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OperatorForms

/-- The constructed density core has an actual base Lp domain. The proof
uses measurability and a continuous compact-support majorant, and never
differentiates the pointwise selected higher representative. -/
lemma PhysicalPrincipalData.firstAdjointDensityCoreRow_memLp
    {Y Ω : Set X} {m : ℕ} {K ρ c₀ floor ε CF CT CB CS CG CK : ℝ}
    {M : Fin (m+1) → ℝ} {Cj : Fin 9 → ℝ} {d : Data}
    (P : PhysicalPrincipalData Y d CF CT) (hY : IsOpen Y) (hΩ : IsOpen Ω) (hSub : Y ⊆ Ω)
    (hd : Admissible Y Ω K ρ c₀ M Cj floor ε d) (hK : 0 < K)
    (WF : PhysicalFirstCommutatorPacket P CB CS ε)
    (WQ : ∀ y ∈ Y,PhysicalPotentialQuarticData P y CG CK) (hCG : 0 ≤ CG) (hCK : 0 ≤ CK)
    (U : X → SphereSobolev (5/2:ℝ)) (hU : ContDiff ℝ ∞ U)
    (S : Set X) (hS : IsCompact S) (hSY : S ⊆ Y) (h0U : ∀ x ∉ S,U x=0) (b : I)
    (hw : ContDiffOn ℝ ∞ (scalarPrincipalConnectionWeight d b) Y) (p : ℝ≥0∞) :
    MemLp (P.firstAdjointDensityCoreRow WF WQ U b) p (volume.restrict Y) := by
  let Z := WF.covariantAdjointLowSection U b
  let Top := P.firstCovariantAdjointFiveHalfSection WQ U b
  let μ := metricDensity d.γ
  let DZ := fun y => fderiv ℝ Z y (axis b)
  let Dμ := fun y => fderiv ℝ μ y (axis b)
  let R := fun y => frameAngularConnectionHigherL d y (axis b)
  let N := fun y => firstAdjointFiveHalfCoordinateBudget d CG CK b y*‖U y‖
  have hg : Elliptic Y K d.γ :=
    ⟨fun i j => (hd.1.1.1 i j).mono hSub,fun x hx => hd.1.1.2 x (hSub hx)⟩
  have he (i : I) : ContDiffOn ℝ ∞ (fun x => d.frame x i) Y := (hd.1.2.2.2.2.2.2.1 i).mono hSub
  have hSupported := WF.covariantAdjointLowSection_supported hY hd U hU S hS.isClosed hSY h0U b hw
  have hZ : ContDiff ℝ ∞ Z := hSupported.1
  have hDZ : ContDiff ℝ ∞ DZ :=
    (hZ.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have hμ : ContDiffOn ℝ ∞ μ Y := hg.contDiffOn_density hK
  have hDμ : ContDiffOn ℝ ∞ Dμ Y := (hμ.fderiv_of_isOpen hY (by simp)).clm_apply contDiffOn_const
  have hR : ContDiffOn ℝ ∞ R Y := contDiffOn_frameAngularConnectionHigherL hY d hg hK he (axis b)
  have hN : ContinuousOn N Y :=
    (continuousOn_firstAdjointFiveHalfCoordinateBudget hY hΩ hSub hd hK b hw).mul hU.continuous.continuousOn.norm
  have hTopN (y) (hy : y ∈ Y) : ‖Top y‖ ≤ N y := by
    dsimp only [Top,PhysicalPrincipalData.firstCovariantAdjointFiveHalfSection]
    rw [dif_pos hy]
    exact ((P.firstCovariantCoordinateAdjointFiveHalfL (WQ y hy) b).le_opNorm (U y)).trans
      (mul_le_mul_of_nonneg_right (P.norm_firstCovariantCoordinateAdjointFiveHalfL_le_budget (WQ y hy)
        hCG hCK (hd.2.2.2.2.1.2 y hy).1.le b) (norm_nonneg _))
  apply memLp_of_compact_supported_continuousOn_majorant hY.measurableSet hS hSY
    (P.firstAdjointDensityCoreRow WF WQ U b)
    (P.firstAdjointDensityCoreRow_aestronglyMeasurable hY hSub hd hK WF WQ U hU.contDiffOn b hw)
    (fun _ _ hs => P.firstAdjointDensityCoreRow_zero_off hY hd WF WQ U hU S hS.isClosed hSY h0U b hw hs)
    (fun y => |μ y| * ‖DZ y‖+|μ y| * ‖R y‖*N y+|Dμ y| * ‖Z y‖)
    (((hμ.continuousOn.abs.mul hDZ.continuous.continuousOn.norm).add
      ((hμ.continuousOn.abs.mul hR.continuousOn.norm).mul hN)).add
      (hDμ.continuousOn.abs.mul hZ.continuous.continuousOn.norm))
  intro y hy
  have hRN : ‖R y (Top y)‖ ≤ ‖R y‖*N y :=
    ((R y).le_opNorm (Top y)).trans (mul_le_mul_of_nonneg_left (hTopN y hy) (norm_nonneg _))
  change ‖μ y • DZ y-μ y • R y (Top y)+Dμ y • Z y‖ ≤ _
  calc
    _ ≤ (‖μ y • DZ y‖+‖μ y • R y (Top y)‖)+‖Dμ y • Z y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ = |μ y| * ‖DZ y‖+|μ y| * ‖R y (Top y)‖+|Dμ y| * ‖Z y‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ _ := by
      simpa only [mul_assoc] using add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hRN (abs_nonneg _))) le_rfl

end ShrinkingSpheres
