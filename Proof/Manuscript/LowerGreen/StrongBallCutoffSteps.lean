module

public import Proof.Manuscript.LowerGreen.GreenCutoffOperators
public import Proof.Manuscript.LowerGreen.StrongBallSmoothInverse

import Mathlib.Tactic

public section

noncomputable section

open Set Filter Metric CalderonN CalderonN.BallDirichlet TauCeti
open scoped Topology ContDiff ENNReal Matrix.Norms.Elementwise

namespace CalderonPaper.LowerGreen

variable {n : ℕ} [NeZero n] [Nontrivial (Fin n)]
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- The forward localization step gains one native Sobolev order. -/
@[expose] def strongForwardCutoffL (s : ℕ) (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1) (p : P) :
    BallSobolev n (s+1) →L[ℝ] BallSobolev n (s+2) :=
  (fullStrongBallInverseL s (commonSupportMatrixFamily (s+2) a ha K hK hSupp p)).comp
    (greenCutoffOperatorFamily s a ha χ hχ p)

/-- The cutoff commutator depends only on the input germ on its support. -/
theorem greenSourceCutoffError_congr_germ_input
    (a : X n → Mat n) (χ u v : X n → ℝ)
    (h : ∀ x ∈ tsupport χ, u =ᶠ[𝓝 x] v) :
    greenSourceCutoffError a χ u = greenSourceCutoffError a χ v := by
  funext x
  by_cases hx : x ∈ tsupport χ
  · have hd (i : I n) : coordDeriv i u x = coordDeriv i v x :=
      congrArg (fun L : X n →L[ℝ] ℝ => L (axis i)) ((h x hx).fderiv_eq (𝕜 := ℝ))
    simp only [greenSourceCutoffError, (h x hx).eq_of_nhds, hd]
  · have hz : χ =ᶠ[𝓝 x] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hx
    rw [greenSourceCutoffError_eq_zero hz, greenSourceCutoffError_eq_zero hz]

set_option maxHeartbeats 1800000 in
/-- Applying the forward step to a smooth harmonic input, or to a
field equal to that input on the cutoff germs, returns its cutoff. -/
theorem strongForwardCutoffL_apply_localized (s : ℕ)
    (a : P × X n → Mat n) (ha : ContDiff ℝ ∞ a)
    (K : Set (X n)) (hK : IsCompact K) (hSupp : ∀ p z, z ∉ K → a (p,z) = 0)
    (χ : SmoothData n) (hχ : HasCompactSupport χ.1)
    (hSupport : tsupport χ.1 ⊆ ball (0 : X n) (1/2))
    (p : P) {lo hi : ℝ}
    (hEll : PDE.UniformlyEllipticOn (fixedBallOpens n : Set (X n)) (fun z => a (p,z)) lo hi)
    (hSym : ∀ z ∈ ball (0 : X n) 1, ∀ i j, a (p,z) i j = a (p,z) j i)
    (u v : SmoothData n) (hu : EqOn (negativeBallDivergence (fun z => a (p,z)) u.1) 0 (ball (0 : X n) 1))
    (hv : ∀ x ∈ tsupport χ.1, v.1 =ᶠ[𝓝 x] u.1) :
    strongForwardCutoffL s a ha K hK hSupp χ hχ p (smoothBallSobolev (s+1) v) =
      smoothBallSobolev (s+2) ⟨fun x => χ.1 x * u.1 x,χ.2.mul u.2⟩ := by
  let f : SmoothData n :=
    ⟨greenSourceCutoffError (fun z => a (p,z)) χ.1 v.1,
      contDiff_greenSourceCutoffError (ha.comp (contDiff_const.prodMk contDiff_id)) χ.2 v.2⟩
  let w : SmoothData n := ⟨fun x => χ.1 x * u.1 x,χ.2.mul u.2⟩
  have hTrace : EqOn w.1 0 (standardSphere n) := by
    intro z hz
    have hn : ¬ z ∈ tsupport χ.1 := by
      intro ht
      have hb := mem_ball_zero_iff.mp (hSupport ht)
      rw [mem_sphere_zero_iff_norm.mp hz] at hb
      norm_num at hb
    change χ.1 z * u.1 z = 0
    have hz₀ : χ.1 z = 0 := (notMem_tsupport_iff_eventuallyEq.mp hn).eq_of_nhds
    rw [hz₀,zero_mul]
  have hEq : EqOn (negativeBallDivergence (fun z => a (p,z)) w.1) f.1 (ball (0 : X n) 1) := by
    intro z hz
    change negativeBallDivergence (fun x => a (p,x)) (fun x => χ.1 x * u.1 x) z =
      greenSourceCutoffError (fun x => a (p,x)) χ.1 v.1 z
    have haP : ContDiff ℝ ∞ (fun x => a (p,x)) := ha.comp (contDiff_const.prodMk contDiff_id)
    have hu₀ : negativeBallDivergence (fun x => a (p,x)) u.1 z = 0 := hu hz
    rw [negativeBallDivergence_mul_eq_at_symm haP χ.2 u.2 z (hSym z hz),hu₀,mul_zero,zero_add,
      greenSourceCutoffError_congr_germ_input _ _ _ _ hv]
  unfold strongForwardCutoffL
  rw [ContinuousLinearMap.comp_apply,greenCutoffOperatorFamily_smooth]
  exact fullStrongBallInverseL_of_classical a ha K hK hSupp p hEll f w hTrace hEq s

end CalderonPaper.LowerGreen

end
