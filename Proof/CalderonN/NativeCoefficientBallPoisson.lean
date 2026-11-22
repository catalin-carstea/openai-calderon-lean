module

public import Proof.CalderonN.BallPoissonOperator

import Proof.CalderonN.BallRegularity.CommonSupportMatrix
import Mathlib.Tactic

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

namespace CalderonN

open BallDirichlet

variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

theorem exists_constantFamily_of_coefficientMatrix
    (s : ℕ) (A : SmoothCoefficientMatrix dim s) :
    ∃ (a : ℝ × X dim → Mat dim) (ha : ContDiff ℝ ∞ a) (K : Set (X dim)) (hK : IsCompact K)
      (hSupport : ∀ p z, z ∉ K → a (p,z) = 0),
      a = coefficientMatrixField s A ∘ Prod.snd ∧
      ∀ p : ℝ, commonSupportMatrixFamily s a ha K hK hSupport p = A := by
  let a : ℝ × X dim → Mat dim := coefficientMatrixField s A ∘ Prod.snd
  have ha : ContDiff ℝ ∞ a := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_coefficientValue s (A i j)).comp contDiff_snd
  let K := ⋃ i : I dim, ⋃ j : I dim, tsupport (coefficientValue s (A i j))
  have hK : IsCompact K :=
    isCompact_iUnion fun i => isCompact_iUnion fun j => hasCompactSupport_coefficientValue s (A i j)
  have hs (p : ℝ) (z : X dim) (hz : z ∉ K) : a (p,z) = 0 := by
    ext i j
    change coefficientValue s (A i j) z = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hh
    exact hz (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,hh⟩⟩)
  refine ⟨a,ha,K,hK,hs,rfl,?_⟩
  intro p
  funext i j
  apply Subtype.ext
  funext k
  apply BoundedContinuousFunction.ext
  intro z
  have hp : (commonSupportMatrixFamily s a ha K hK hs p i j).1 k z =
      iteratedFDeriv ℝ k.val (coefficientValue s (A i j)) z := by
    exact commonSupportCoefficientFamily_jet s (fun q => a q i j)
      (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK (fun p z hz => by rw [hs p z hz]; rfl) p k z
  exact hp.trans (coefficientJet_eq_iteratedFDeriv s (A i j) k z).symm

/-- The full Sobolev operator acts by the classical divergence on native
smooth lifts, including compact coefficient extensions of a local metric. -/
theorem fullBallDivergence_native_smooth (s : ℕ) (F : SmoothCoefficientMatrix dim (s+2))
    (u : SmoothData dim) :
    ∃ h : ContDiff ℝ ∞ (negativeBallDivergence (coefficientMatrixField (s+2) F) u.1),
      fullBallDivergenceL s F (smoothBallSobolev (s+2) u) =
        smoothBallSobolev s ⟨negativeBallDivergence (coefficientMatrixField (s+2) F) u.1,h⟩ := by
  obtain ⟨a,ha,K,hK,hS,rfl,hRep⟩ := exists_constantFamily_of_coefficientMatrix (s+2) F
  have h := fullBallDivergence_family_smooth s _ ha K hK hS 0 u
  dsimp only [Function.comp_apply] at h
  have hc : ContDiff ℝ ∞ (negativeBallDivergence (coefficientMatrixField (s+2) F) u.1) :=
    contDiff_negativeBallDivergence (ha.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)) u.2
  refine ⟨hc,?_⟩
  simpa only [hRep,Function.comp_apply] using h

/-- The native strong Poisson operator gives the classical solution for
its own exact coefficient field. -/
theorem exists_native_classicalBallPoisson
    (s : ℕ) (F : SmoothCoefficientMatrix dim (s+2)) {lo hi : ℝ}
    (hEll : TauCeti.PDE.UniformlyEllipticOn (fixedBallOpens dim : Set (X dim))
      (coefficientMatrixField (s+2) F) lo hi)
    (u : SmoothData dim) :
    ∃ b : X dim → ℝ, ∃ hb : ContDiff ℝ ∞ b,
      EqOn b u.1 (standardSphere dim) ∧
      EqOn (negativeBallDivergence (coefficientMatrixField (s+2) F) b) 0 (ball (0 : X dim) 1) ∧
      ballPoissonOperatorL s F (smoothBallSobolev (s+2) u) = smoothBallSobolev (s+2) ⟨b,hb⟩ := by
  obtain ⟨a,ha,K,hK,hS,rfl,hRep⟩ := exists_constantFamily_of_coefficientMatrix (s+2) F
  let d : ℝ × X dim → ℝ := u.1 ∘ Prod.snd
  have hd : ContDiff ℝ ∞ d := u.2.comp contDiff_snd
  obtain ⟨b,hb,hT,hH,hOp⟩ := exists_smooth_representative_ballPoissonOperator _ ha K hK hS
    univ (fun _ => lo) (fun _ => hi) (fun _ _ => hEll) d hd 0 (mem_univ _)
  exact ⟨b,hb,hT,hH,by simpa only [hRep,d,Function.comp_apply] using hOp s⟩

end CalderonN
