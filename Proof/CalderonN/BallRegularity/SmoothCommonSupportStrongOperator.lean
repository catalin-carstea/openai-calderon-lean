module

public import Proof.CalderonN.BallRegularity.ClosedCoefficientMultiplier
public import Proof.CalderonN.BallRegularity.CommonSupportMatrix
public import Proof.CalderonN.BallRegularity.StrongExistence
public import Proof.CalderonN.BallRegularity.BanachInverseFamily
/-! From Proof/Archive/SmoothCommonSupportStrongOperator.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section


set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

theorem contDiff_commonSupport_actual_strongDirichletOperator
    (hcalc : (FixedSobolevCalculus dim)) (s : ℕ)
    (a : H × (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → a (p,z) = 0) :
    ContDiff ℝ ∞ (fun p => strongDirichletOperator hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hz p)) := by
  have hm : ContDiff ℝ ∞ (fun p => coefficientMatrixMultiplierL hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hz p)) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact contDiff_commonSupport_actual_coefficientMultiplier hcalc (s+1)
      (fun p => a p i j) (contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
      (fun p z h => by rw [hz p z h]; rfl)
  change ContDiff ℝ ∞ (fun p => unitBallDivergenceL hcalc s
    (coefficientMatrixMultiplierL hcalc s (commonSupportMatrixFamily (s+2) a ha K hK hz p)))
  exact (unitBallDivergenceL hcalc s).contDiff.comp hm

theorem contDiffOn_commonSupport_actual_strongDirichletInverse
    (hcalc : (FixedSobolevCalculus dim)) (hreg : (FixedDirichletRegularity dim)) (s : ℕ)
    (a : H × (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ p z, z ∉ K → a (p,z) = 0)
    (q : Set H) (lam Lam : H → ℝ)
    (hUE : ∀ p ∈ q, TauCeti.PDE.UniformlyEllipticOn ((fixedBallOpens dim) : Set (X dim))
      (fun z => a (p,z)) (lam p) (Lam p)) :
    ContDiffOn ℝ ∞ (fun p => (strongDirichletOperator hcalc s
      (commonSupportMatrixFamily (s+2) a ha K hK hz p)).inverse) q := by
  apply contDiffOn_banachInverseFamily _ q
    (contDiff_commonSupport_actual_strongDirichletOperator hcalc s a ha K hK hz).contDiffOn
  intro p hp
  apply strongDirichletOperator_isInvertible_of_elliptic hcalc hreg s
  rw [coefficientMatrixField_commonSupportMatrixFamily]
  exact hUE p hp
end CalderonN.BallDirichlet
