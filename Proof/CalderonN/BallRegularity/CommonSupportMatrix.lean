module

public import Proof.CalderonN.BallRegularity.CoefficientJetFamily
public import Proof.CalderonN.BallRegularity.CoefficientMatrixRegularity
/-! From Proof/Archive/CommonSupportMatrixInverse.lean in the Proposition 5.3 release
`f308cb9d8751b6590c8caa28736de77e063a41e1af8cad4e9dfa94819a8299b8`. Module layout adapted for Leanflow v2. -/

@[expose] public section


set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Elementwise
namespace CalderonN.BallDirichlet

variable {dim : ℕ} [NeZero dim]

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

def commonSupportCoefficientMatrix (r : ℕ) (g : Fin dim → Fin dim → H × (X dim) → ℝ)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0) (t : H) : SmoothCoefficientMatrix dim r :=
  fun i j => commonSupportCoefficientFamily r (g i j) (hg i j) K hK (hz i j) t

theorem coefficientMatrixField_commonSupportCoefficientMatrix (r : ℕ)
    (g : Fin dim → Fin dim → H × (X dim) → ℝ) (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ i j t x, x ∉ K → g i j (t,x) = 0) (t : H) :
    coefficientMatrixField r (commonSupportCoefficientMatrix r g hg K hK hz t) =
      fun x i j => g i j (t,x) := by
  funext x i j
  exact coefficientValue_commonSupportCoefficientFamily r (g i j) (hg i j) K hK (hz i j) t x

def commonSupportMatrixFamily (r : ℕ) (a : H × (X dim) → Matrix (Fin dim) (Fin dim) ℝ)
    (ha : ContDiff ℝ ∞ a) (K : Set (X dim)) (hK : IsCompact K)
    (hz : ∀ t z, z ∉ K → a (t,z) = 0) (t : H) : (SmoothCoefficientMatrix dim) r :=
  commonSupportCoefficientMatrix r (fun i j p => a p i j)
    (fun i j => contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun i j t z h => by rw [hz t z h]; rfl) t

theorem coefficientMatrixField_commonSupportMatrixFamily (r : ℕ)
    (a : H × (X dim) → Matrix (Fin dim) (Fin dim) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set (X dim)) (hK : IsCompact K) (hz : ∀ t z, z ∉ K → a (t,z) = 0) (t : H) :
    coefficientMatrixField r (commonSupportMatrixFamily r a ha K hK hz t) =
      fun z => a (t,z) :=
  coefficientMatrixField_commonSupportCoefficientMatrix r (fun i j p => a p i j)
    (fun i j => contDiff_pi.mp (contDiff_pi.mp ha i) j) K hK
    (fun i j t z h => by rw [hz t z h]; rfl) t

end CalderonN.BallDirichlet
