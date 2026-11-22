module

public import Proof.Manuscript.MovingTrace.ParametricLayerSlice
public import Proof.CalderonN.Coordinates
public import Proof.CalderonPatch.BoundaryLayerCutoffEstimate
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000

open Set Finset Polynomial
open CalderonN (X I axis)
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer.ParametricLayerCoefficients

variable {n : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {U : Set (P × X n)} (B : ParametricLayerCoefficients (n := n) U)

theorem angularSlice_truncate (p : P) (ξ : I n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ)) (M : ℕ) :
    (B.truncate M).angularSlice p ξ hξ = (B.angularSlice p ξ hξ).truncate M := rfl

/-- The joint residual polynomial restricts to the published fixed-parameter
residual polynomial. Thus the exact Taylor cancellation identity can be
used while its quantitative estimates control auxiliary parameter jets. -/
theorem finiteResidualPolynomial_slice
    (hU : IsOpen U) (p : P) (ξ : I n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i))
    {K : Set (P × X n)} (hK : IsClosed K) {a : P × X n → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M : ℕ)
    {x : X n} (hx : x ∈ slice U p) :
    B.finiteResidualPolynomial a M (p,x) =
      (B.angularSlice p ξ hξ).finiteResidualPolynomial (fun y => a (p,y)) M x := by
  let C := B.angularSlice p ξ hξ
  have hEq (k : ℕ) : EqOn (fun y => B.layerPolynomial a k (p,y))
      (C.layerPolynomial (fun y => a (p,y)) k) (slice U p) :=
    B.layerPolynomial_slice hU p ξ hξ hAxis hK ha ha0 k
  have hκ : C.kappa x = B.kappa (p,x) := rfl
  have hForcing (j k : ℕ) :
      (B.truncate M).forcing j k (B.layerPolynomial a k) (p,x) =
        (C.truncate M).forcing j k (C.layerPolynomial (fun y => a (p,y)) k) x := by
    let Q := B.layerPolynomial a k
    let R := C.layerPolynomial (fun y => a (p,y)) k
    have he : EqOn (fun y => Q (p,y)) R (slice U p) := hEq k
    change (B.truncate M).forcing j k Q (p,x) = (C.truncate M).forcing j k R x
    have hAxis' : ∀ i, (B.truncate M).angularDirection i = (0,axis i) := hAxis
    have hSlice := (B.truncate M).forcing_slice hU p ξ hξ hAxis' j k
      (B.layerPolynomial_properties hU hK a ha ha0 k).1 hx
    rw [B.angularSlice_truncate] at hSlice
    have hSlice' : (B.truncate M).forcing j k Q (p,x) =
        (C.truncate M).forcing j k (fun y => Q (p,y)) x := hSlice
    refine hSlice'.trans ?_
    have h₁ (i : I n) :=
      profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) he C.kappa (2*k) (EuclideanSpace.single i 1)
    have h₂ (i l : I n) :=
      profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) (h₁ l) C.kappa (2*k+1) (EuclideanSpace.single i 1)
    simp [BoundaryLayerCoefficients.forcing,BoundaryLayerCoefficients.principalTerm,
      BoundaryLayerCoefficients.normalTerm,BoundaryLayerCoefficients.crossTerm,
      BoundaryLayerCoefficients.phaseDriftTerm,BoundaryLayerCoefficients.tangentSecondTerm,
      BoundaryLayerCoefficients.tangentFirstTerm,he hx,fun i => h₁ i hx, fun i l => h₂ i l hx]
  have hAt (k : ℕ) : B.layerPolynomial a k (p,x) = C.layerPolynomial (fun y => a (p,y)) k x := hEq k hx
  simp only [finiteResidualPolynomial,BoundaryLayerCoefficients.finiteResidualPolynomial]
  change triangularScalePolynomial _ _ _ _ = triangularScalePolynomial _ _ _ _
  apply congrArg₂ (triangularScalePolynomial M M)
  · funext k
    rw [hAt k]
    rfl
  · funext j k
    exact hForcing j k

theorem finiteResidualProfile_slice
    (hU : IsOpen U) (p : P) (ξ : I n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i))
    {K : Set (P × X n)} (hK : IsClosed K) {a : P × X n → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (M : ℕ)
    {x : X n} (hx : x ∈ slice U p) (h s : ℝ) :
    B.finiteResidualProfile a M h ((p,x),s) =
      (B.angularSlice p ξ hξ).finiteResidualProfile (fun y => a (p,y)) M h (x,s) := by
  rw [B.finiteResidualProfile_eq_eval,BoundaryLayerCoefficients.finiteResidualProfile_eq_eval,
    B.finiteResidualPolynomial_slice hU p ξ hξ hAxis hK ha ha0 M hx]
  rfl

/-- Polynomial readout of the normal and tangential derivatives of each
transport profile, including the derivatives in the cutoff commutator. -/
def layerJetPolynomial (a : P × X n → ℂ) (j : ℕ) : LayerJetIndex n → P × X n → Polynomial ℂ
  | .inl _ => B.layerPolynomial a j
  | .inr (.inl _) => fun q => profileDerivative (B.kappa q) (B.layerPolynomial a j q)
  | .inr (.inr (.inl i)) => profileSpatialDeriv (2*j) (B.angularDirection i) B.kappa (B.layerPolynomial a j)
  | .inr (.inr (.inr il)) => profileSpatialDeriv (2*j+1) (B.angularDirection il.1) B.kappa
      (profileSpatialDeriv (2*j) (B.angularDirection il.2) B.kappa (B.layerPolynomial a j))

theorem layerJetPolynomial_regular (hU : IsOpen U) {K : Set (P × X n)} (hK : IsClosed K)
    (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (j : ℕ) (i : LayerJetIndex n) : CoeffContDiffOn (B.layerJetPolynomial a j i) U := by
  have hP := (B.layerPolynomial_properties hU hK a ha ha0 j).1
  rcases i with _ | i
  · exact hP
  rcases i with _ | i
  · exact hP.derivative.sub (hP.C_mul (Complex.ofRealCLM.contDiff.comp_contDiffOn B.kappa_smooth))
  rcases i with i | il
  · exact hP.profileSpatialDeriv hU B.kappa_smooth (2*j) (B.angularDirection i)
  · exact (hP.profileSpatialDeriv hU B.kappa_smooth (2*j) (B.angularDirection il.2)).profileSpatialDeriv
      hU B.kappa_smooth (2*j+1) (B.angularDirection il.1)

theorem layerJetPolynomial_degree (hU : IsOpen U) {K : Set (P × X n)} (hK : IsClosed K)
    (a : P × X n → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ q ∉ K, a q = 0)
    (j : ℕ) (i : LayerJetIndex n) {q : P × X n} (hq : q ∈ U) :
    (B.layerJetPolynomial a j i q).natDegree ≤ 2*j+2 := by
  have hP := (B.layerPolynomial_properties hU hK a ha ha0 j).2.1 q hq
  rcases i with _ | i
  · exact hP.trans (by omega)
  rcases i with _ | i
  · exact (profileDerivative_natDegree_le _ _).trans (hP.trans (by omega))
  rcases i with i | il
  · exact (profileSpatialDeriv_natDegree_le (2*j) (B.angularDirection i) B.kappa _ hP).trans (by omega)
  · exact profileSpatialDeriv_natDegree_le _ _ _ _
      (profileSpatialDeriv_natDegree_le (2*j) (B.angularDirection il.2) B.kappa _ hP)

theorem layerJetPolynomial_slice (hU : IsOpen U) (p : P) (ξ : I n → ℝ)
    (hξ : ∀ i x, B.covector i (p,x) = (ξ i : ℂ))
    (hAxis : ∀ i, B.angularDirection i = (0,axis i))
    {K : Set (P × X n)} (hK : IsClosed K) {a : P × X n → ℂ}
    (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0) (j : ℕ) (i : LayerJetIndex n)
    {x : X n} (hx : x ∈ slice U p) :
    B.layerJetPolynomial a j i (p,x) =
      (B.angularSlice p ξ hξ).layerJetPolynomial (fun y => a (p,y)) j i x := by
  let C := B.angularSlice p ξ hξ
  let Q := B.layerPolynomial a j
  let R := C.layerPolynomial (fun y => a (p,y)) j
  have hBase : EqOn (fun y => Q (p,y)) R (slice U p) :=
    B.layerPolynomial_slice hU p ξ hξ hAxis hK ha ha0 j
  have hQ := (B.layerPolynomial_properties hU hK a ha ha0 j).1
  have hTan (l : I n) : EqOn
      (fun y => profileSpatialDeriv (2*j) (B.angularDirection l) B.kappa Q (p,y))
      (profileSpatialDeriv (2*j) (axis l) C.kappa R) (slice U p) := by
    intro y hy
    rw [hAxis l]
    exact (profileSpatialDeriv_slice hU hQ B.kappa_smooth (2*j) hy (axis l)).symm.trans
      (profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) hBase _ _ _ hy)
  rcases i with _ | i
  · exact hBase hx
  rcases i with _ | i
  · change profileDerivative (B.kappa (p,x)) (Q (p,x)) = profileDerivative (C.kappa x) (R x)
    have hQR : Q (p,x) = R x := hBase hx
    rw [hQR]
    rfl
  rcases i with i | il
  · simpa only [layerJetPolynomial,BoundaryLayerCoefficients.layerJetPolynomial,
      EuclideanSpace.basisFun_apply, CalderonN.axis] using hTan i hx
  · simp only [layerJetPolynomial,BoundaryLayerCoefficients.layerJetPolynomial,
      EuclideanSpace.basisFun_apply]
    change profileSpatialDeriv (2*j+1) (B.angularDirection il.1) B.kappa
        (profileSpatialDeriv (2*j) (B.angularDirection il.2) B.kappa Q) (p,x) =
      profileSpatialDeriv (2*j+1) (axis il.1) C.kappa
        (profileSpatialDeriv (2*j) (axis il.2) C.kappa R) x
    rw [hAxis il.1]
    have hD := hQ.profileSpatialDeriv hU B.kappa_smooth (2*j) (B.angularDirection il.2)
    refine (profileSpatialDeriv_slice hU hD B.kappa_smooth (2*j+1) hx (axis il.1)).symm.trans ?_
    exact profileSpatialDeriv_congr_fixed_kappa (isOpen_slice hU p) (hTan il.2) C.kappa (2*j+1) (axis il.1) hx

end CalderonPatch.BoundaryLayer.ParametricLayerCoefficients
