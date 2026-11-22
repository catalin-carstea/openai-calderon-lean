module

public import Proof.CalderonN.ActualTraceSymbolAtoms
public import Proof.CalderonN.ActualGaussConormalScalarCommutators

import Proof.CalderonN.ActualConormalCoefficientBounds
import Proof.CalderonN.WeakEnergyConormalJets
import Mathlib.Tactic

/-! The checked flat and Gauss conormal commutators provide a common
pointwise angular calculus for the actual velocity coefficients. -/

public section

noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Elementwise
set_option autoImplicit false
set_option maxHeartbeats 4750000
set_option backward.isDefEq.respectTransparency false
namespace CalderonN

open BallDirichlet TauCeti PDE
variable {dim : ℕ} [NeZero dim] [Nontrivial (Fin dim)]

structure ActualTraceAngularBasis (hn : 3 ≤ dim)
    (B R : Module.End ℝ (SmoothSphereTrace dim)) (J C : ℝ) where
  atoms : SmoothTraceSymbolAtoms hn
  identity : SmoothTraceSymbolBounds atoms 0 C 1
  degree : SmoothTraceSymbolBounds atoms 1 C B
  rotation : ∀ i j,SmoothTraceSymbolBounds atoms 1 C (smoothSphereTraceRotation i j)
  conormal : SmoothTraceSymbolBounds atoms 1 C R
  multiplier : ∀ m,TraceAngularAtom.HasJets J (.multiplier m) →
    SmoothTraceSymbolBounds atoms 0 C (smoothSphereTraceMul m)

theorem coordinateData_hasJets (i : I dim) (J : ℝ) (hJ : 1 ≤ J) :
    TraceAngularAtom.HasJets J (.multiplier (smoothCoordinateData i)) := by
  intro z hz
  let L := EuclideanSpace.proj (𝕜:=ℝ) i
  have hL : ‖L‖ ≤ 1 := norm_euclidean_proj_le_one i
  refine ⟨L.contDiff.contDiffAt,fun n hn => ?_⟩
  cases n with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact ((L.le_opNorm z).trans (mul_le_one₀ hL (norm_nonneg _) (mem_closedBall_zero_iff.mp hz))).trans hJ
  | succ n =>
    change ‖iteratedFDeriv ℝ (n+1) (fun y => L y) z‖ ≤ J
    simpa only [zero_add] using ((norm_iteratedFDeriv_affine_pos_le L 0 z (n+1) (Nat.succ_pos _)).trans hL).trans hJ

theorem uniform_actualTraceAngularBasis (hn : 3 ≤ dim)
    {Y Ω : Set (X dim)} (hY : IsOpen Y) (hΩ : IsOpen Ω) {m : ℕ} (hm : 5 ≤ m)
    (K ρ c₀ : ℝ) (M : Fin (m+1) → ℝ) (Cj : Fin 9 → ℝ)
    (hK : 1 ≤ K) (hρ : 0 < ρ) (J : ℝ) (hJ : 0 ≤ J)
    {A : X dim → Mat dim} (hA : ContDiff ℝ ∞ A)
    {lo hi : ℝ} (hEll : UniformlyEllipticOn (fixedBallOpens dim : Set (X dim)) A lo hi)
    {ell : X dim →L[ℝ] ℝ} (S : ∀ f : SmoothData dim,ConormalTaylorSolutions A ell f) :
    ∃ η C : ℝ,0 < η ∧ 1 ≤ C ∧ ∀ floor ≥ 1,∀ ε,0 ≤ ε → ε ≤ η → ∀ d,
      Admissible Y Ω K ρ c₀ M Cj floor ε d → ∀ x ∈ Y,∀ D : ActualGaussFiberData d x,
        Nonempty (ActualTraceAngularBasis hn (smoothTraceFlatDegree hA hEll S)
          (((d.radius x)^2)⁻¹ • D.conormalRemainder) J C) := by
  let B := smoothTraceFlatDegree hA hEll S
  have hB := smoothTraceFlatDegree_symmetric hn hA hEll S
  have hFin := smoothTraceFlatDegree_finite hA hEll S
  obtain ⟨η₀,C₀,hη₀,hC₀,hR⟩ := uniform_actualGauss_conormal_angularBounds hn hY hΩ hm K ρ c₀ M Cj hK hρ
  obtain ⟨η₁,C₁,hη₁,hC₁,hRM⟩ := uniform_actualGauss_scaledConormal_scalar_commutators hn hY hΩ hm K ρ c₀ M Cj hK hρ
  let U := smoothTraceMultiplierJetConstant dim J
  let V := smoothTraceMultiplierJetConstant dim (8*J)
  let W := 64*J
  let W₁ := smoothTraceRotationLiftConstant dim W W
  let W₂ := smoothTraceRotationLiftConstant dim W₁ W₁
  let L := U+V+2*(dim:ℝ)^4*(W+W₁+W₂)
  let C := 1+8*(dim:ℝ)+C₀+C₁*J+L
  have hU := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) J hJ
  have hV := smoothTraceMultiplierJetConstant_nonneg (dim:=dim) (8*J) (by positivity)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hW₁ : 0 ≤ W₁ := Real.sqrt_nonneg _
  have hW₂ : 0 ≤ W₂ := Real.sqrt_nonneg _
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 1 ≤ C := by
    dsimp only [C]
    linarith only [show 0 ≤ (dim:ℝ) by positivity,hC₀,mul_nonneg hC₁ hJ,hL]
  refine ⟨min η₀ η₁,C,lt_min hη₀ hη₁,hC,?_⟩
  intro floor hFloor ε hε hs d hd x hx D
  let R := ((d.radius x)^2)⁻¹ • D.conormalRemainder
  obtain ⟨_,hR₀,hRr,hRd⟩ := hR floor hFloor ε hε (hs.trans (min_le_left _ _)) d hd x hx D
  have hB' : D.flatDegree = B :=
    smoothTraceFlatDegree_eq hn D.smoothCoefficient hA D.ellipticCoefficient hEll D.solve S
  have hRC : SmoothTraceCommutatorBounds hn B 1 C R := by
    have hr : SmoothTraceCommutatorBounds hn B 1 C₀ R := by
      refine ⟨hC₀,hR₀,?_,hRr⟩
      rwa [hB'] at hRd
    refine hr.enlarge ?_
    dsimp only [C]
    linarith only [show 0 ≤ (dim:ℝ) by positivity,mul_nonneg hC₁ hJ,hL]
  have hRot (i j : I dim) : SmoothTraceCommutatorBounds hn B 1 C (smoothSphereTraceRotation i j) := by
    refine (smoothTraceRotation_commutatorBounds hn hA hEll S i j).enlarge ?_
    dsimp only [C]
    linarith only [hC₀,mul_nonneg hC₁ hJ,hL]
  have hMul (b : SmoothData dim) (hb : TraceAngularAtom.HasJets J (.multiplier b)) :
      SmoothTraceCommutatorBounds hn B 0 C (smoothSphereTraceMul b) := by
    have h' : SmoothTraceCommutatorBounds hn B 0 L (smoothSphereTraceMul b) :=
      smoothTraceMultiplier_commutatorBounds_of_jets hn B hB hFin b J hJ hb
    refine h'.enlarge ?_
    dsimp only [C]
    linarith only [show 0 ≤ (dim:ℝ) by positivity,hC₀,mul_nonneg hC₁ hJ]
  have hRmul (b : SmoothData dim) (hb : TraceAngularAtom.HasJets J (.multiplier b)) :
      SmoothTraceAngularBound hn 0 C (R*smoothSphereTraceMul b-smoothSphereTraceMul b*R) := by
    refine (hRM floor hFloor ε hε (hs.trans (min_le_right _ _)) d hd x hx D b J hJ hb).enlarge ?_
    dsimp only [C]
    linarith only [show 0 ≤ (dim:ℝ) by positivity,hC₀,hL]
  have hDeg := (smoothTraceFlatDegree_commutatorBounds hn hA hEll S).bound.enlarge hC
  let Q := TraceAngularAtom.symbolAtoms hn B R J C hC hDeg hRot hRC hMul hRmul
  have hb := TraceAngularAtom.symbolBound hn B R J C hC hDeg hRot hRC hMul hRmul
  exact ⟨⟨Q,hb .identity trivial,hb .degree trivial,fun i j => hb (.rotation i j) trivial,
    hb .conormal trivial,fun b hb' => hb (.multiplier b) hb'⟩⟩

end CalderonN
