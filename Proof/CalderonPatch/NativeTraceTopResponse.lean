module

public import Proof.CalderonPatch.BoundaryNormalDriftJets
public import Proof.CalderonPatch.BoundaryTangentialDriftJets
public import Proof.CalderonPatch.BoundaryLayerTraceResponse

import Mathlib.Tactic

public section
noncomputable section
open Filter Finset Set
open scoped ContDiff

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField chartVolume)

variable {n : ℕ}
local notation "Y" => X n
local notation "Z" => X (n+1)

@[expose] def inverseQuadraticNormalJet (g : MetricField (n+1)) (k : ℕ) (ξ : I n → ℝ) (y : Y) : ℝ :=
  ∑ i : I n, ∑ j : I n, inverseNormalJet g k y i.succ j.succ * ξ i * ξ j

theorem inverseQuadraticNormalJet_zero (g : MetricField (n+1)) (ξ : I n → ℝ) (y : Y) :
    inverseQuadraticNormalJet g 0 ξ y = faceInverseQuadratic g ξ y := by
  simp only [inverseQuadraticNormalJet,inverseNormalJet_zero,faceInverseQuadratic,signedLayerCoordinates_face]

theorem contDiffOn_normalJetAt {O : Set Z} (hO : IsOpen O) {f : Z → ℝ}
    (hf : ContDiffOn ℝ ∞ f O) {U : Set Y} (hF : MapsTo normalFacePoint U O) (k : ℕ) :
    ContDiffOn ℝ ∞ (normalJetAt f k) U := by
  have hf' := hf.comp signedLayerCoordinates.contDiff.contDiffOn
    (mapsTo_preimage signedLayerCoordinates O)
  exact contDiffOn_normalTaylorCoeff (hO.preimage signedLayerCoordinates.continuous) hf'
    (fun y hy => by simpa only [Set.mem_preimage,signedLayerCoordinates_face] using hF hy) k

theorem contDiffOn_inverseQuadraticNormalJet {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)}
    (hg : CalderonN.SmoothMetric O g) {U : Set Y} (hF : MapsTo normalFacePoint U O)
    (k : ℕ) (ξ : I n → ℝ) : ContDiffOn ℝ ∞ (inverseQuadraticNormalJet g k ξ) U := by
  unfold inverseQuadraticNormalJet
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j _
  refine (((contDiffOn_normalJetAt hO (CalderonN.contDiffOn_metric_inv_entry hg i.succ j.succ) hF k).mul
    (contDiffOn_const (c := ξ i))).mul (contDiffOn_const (c := ξ j))).congr ?_
  intro y hy
  rw [inverseNormalJet_entry hO hg (hF hy)]

theorem traceCoefficient_metric_top_difference
    {O₁ O₂ : Set Z} (hO₁ : IsOpen O₁) (hO₂ : IsOpen O₂)
    {g₁ g₂ : MetricField (n+1)} (hg₁ : CalderonN.SmoothMetric O₁ g₁)
    (hg₂ : CalderonN.SmoothMetric O₂ g₂) (hN₁ : HasNormalMetricBlock 0 g₁ O₁)
    (hN₂ : HasNormalMetricBlock 0 g₂ O₂)
    {U W : Set Y} (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U)
    (hF₁ : MapsTo normalFacePoint U O₁) (hF₂ : MapsTo normalFacePoint U O₂)
    (ξ : I n → ℝ) (hξ : ξ ≠ 0) {K : Set Y} (hK : IsClosed K)
    (a : Y → ℂ) (ha : ContDiffOn ℝ ∞ a U) (ha0 : ∀ y ∉ K, a y = 0)
    (L : ℕ) (hJ : ∀ j ≤ L, EqOn (inverseNormalJet g₁ j) (inverseNormalJet g₂ j) W)
    {y : Y} (hy : y ∈ W) :
    let B₁ := boundaryLayerCoefficientsOfMetric hO₁ g₁ hg₁
      (fun x hx => by simpa only [signedLayerCoordinates_face] using hF₁ hx) ξ hξ
    let B₂ := boundaryLayerCoefficientsOfMetric hO₂ g₂ hg₂
      (fun x hx => by simpa only [signedLayerCoordinates_face] using hF₂ hx) ξ hξ
    let T := (g₁ (normalFacePoint y) * (inverseNormalJet g₁ (L+1) y - inverseNormalJet g₂ (L+1) y)).trace
    let Q := inverseQuadraticNormalJet g₁ (L+1) ξ y - inverseQuadraticNormalJet g₂ (L+1) ξ y
    B₁.traceCoefficient a (L+1) y - B₂.traceCoefficient a (L+1) y =
      a y * ((-(Q - B₁.kappa y ^ 2 * T) / (2 * B₁.kappa y) ^ (L+2) : ℝ) : ℂ) := by
  let B₁ := boundaryLayerCoefficientsOfMetric hO₁ g₁ hg₁
    (fun x hx => by simpa only [signedLayerCoordinates_face] using hF₁ hx) ξ hξ
  let B₂ := boundaryLayerCoefficientsOfMetric hO₂ g₂ hg₂
    (fun x hx => by simpa only [signedLayerCoordinates_face] using hF₂ hx) ξ hξ
  have hy₁ := hF₁ (hWU hy)
  have hy₂ := hF₂ (hWU hy)
  have hκ : EqOn B₁.kappa B₂.kappa W := by
    intro z hz
    change Real.sqrt (faceInverseQuadratic g₁ ξ z) = Real.sqrt (faceInverseQuadratic g₂ ξ z)
    have h := hJ 0 (Nat.zero_le _) hz
    rw [← inverseQuadraticNormalJet_zero,← inverseQuadraticNormalJet_zero]
    simp only [inverseQuadraticNormalJet,h]
  have hA : ∀ l < L+1, ∀ i j, EqOn (B₁.inverse l i j) (B₂.inverse l i j) W := by
    intro l hl i j z hz
    change normalFaceTaylor (fun x => (g₁ x)⁻¹ i.succ j.succ) l z =
      normalFaceTaylor (fun x => (g₂ x)⁻¹ i.succ j.succ) l z
    apply normalFaceTaylor_congr_normalJetAt
    rw [← inverseNormalJet_entry hO₁ hg₁ (hF₁ (hWU hz)),
      ← inverseNormalJet_entry hO₂ hg₂ (hF₂ (hWU hz)),hJ l (by omega) hz]
  have hτ : ∀ l, l+1 < L+1 → EqOn (B₁.normalDrift l) (B₂.normalDrift l) W := by
    intro l hl z hz
    change normalFaceTaylor (fun x => (-2) * laplaceFirstCoeff g₁ x 0) l z =
      normalFaceTaylor (fun x => (-2) * laplaceFirstCoeff g₂ x 0) l z
    apply normalFaceTaylor_congr_normalJetAt
    apply sub_eq_zero.mp
    rw [signed_normalDrift_top_difference hO₁ hO₂ hg₁ hg₂ hN₁ hN₂
      (hF₁ (hWU hz)) (hF₂ (hWU hz)) l (fun j hj => hJ j (by omega) hz),
      hJ (l+1) (by omega) hz,sub_self,mul_zero,Matrix.trace_zero]
  have hc : ∀ l < L+1, ∀ i, EqOn (B₁.tangentDrift l i) (B₂.tangentDrift l i) W := by
    intro l hl i z hz
    exact normalFaceTaylor_congr_normalJetAt
      (eqOn_tangentDrift_normalJet_of_eqOn_inverseNormalJet hO₁ hO₂ hg₁ hg₂ hN₁ hN₂ hW
        (hF₁.mono_left hWU) (hF₂.mono_left hWU) l (fun j hj => hJ j (by omega)) i hz)
  have hP {O : Set Z} (hO : IsOpen O) {g : MetricField (n+1)} (hg : CalderonN.SmoothMetric O g)
      (hF : MapsTo normalFacePoint U O) :
      let B := boundaryLayerCoefficientsOfMetric hO g hg
        (fun x hx => by simpa only [signedLayerCoordinates_face] using hF hx) ξ hξ
      (∑ i, ∑ j, B.inverse (L+1) i j y * (ξ i : ℂ) * (ξ j : ℂ)) =
        (inverseQuadraticNormalJet g (L+1) ξ y : ℂ) / ((L+1).factorial : ℂ) := by
    dsimp only [boundaryLayerCoefficientsOfMetric]
    simp only [normalFaceTaylor_eq_normalJetAt, ← inverseNormalJet_entry hO hg (hF (hWU hy)),
      inverseQuadraticNormalJet,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_div]
    exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by ring))
  have hTop := B₁.traceCoefficient_top_difference B₂ hU hK a ha ha0 hW hWU hκ
    (L+1) (Nat.succ_pos _) hA hτ hc hy
  have hN : L+1-1 = L := Nat.add_sub_cancel L 1
  have hFact := trace_factorial_response L (B₁.kappa y : ℂ)
    (inverseQuadraticNormalJet g₁ (L+1) ξ y : ℂ) (inverseQuadraticNormalJet g₂ (L+1) ξ y : ℂ)
    (normalJetAt (fun z => (-2) * laplaceFirstCoeff g₁ z 0) L y : ℂ)
    (normalJetAt (fun z => (-2) * laplaceFirstCoeff g₂ z 0) L y : ℂ)
    (Complex.ofReal_ne_zero.mpr (B₁.kappa_pos y (hWU hy)).ne')
  rw [hN,hP hO₁ hg₁ hF₁,hP hO₂ hg₂ hF₂] at hTop
  change _ = a y * ((2 * (B₁.kappa y : ℂ))⁻¹ ^ (L+1) * (L.factorial : ℂ) *
    (((normalFaceTaylor (fun z => (-2) * laplaceFirstCoeff g₁ z 0) L y -
        normalFaceTaylor (fun z => (-2) * laplaceFirstCoeff g₂ z 0) L y) / 2) * (B₁.kappa y : ℂ)) - _) at hTop
  rw [normalFaceTaylor_eq_normalJetAt,normalFaceTaylor_eq_normalJetAt,hFact] at hTop
  change B₁.traceCoefficient a (L+1) y - B₂.traceCoefficient a (L+1) y = _
  rw [hTop]
  simp only [← Complex.ofReal_sub,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_ofNat,
    ← Complex.ofReal_neg,← Complex.ofReal_div,
    signed_normalDrift_top_difference hO₁ hO₂ hg₁ hg₂ hN₁ hN₂ hy₁ hy₂ L
      (fun j hj => hJ j hj hy)]
  rfl

end CalderonPatch.BoundaryLayer
