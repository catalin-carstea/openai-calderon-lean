module

public import Proof.CalderonPatch.MeasuredBoundaryMetric
public import Proof.CalderonPatch.NormalJetTraceDetermination

import Mathlib.Tactic

public section
noncomputable section
open Filter Finset MeasureTheory Set
open scoped ContDiff Manifold

namespace CalderonPatch.BoundaryLayer

open CalderonN (X I Mat MetricField chartVolume)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanHalfSpace (n+1)) M] [IsManifold (𝓡∂ (n+1)) ∞ M]

local notation "Y" => X n
local notation "Z" => X (n+1)
local notation "J" => 𝓡∂ (n+1)
local notation "Qface[" l "," r "]" => Icc (l ∘ Fin.succAbove 0) (r ∘ Fin.succAbove 0)

variable {d₁ d₂ : DirichletData n M} {p₁ p₂ : M}
  (D₁ : NativeBoundaryMetricChart d₁.metric p₁) (D₂ : NativeBoundaryMetricChart d₂.metric p₂)

/-- Equality of the measured Dirichlet quadratic energies determines
every pure normal derivative of the actual metric along a shared face. -/
theorem normalMetricJets_eqOn_of_patchEnergy (hn : 2 ≤ n)
    {Γ : Set ((J).boundary M)} (hMeas : PatchEnergyEqual d₁.metric d₂.metric d₁.volume d₂.volume Γ)
    {l r : I (n+1) → ℝ} (hlr : l ≤ r) (hl0 : l 0 = 0)
    {O : Set Z} (hO : IsOpen O) (hOD₁ : O ⊆ D₁.ambient) (hOD₂ : O ⊆ D₂.ambient)
    (hBox : MapsTo (WithLp.toLp 2) (Icc l r) O)
    (hSame : EqOn D₁.coord.symm D₂.coord.symm (O ∩ {z | z 0 = 0}))
    (hΓ : MapsTo (D₁.coord.symm ∘ normalFacePoint) (tangentialBox l r) (Subtype.val '' Γ))
    {U : Set Y} (hU : IsOpen U)
    (hF₁ : MapsTo normalFacePoint U D₁.ambient) (hF₂ : MapsTo normalFacePoint U D₂.ambient)
    (hQU : MapsTo (WithLp.toLp 2) Qface[l,r] U)
    (η : ContDiffBump (0 : ℝ)) (hTop : η.rOut < r 0) :
    ∀ k : ℕ, ∀ i j : I (n+1),
      EqOn (normalJetAt (fun z => D₁.field z i j) k)
        (normalJetAt (fun z => D₂.field z i j) k) (tangentialBox l r) := by
  let g₁ := D₁.field
  let g₂ := D₂.field
  let V := tangentialBox l r
  have hV : IsOpen V := isOpen_tangentialBox l r
  have hVU : V ⊆ U := by
    intro y hy
    have he : WithLp.ofLp y ∈ Qface[l,r] :=
      ⟨fun i => (hy i).1.le,fun i => (hy i).2.le⟩
    simpa only [WithLp.toLp_ofLp] using hQU he
  have hG : EqOn (g₁ ∘ normalFacePoint) (g₂ ∘ normalFacePoint) V :=
    field_eqOn_face_of_patchEnergy D₁ D₂ hn hMeas hlr hl0 hO hOD₁ hOD₂ hBox hSame hΓ
      hU hF₁ hF₂ hQU η hTop
  have hStep (L : ℕ)
      (hJ : ∀ j ≤ L, EqOn (inverseNormalJet g₁ j) (inverseNormalJet g₂ j) V) :
      EqOn (inverseNormalJet g₁ (L+1)) (inverseNormalJet g₂ (L+1)) V := by
    let T (y : Y) := (g₁ (normalFacePoint y) *
      (inverseNormalJet g₁ (L+1) y - inverseNormalJet g₂ (L+1) y)).trace
    have hT : ContinuousOn T V := by
      have h₁ := contDiffOn_normalJetAt D₁.open_ambient
        ((contDiffOn_const (c := (-2 : ℝ))).mul (contDiffOn_laplaceFirstCoeff D₁.open_ambient D₁.smooth_field 0)) hF₁ L
      have h₂ := contDiffOn_normalJetAt D₂.open_ambient
        ((contDiffOn_const (c := (-2 : ℝ))).mul (contDiffOn_laplaceFirstCoeff D₂.open_ambient D₂.smooth_field 0)) hF₂ L
      refine ((h₁.sub h₂).continuousOn.mono hVU).congr ?_
      intro y hy
      exact (signed_normalDrift_top_difference D₁.open_ambient D₂.open_ambient
        D₁.smooth_field D₂.smooth_field D₁.normal_field D₂.normal_field
        (hF₁ (hVU hy)) (hF₂ (hVU hy)) L (fun j hj => hJ j hj hy)).symm
    have hRead (ξ : I n → ℝ) (hξ : ξ ≠ 0) : ∀ y ∈ V,
        inverseQuadraticNormalJet g₁ (L+1) ξ y - inverseQuadraticNormalJet g₂ (L+1) ξ y =
          faceInverseQuadratic g₁ ξ y * T y := by
      let B₁ := boundaryLayerCoefficientsOfMetric D₁.open_ambient g₁ D₁.smooth_field
        (fun y hy => by simpa only [signedLayerCoordinates_face] using hF₁ hy) ξ hξ
      let B₂ := boundaryLayerCoefficientsOfMetric D₂.open_ambient g₂ D₂.smooth_field
        (fun y hy => by simpa only [signedLayerCoordinates_face] using hF₂ hy) ξ hξ
      let Q (y : Y) := inverseQuadraticNormalJet g₁ (L+1) ξ y - inverseQuadraticNormalJet g₂ (L+1) ξ y
      let F (y : Y) := (Q y - B₁.kappa y ^ 2 * T y) / (2 * B₁.kappa y) ^ (L+2)
      let C (y : Y) := chartVolume g₁ (normalFacePoint y) * F y
      have hQ : ContinuousOn Q V := ((contDiffOn_inverseQuadraticNormalJet D₁.open_ambient
        D₁.smooth_field hF₁ (L+1) ξ).sub (contDiffOn_inverseQuadraticNormalJet D₂.open_ambient
          D₂.smooth_field hF₂ (L+1) ξ)).continuousOn.mono hVU
      have hκ : ContinuousOn B₁.kappa V := B₁.kappa_smooth.continuousOn.mono hVU
      have hκp (y : Y) (hy : y ∈ V) : 0 < B₁.kappa y := B₁.kappa_pos y (hVU hy)
      have hVolume : ContinuousOn (fun y => chartVolume g₁ (normalFacePoint y)) V :=
        ((CalderonN.contDiffOn_metric_volume D₁.smooth_field).continuousOn.comp
          continuous_normalFacePoint.continuousOn hF₁).mono hVU
      have hC : ContinuousOn C V := hVolume.mul
        ((hQ.sub ((hκ.pow 2).mul hT)).div (((continuousOn_const (c := (2 : ℝ))).mul hκ).pow (L+2))
          (fun y hy => pow_ne_zero _ (mul_ne_zero two_ne_zero (hκp y hy).ne')))
      have hMeasured := eqOn_faceCoefficientDifference_zero_of_patchEnergy D₁ D₂ hMeas hlr hl0 hO
        hOD₁ hOD₂ hBox hSame hΓ hU hF₁ hF₂ hQU ξ hξ η hTop (L+1) hC (by
          dsimp only
          intro a ha hac has y hy
          let b (z : Y) : ℂ := a z
          have hb : ContDiffOn ℝ ∞ b U := (Complex.ofRealCLM.contDiff.comp ha).contDiffOn
          have hb0 (z : Y) (hz : z ∉ tsupport a) : b z = 0 := by
            simp [b,image_eq_zero_of_notMem_tsupport hz]
          have hTop := traceCoefficient_metric_top_difference D₁.open_ambient D₂.open_ambient
            D₁.smooth_field D₂.smooth_field D₁.normal_field D₂.normal_field hU hV hVU hF₁ hF₂ ξ hξ
            hac.isClosed b hb hb0 L hJ hy
          have hTop' : B₁.traceCoefficient b (L+1) y - B₂.traceCoefficient b (L+1) y =
              b y * ((-F y : ℝ) : ℂ) := by
            change _ = _ at hTop
            simpa only [F,neg_div] using hTop
          have hρ : chartVolume g₂ (normalFacePoint y) = chartVolume g₁ (normalFacePoint y) :=
            congrArg (fun A : Mat (n+1) => Real.sqrt A.det) (hG hy).symm
          change faceEnergyCoefficient g₁ B₁ b (L+1) y -
            faceEnergyCoefficient g₂ B₂ b (L+1) y = _
          rw [faceEnergyCoefficient,faceEnergyCoefficient,hρ]
          have hCombine :
              -(chartVolume g₁ (normalFacePoint y) * ((starRingEnd ℂ) (b y) *
                B₁.traceCoefficient b (L+1) y).re) -
              -(chartVolume g₁ (normalFacePoint y) * ((starRingEnd ℂ) (b y) *
                B₂.traceCoefficient b (L+1) y).re) =
              -(chartVolume g₁ (normalFacePoint y) * ((starRingEnd ℂ) (b y) *
                (B₁.traceCoefficient b (L+1) y - B₂.traceCoefficient b (L+1) y)).re) := by
            rw [mul_sub,Complex.sub_re]
            ring
          rw [hCombine,hTop']
          simp only [b,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
            Complex.conj_re,Complex.conj_im,zero_mul,mul_zero,sub_zero,add_zero,neg_zero,C]
          ring)
      intro y hy
      have hPos : chartVolume g₁ (normalFacePoint y) ≠ 0 :=
        (Real.sqrt_pos.2 (D₁.smooth_field.2 _ (hF₁ (hVU hy))).det_pos).ne'
      have hF₀ : F y = 0 := (mul_eq_zero.mp (hMeasured hy)).resolve_left hPos
      have hDen : (2 * B₁.kappa y) ^ (L+2) ≠ 0 :=
        pow_ne_zero _ (mul_ne_zero two_ne_zero (hκp y hy).ne')
      have hE : Q y - B₁.kappa y ^ 2 * T y = 0 :=
        ((div_eq_iff hDen).mp hF₀).trans (zero_mul _)
      have hkSq : B₁.kappa y ^ 2 = faceInverseQuadratic g₁ ξ y :=
        Real.sq_sqrt (faceInverseQuadratic_pos D₁.smooth_field ξ hξ (by
          simpa only [signedLayerCoordinates_face] using hF₁ (hVU hy))).le
      rw [hkSq] at hE
      exact sub_eq_zero.mp hE
    intro y hy
    apply inverseNormalJet_eq_of_trace_direction hn D₁.open_ambient D₂.open_ambient
      D₁.smooth_field D₂.smooth_field D₁.normal_field D₂.normal_field (hF₁ (hVU hy)) (hF₂ (hVU hy))
    intro ξ
    by_cases hξ : ξ = 0
    · simp [hξ,inverseQuadraticNormalJet,faceInverseQuadratic]
    · exact hRead ξ hξ y hy
  have hAll (k : ℕ) : EqOn (inverseNormalJet g₁ k) (inverseNormalJet g₂ k) V := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero =>
        intro y hy
        rw [inverseNormalJet_zero,inverseNormalJet_zero]
        exact congrArg (fun A : Mat (n+1) => A⁻¹) (hG hy)
      | succ L => exact hStep L (fun j hj => ih j (Nat.lt_succ_iff.mpr hj))
  intro k i j y hy
  exact normalJetAt_metric_entry_eq_of_inverseNormalJet_eq D₁.open_ambient D₂.open_ambient
    D₁.smooth_field D₂.smooth_field (hF₁ (hVU hy)) (hF₂ (hVU hy)) k (fun l _ => hAll l hy) i j

end CalderonPatch.BoundaryLayer
