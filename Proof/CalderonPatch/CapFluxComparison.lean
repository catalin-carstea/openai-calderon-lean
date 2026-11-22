module

public import Proof.CalderonPatch.BoundaryChartTests
public import Proof.CalderonPatch.CapTraceCutoff

import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

public section
noncomputable section
open Filter MeasureTheory Set
open scoped ContDiff Matrix Topology

namespace CalderonPatch

open CalderonN (I X MetricField Mat axis coordDeriv laplace chartVolume divergenceCoeff divergenceFlux)

variable {m : ℕ}
local notation "N" => (m + 1)
local notation "Y" => (I N → ℝ)
local notation "E" => X N

private abbrev openBox (a b : Y) : Set Y :=
  Set.pi univ fun i => Ioo (a i) (b i)

/-- The cap in signed coordinates. The lower boundary is the graph of
the negative height and the upper boundary is the original flat face. -/
@[expose] def signedCap (h : X m → ℝ) : Set E :=
  {x | -(h (normalTangentialCoordinates x)) < x 0 ∧ x 0 < 0}

private abbrev overGraph (h : X m → ℝ) : Set E :=
  {x | -(h (normalTangentialCoordinates x)) ≤ x 0}

private theorem capFlux_contDiffOn
    {U : Set E} (hU : IsOpen U) {h : X m → ℝ} (hh : Continuous h)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hGraph : ∀ x ∈ U, x 0 = -h (normalTangentialCoordinates x) → u x = 0)
    {g : MetricField N} (hg : CalderonN.SmoothMetric U g)
    {ε : ℝ} (hε : 0 < ε) (i : I N) :
    ContDiffOn ℝ ∞ ((overGraph h).piecewise
      (fun x => capTraceCutoff ε (u x) * divergenceFlux g u x i) 0) U := by
  classical
  intro x hx
  let t (x : E) := x 0 + h (normalTangentialCoordinates x)
  have ht : Continuous t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)).continuous.add
      (hh.comp contDiff_normalTangentialCoordinates.continuous)
  rcases lt_trichotomy (t x) 0 with hNeg | hEq | hPos
  · apply (contDiffWithinAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt ht continuous_const).mem_nhds hNeg)] with y hy
      have hy' : t y < 0 := hy
      have hOut : y ∉ overGraph h := by
        intro hY
        have : -h (normalTangentialCoordinates y) ≤ y 0 := hY
        dsimp only [t] at hy'
        linarith
      simp [hOut]
    · have hOut : x ∉ overGraph h := by
        intro hX
        have : -h (normalTangentialCoordinates x) ≤ x 0 := hX
        dsimp only [t] at hNeg
        linarith
      simp [hOut]
  · have hG : x 0 = -h (normalTangentialCoordinates x) := by
      dsimp only [t] at hEq
      linarith
    have hzero : u x = 0 := hGraph x hx hG
    have hnear : ∀ᶠ y in 𝓝[U] x, |u y| < ε := by
      have hT : Tendsto (fun y => |u y|) (𝓝[U] x) (𝓝 |u x|) :=
        (hu.continuousOn x hx).abs
      exact hT ((isOpen_lt continuous_id continuous_const).mem_nhds (by simpa [hzero] using hε))
    apply (contDiffWithinAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [hnear] with y hy
      by_cases hY : y ∈ overGraph h
      · rw [piecewise_eq_of_mem _ _ _ hY, capTraceCutoff_zero_of_abs_le hε hy.le, zero_mul]
      · simp [hY]
    · have hK : capTraceCutoff ε (u x) = 0 :=
        capTraceCutoff_zero_of_abs_le hε (by simpa [hzero] using hε.le)
      have hX : x ∈ overGraph h := hG.ge
      rw [piecewise_eq_of_mem _ _ _ hX,hK,zero_mul]
  · have hK : ContDiffWithinAt ℝ ∞
        (fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i) U x :=
      (((capTraceCutoff_contDiff ε).comp_contDiffOn hu).mul
        (CalderonN.contDiffOn_divergenceFlux hU hg hu i)) x hx
    apply hK.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt continuous_const ht).mem_nhds hPos)] with y hy
      have hy' : 0 < t y := hy
      have hY : y ∈ overGraph h := by
        change -h (normalTangentialCoordinates y) ≤ y 0
        dsimp only [t] at hy'
        linarith
      exact piecewise_eq_of_mem _ _ _ hY
    · have hX : x ∈ overGraph h := by
        change -h (normalTangentialCoordinates x) ≤ x 0
        dsimp only [t] at hPos
        linarith
      exact piecewise_eq_of_mem _ _ _ hX

private theorem capFlux_pairing_eq_dotProduct (g : MetricField N) (u : E → ℝ) (x : E) :
    (∑ i, coordDeriv i u x * divergenceFlux g u x i) =
      (coordDeriv · u x) ⬝ᵥ ((show Mat N from fun i j => divergenceCoeff g x i j) *ᵥ
        (coordDeriv · u x)) := by
  simp only [divergenceFlux, Matrix.mulVec, dotProduct]

private theorem capFlux_divergence_at
    {U : Set E} (hU : IsOpen U) {h : X m → ℝ} (hh : Continuous h)
    {g : MetricField N} (hg : CalderonN.SmoothMetric U g)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hGraph : ∀ x ∈ U, x 0 = -h (normalTangentialCoordinates x) → u x = 0)
    (hEq : EqOn (laplace g u) 0 (signedCap h ∩ U))
    {ε : ℝ} (hε : 0 < ε) {x : E} (hx : x ∈ U) (hx₀ : x 0 < 0) :
    (∑ i, coordDeriv i ((overGraph h).piecewise
      (fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i) 0) x) =
      (signedCap h).indicator (fun y => deriv (capTraceCutoff ε) (u y) *
        ∑ i, coordDeriv i u y * divergenceFlux g u y i) x := by
  classical
  let t (x : E) := x 0 + h (normalTangentialCoordinates x)
  have ht : Continuous t :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : I N)).continuous.add
      (hh.comp contDiff_normalTangentialCoordinates.continuous)
  by_cases hIn : x ∈ signedCap h
  · rw [indicator_of_mem hIn]
    have hx₁ : -h (normalTangentialCoordinates x) < x 0 := hIn.1
    have htx : 0 < t x := by dsimp only [t]; linarith
    have he (i : I N) : (overGraph h).piecewise
          (fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i) 0 =ᶠ[𝓝 x]
        fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i := by
      filter_upwards [(isOpen_lt continuous_const ht).mem_nhds htx] with y hy
      have hy' : 0 < t y := hy
      have hY : y ∈ overGraph h := by
        change -h (normalTangentialCoordinates y) ≤ y 0
        dsimp only [t] at hy'
        linarith
      exact piecewise_eq_of_mem _ _ _ hY
    have huD := ((hu.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    have hK := ((capTraceCutoff_contDiff ε).differentiable (by simp) (u x)).hasDerivAt
    have hprod (i : I N) :
        coordDeriv i ((overGraph h).piecewise
          (fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i) 0) x =
          deriv (capTraceCutoff ε) (u x) * (coordDeriv i u x * divergenceFlux g u x i) +
          capTraceCutoff ε (u x) * coordDeriv i (fun y => divergenceFlux g u y i) x := by
      have hF := (((CalderonN.contDiffOn_divergenceFlux hU hg hu i).contDiffAt
        (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have hD := (hK.comp_hasFDerivAt x huD).mul hF
      have hdEq : fderiv ℝ (fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i) x =
          capTraceCutoff ε (u x) • fderiv ℝ (fun y => divergenceFlux g u y i) x +
            divergenceFlux g u x i • deriv (capTraceCutoff ε) (u x) • fderiv ℝ u x := hD.fderiv
      simp only [coordDeriv, (he i).fderiv_eq, hdEq, _root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      ring
    simp only [hprod, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← CalderonN.chartVolume_mul_laplace_eq_divergence hU hg hu hx,
      hEq ⟨hIn,hx⟩, Pi.zero_apply, mul_zero, add_zero]
  · rw [indicator_of_notMem hIn]
    have hLe : x 0 ≤ -h (normalTangentialCoordinates x) :=
      le_of_not_gt fun hy => hIn ⟨hy,hx₀⟩
    have he (i : I N) : (overGraph h).piecewise
          (fun y => capTraceCutoff ε (u y) * divergenceFlux g u y i) 0 =ᶠ[𝓝 x] 0 := by
      rcases lt_or_eq_of_le hLe with hlt | hEq'
      · have htx : t x < 0 := by dsimp only [t]; linarith
        filter_upwards [(isOpen_lt ht continuous_const).mem_nhds htx] with y hy
        have hy' : t y < 0 := hy
        have hY : y ∉ overGraph h := by
          intro hY
          have : -h (normalTangentialCoordinates y) ≤ y 0 := hY
          dsimp only [t] at hy'
          linarith
        exact piecewise_eq_of_notMem _ _ _ hY
      · have hu0 := hGraph x hx hEq'
        have hT : Tendsto (fun y => |u y|) (𝓝 x) (𝓝 |u x|) :=
          (hu.continuousOn.continuousAt (hU.mem_nhds hx)).abs
        filter_upwards [hT ((isOpen_lt continuous_id continuous_const).mem_nhds
          (by simpa [hu0] using hε))] with y hy
        by_cases hY : y ∈ overGraph h
        · rw [piecewise_eq_of_mem _ _ _ hY,capTraceCutoff_zero_of_abs_le hε hy.le,zero_mul]
          rfl
        · exact piecewise_eq_of_notMem _ _ _ hY
    simp only [coordDeriv,(he _).fderiv_eq,fderiv_zero,Pi.zero_apply,
      zero_apply,Finset.sum_const_zero]

private theorem integral_divergence_eq_topFace {a b : Y} (hab : a ≤ b)
    (F : I N → Y → ℝ) (D : I N → Y → Y →L[ℝ] ℝ)
    (hC : ∀ i, ContinuousOn (F i) (Icc a b))
    (hD : ∀ y ∈ openBox a b, ∀ i, HasFDerivAt (F i) (D i y) y)
    (hInt : IntegrableOn (fun y => ∑ i, D i y (Pi.single i 1)) (Icc a b))
    (hBottom : ∀ i, EqOn (fun z => F i (Fin.insertNth i (a i) z)) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hSides : ∀ i ≠ (0 : I N), EqOn (fun z => F i (Fin.insertNth i (b i) z)) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    (∫ y in Icc a b, ∑ i, D i y (Pi.single i 1)) =
      ∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), F 0 (Fin.insertNth 0 (b 0) z) := by
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab F D ∅
    countable_empty hC (fun y hy => hD y hy.1) hInt
  rw [h, Finset.sum_eq_single (0 : I N)]
  · rw [setIntegral_congr_fun measurableSet_Icc (hBottom 0)]
    simp
  · intro i _ hi
    rw [setIntegral_congr_fun measurableSet_Icc (hSides i hi),
      setIntegral_congr_fun measurableSet_Icc (hBottom i)]
    simp
  · simp

/-- A harmonic difference vanishing on the outer cap graph vanishes
throughout the cap if each smooth truncated test has nonpositive
flux at the flat seam. The cutoff extends the flux smoothly through
the lower graph, including the points where the cap closes up. -/
theorem eqOn_zero_signedCap_of_truncatedFlux
    {a b : Y} (hab : a ≤ b) (hTop : b 0 = 0)
    {U : Set E} (hU : IsOpen U)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {h : X m → ℝ} (hh : Continuous h)
    (hHeight : ∀ z, 0 ≤ h z ∧ a 0 < -h z)
    (hSupport : Function.support h ⊆ tangentialBox a b)
    {g : MetricField N} (hg : CalderonN.SmoothMetric U g)
    {u : E → ℝ} (hu : ContDiffOn ℝ ∞ u U)
    (hGraph : ∀ x ∈ U, x 0 = -h (normalTangentialCoordinates x) → u x = 0)
    (hEq : EqOn (laplace g u) 0 (signedCap h ∩ U))
    (hFlux : ∀ ε > 0,
      (∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0),
        capTraceCutoff ε (u (normalFacePoint (WithLp.toLp 2 z))) *
          divergenceFlux g u (normalFacePoint (WithLp.toLp 2 z)) 0) ≤ 0) :
    EqOn u 0 (signedCap h) := by
  classical
  let B := openBox a b
  have hB : IsOpen B := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have hBC : B ⊆ Icc a b := by
    intro y hy
    exact ⟨fun i => ((mem_pi.mp hy) i (mem_univ i)).1.le,
      fun i => ((mem_pi.mp hy) i (mem_univ i)).2.le⟩
  have hCapBox (x : E) (hx : x ∈ signedCap h) : WithLp.ofLp x ∈ B := by
    rw [Set.mem_pi]
    have hx₁ : -h (normalTangentialCoordinates x) < x 0 := hx.1
    have hx₂ : x 0 < 0 := hx.2
    have hs : normalTangentialCoordinates x ∈ Function.support h := by
      change h (normalTangentialCoordinates x) ≠ 0
      intro hZ
      linarith
    intro i _
    by_cases hI : i = 0
    · subst i
      rw [hTop]
      exact ⟨(hHeight _).2.trans hx₁,hx₂⟩
    · obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq hI
      exact hSupport hs j
  intro x hx
  change u x = 0
  by_contra hn
  let ε := |u x|/2
  have hε : 0 < ε := half_pos (abs_pos.mpr hn)
  let L := (WithLp.linearEquiv 2 ℝ Y).symm.toContinuousLinearEquiv
  let P (i : I N) : E → ℝ := (overGraph h).piecewise
    (fun v => capTraceCutoff ε (u v) * divergenceFlux g u v i) 0
  let F (i : I N) (y : Y) := P i (L y)
  let D (i : I N) (y : Y) := fderiv ℝ (P i) (L y) |>.comp (L : Y →L[ℝ] E)
  have hL (y : Y) : L y = WithLp.toLp 2 y := rfl
  have hLaxis (i : I N) : L (Pi.single i 1) = axis i := rfl
  have hP (i : I N) : ContDiffOn ℝ ∞ (P i) U :=
    capFlux_contDiffOn hU hh hu hGraph hg hε i
  have hFC (i : I N) : ContinuousOn (F i) (Icc a b) :=
    (hP i).continuousOn.comp L.continuous.continuousOn fun _ hy => hBox hy
  have hFD (y : Y) (hy : y ∈ B) (i : I N) : HasFDerivAt (F i) (D i y) y :=
    (((hP i).contDiffAt (hU.mem_nhds (hBox (hBC hy)))).differentiableAt
      (by simp)).hasFDerivAt.comp y L.toContinuousLinearMap.hasFDerivAt
  let S (y : Y) := ∑ i, D i y (Pi.single i 1)
  have hSC : ContinuousOn S (Icc a b) := by
    apply continuousOn_finsetSum
    intro i _
    change ContinuousOn (fun y => fderiv ℝ (P i) (L y) (L (Pi.single i 1))) _
    exact (((hP i).fderiv_of_isOpen (m := 0) hU (by simp)).continuousOn.clm_apply
      continuousOn_const).comp L.continuous.continuousOn (fun _ hy => hBox hy)
  have hSI : IntegrableOn S (Icc a b) := hSC.integrableOn_compact isCompact_Icc
  have hPzero {y : Y} (hy : y ∈ Icc a b)
      (hLow : y 0 ≤ -h (normalTangentialCoordinates (L y))) (i : I N) : P i (L y) = 0 := by
    rcases lt_or_eq_of_le hLow with hlt | he
    · have hY : L y ∉ overGraph h := fun hY => (not_le_of_gt hlt) hY
      exact piecewise_eq_of_notMem _ _ _ hY
    · have hY : L y ∈ overGraph h := he.ge
      have hG := hGraph (L y) (hBox hy) he
      have hK : capTraceCutoff ε (u (L y)) = 0 :=
        capTraceCutoff_zero_of_abs_le hε (by simpa [hG] using hε.le)
      change (overGraph h).piecewise _ _ (L y) = 0
      rw [piecewise_eq_of_mem _ _ _ hY,hK,zero_mul]
  have hBottom (i : I N) : EqOn (fun z => F i (Fin.insertNth i (a i) z)) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro z hz
    let y : Y := Fin.insertNth (α := fun _ => ℝ) i (a i) z
    have hy : y ∈ Icc a b := insertNth_mem_box _ ⟨le_rfl,hab i⟩ hz
    have hy₀ : y 0 ≤ 0 := (hy.2 _).trans_eq hTop
    apply hPzero hy _ i
    by_cases hi : i = 0
    · subst i
      change Fin.insertNth (α := fun _ : I N => ℝ) 0 (a 0) z 0 ≤ _
      rw [Fin.insertNth_apply_same]
      exact (hHeight _).2.le
    · have hZ : h (normalTangentialCoordinates (L y)) = 0 := by
        by_contra hn'
        have hh' := hSupport (show normalTangentialCoordinates (L y) ∈ Function.support h from hn')
        obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
        have hid : y i = a i := Fin.insertNth_apply_same _ _ _
        have hstrict : a i < y i := hj ▸ (hh' j).1
        exact (lt_irrefl (a i)) (hstrict.trans_eq hid)
      rwa [hZ,neg_zero]
  have hSides (i : I N) (hi : i ≠ 0) : EqOn (fun z => F i (Fin.insertNth i (b i) z)) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro z hz
    let y : Y := Fin.insertNth (α := fun _ => ℝ) i (b i) z
    have hy : y ∈ Icc a b := insertNth_mem_box _ ⟨hab i,le_rfl⟩ hz
    have hy₀ : y 0 ≤ 0 := (hy.2 _).trans_eq hTop
    apply hPzero hy _ i
    have hZ : h (normalTangentialCoordinates (L y)) = 0 := by
      by_contra hn'
      have hh' := hSupport (show normalTangentialCoordinates (L y) ∈ Function.support h from hn')
      obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
      have hid : y i = b i := Fin.insertNth_apply_same _ _ _
      have hstrict : y i < b i := hj ▸ (hh' j).2
      exact (lt_irrefl (b i)) (hid.symm.trans_lt hstrict)
    rwa [hZ,neg_zero]
  have hIntFlux := integral_divergence_eq_topFace hab F D hFC hFD hSI hBottom hSides
  have hFluxBelow : (∫ y in Icc a b, S y) ≤ 0 := by
    rw [hIntFlux]
    convert hFlux ε hε using 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro z _
    rw [hTop]
    let v := normalFacePoint (WithLp.toLp 2 z)
    have hv : v ∈ overGraph h := by
      change -h (normalTangentialCoordinates v) ≤ v 0
      rw [normalFacePoint_height]
      exact neg_nonpos.mpr (hHeight _).1
    exact piecewise_eq_of_mem _ _ _ hv
  have hSle (y : Y) (hy : y ∈ B) : 0 ≤ S y := by
    have hy₀ : (L y : E) 0 < 0 := ((mem_pi.mp hy) 0 (mem_univ _)).2.trans_eq hTop
    have hRead : S y = _ :=
      capFlux_divergence_at hU hh hg hu hGraph hEq hε (hBox (hBC hy)) hy₀
    rw [hRead]
    by_cases hY : L y ∈ signedCap h
    · rw [indicator_of_mem hY,capFlux_pairing_eq_dotProduct]
      exact mul_nonneg (capTraceCutoff_deriv_nonneg ε _) <|
        (CalderonN.divergenceMatrix_posDef g (L y) (hg.2 _ (hBox (hBC hy)))).posSemidef.dotProduct_mulVec_nonneg _
    · rw [indicator_of_notMem hY]
  have hVol : B =ᵐ[volume] Icc a b := Measure.univ_pi_Ioo_ae_eq_Icc
  have hI : IntegrableOn S B := hSI.mono_set hBC
  have hNA : 0 ≤ᵐ[volume.restrict B] S :=
    (ae_restrict_mem hB.measurableSet).mono hSle
  have hIntZero : (∫ y in B, S y) = 0 := by
    apply le_antisymm _ (integral_nonneg_of_ae hNA)
    exact (setIntegral_congr_set hVol).trans_le hFluxBelow
  have hSzero : EqOn S 0 B :=
    Measure.eqOn_open_of_ae_eq ((integral_eq_zero_iff_of_nonneg_ae hNA hI).mp hIntZero)
      hB (hSC.mono hBC) continuousOn_const
  have hCutDeriv (v : E) (hv : v ∈ signedCap h) :
      fderiv ℝ (fun y => capTraceCutoff ε (u y)) v = 0 := by
    have hy := hCapBox v hv
    have hvU : v ∈ U := by simpa using hBox (hBC hy)
    have hRead : S (WithLp.ofLp v) =
        (signedCap h).indicator (fun y => deriv (capTraceCutoff ε) (u y) *
          ∑ i, coordDeriv i u y * divergenceFlux g u y i) v := by
      have he : L (WithLp.ofLp v) = v := WithLp.toLp_ofLp _ _
      simp only [S,D,ContinuousLinearMap.comp_apply,he]
      exact capFlux_divergence_at hU hh hg hu hGraph hEq hε hvU hv.2
    rw [hSzero hy,Pi.zero_apply,indicator_of_mem hv,capFlux_pairing_eq_dotProduct] at hRead
    have he : deriv (capTraceCutoff ε) (u v) = 0 ∨ (coordDeriv · u v) = 0 := by
      rcases mul_eq_zero.mp hRead.symm with h | h
      · exact Or.inl h
      · refine Or.inr (not_not.mp fun hne => ?_)
        have hp := (CalderonN.divergenceMatrix_posDef g v (hg.2 _ hvU)).dotProduct_mulVec_pos hne
        exact hp.ne' h
    have huD := ((hu.contDiffAt (hU.mem_nhds hvU)).differentiableAt (by simp)).hasFDerivAt
    have hK := ((capTraceCutoff_contDiff ε).differentiable (by simp) (u v)).hasDerivAt
    have hdEq : fderiv ℝ (fun y => capTraceCutoff ε (u y)) v =
        deriv (capTraceCutoff ε) (u v) • fderiv ℝ u v := (hK.comp_hasFDerivAt v huD).fderiv
    rw [hdEq]
    rcases he with h | h
    · rw [h,zero_smul]
    · have hD : fderiv ℝ u v = 0 := by
        have hLinear : (fderiv ℝ u v).toLinearMap = 0 := by
          apply (EuclideanSpace.basisFun (I N) ℝ |>.toBasis).ext
          intro i
          simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,axis,
            ContinuousLinearMap.coe_coe,LinearMap.zero_apply,Pi.zero_apply,coordDeriv] using congrFun h i
        exact ContinuousLinearMap.ext (fun w => DFunLike.congr_fun hLinear w)
      rw [hD,smul_zero]
  let z := normalTangentialCoordinates x
  let j (t : ℝ) : E := WithLp.toLp 2 (Fin.insertNth 0 t (WithLp.ofLp z))
  have hj₀ (t : ℝ) : j t 0 = t := by
    simp [j,Fin.insertNth_apply_same]
  have hjZ (t : ℝ) : normalTangentialCoordinates (j t) = z := by
    ext i
    simp [j,normalTangentialCoordinates]
  have hjEq (v : E) (hv : normalTangentialCoordinates v = z) : j (v 0) = v := by
    apply WithLp.ofLp_injective
    have he : WithLp.ofLp z = Fin.removeNth 0 (WithLp.ofLp v) :=
      congrArg WithLp.ofLp hv.symm
    change Fin.insertNth 0 (v 0) (WithLp.ofLp z) = WithLp.ofLp v
    rw [he,Fin.insertNth_self_removeNth]
  have hV (t : ℝ) (ht : t ∈ Icc (-h z) (x 0)) : j t ∈ U := by
    have hzy : WithLp.ofLp z ∈ Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0) :=
      ⟨fun i => ((mem_pi.mp (hCapBox x hx)) _ (mem_univ ((0 : I N).succAbove i))).1.le,
        fun i => ((mem_pi.mp (hCapBox x hx)) _ (mem_univ ((0 : I N).succAbove i))).2.le⟩
    apply hBox (insertNth_mem_box 0 _ hzy)
    rw [hTop]
    exact ⟨(hHeight _).2.le.trans ht.1,ht.2.trans hx.2.le⟩
  let y := j (-h z)
  let T := segment ℝ y x
  have hSeg (v : E) (hv : v ∈ T) :
      normalTangentialCoordinates v = z ∧ v 0 ∈ Icc (-h z) (x 0) := by
    rw [show T = _ from segment_eq_image_lineMap ℝ y x] at hv
    obtain ⟨t,ht,rfl⟩ := hv
    constructor
    · ext i
      let k := (0 : I N).succAbove i
      change (AffineMap.lineMap y x t) k = z i
      rw [AffineMap.lineMap_apply_module]
      have hY : y k = z i := congrFun (congrArg WithLp.ofLp (hjZ (-h z))) i
      have hX : x k = z i := rfl
      change (1-t) * y k + t * x k = z i
      rw [hY,hX]
      ring
    · have hA : -h z ∈ Icc (-h z) (x 0) := ⟨le_rfl,hx.1.le⟩
      have hB' : x 0 ∈ Icc (-h z) (x 0) := ⟨hx.1.le,le_rfl⟩
      have he : (AffineMap.lineMap y x t) 0 = AffineMap.lineMap (-h z) (x 0) t := by
        simp only [AffineMap.lineMap_apply_module]
        change (1-t) * y 0 + t * x 0 = (1-t) * (-h z) + t * x 0
        rw [show y 0 = -h z from hj₀ _]
      rw [he]
      exact (convex_Icc _ _).mapsTo_lineMap hA hB' ht
  have hD (v : E) (hv : v ∈ T) :
      HasFDerivWithinAt (fun p : E => capTraceCutoff ε (u p)) (0 : E →L[ℝ] ℝ) T v := by
    obtain ⟨hZ,ht⟩ := hSeg v hv
    have hvU : v ∈ U := hjEq v hZ ▸ hV _ ht
    apply HasFDerivAt.hasFDerivWithinAt
    by_cases hEnd : v 0 = -h z
    · have hU0 : u v = 0 := hGraph v hvU (by rwa [hZ])
      have hT : Tendsto (fun p => |u p|) (𝓝 v) (𝓝 |u v|) :=
        (hu.continuousOn.continuousAt (hU.mem_nhds hvU)).abs
      apply (hasFDerivAt_const (c := (0 : ℝ)) (x := v)).congr_of_eventuallyEq
      filter_upwards [hT ((isOpen_lt continuous_id continuous_const).mem_nhds
        (by simpa [hU0] using hε))] with p hp
      exact capTraceCutoff_zero_of_abs_le hε hp.le
    · have hCap : v ∈ signedCap h := by
        change -h (normalTangentialCoordinates v) < v 0 ∧ v 0 < 0
        rw [hZ]
        exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hEnd),ht.2.trans_lt hx.2⟩
      rw [← hCutDeriv v hCap]
      exact ((((capTraceCutoff_contDiff ε).comp_contDiffOn hu).contDiffAt
        (hU.mem_nhds hvU)).differentiableAt (by simp)).hasFDerivAt
  have hN := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hD
    (C := 0) (by intro v hv; rw [norm_zero]) (convex_segment y x)
    (left_mem_segment ℝ y x) (right_mem_segment ℝ y x)
  have hJ : capTraceCutoff ε (u x) = capTraceCutoff ε (u y) :=
    sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [zero_mul] using hN))
  have hLower := hV (-h z) ⟨le_rfl,hx.1.le⟩
  have hZero := hGraph y hLower (by change j (-h z) 0 = _; rw [hj₀,hjZ])
  have hKzero : capTraceCutoff ε 0 = 0 :=
    capTraceCutoff_zero_of_abs_le hε (by simpa using hε.le)
  have hKid : capTraceCutoff ε (u x) = u x :=
    capTraceCutoff_eq_of_two_mul_le_abs hε (by dsimp [ε]; linarith)
  rw [hZero,hKzero,hKid] at hJ
  exact hn hJ

end CalderonPatch
