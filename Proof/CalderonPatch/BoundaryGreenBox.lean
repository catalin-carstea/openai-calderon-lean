module

public import Proof.CalderonPatch.BoundaryNormalLaplacian
public import Proof.CalderonN.MetricDivergence

import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Filter Matrix MeasureTheory Set
open scoped ContDiff Topology

namespace CalderonPatch

open CalderonN (I X MetricField axis coordDeriv laplace chartVolume divergenceFlux)

variable {m : ℕ}

private theorem integral_divergence_eq_bottomFace {a b : Fin (m + 1) → ℝ} (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ)
    (D : Fin (m + 1) → (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) →L[ℝ] ℝ)
    (hC : ∀ i, ContinuousOn (F i) (Icc a b))
    (hD : ∀ y ∈ Set.pi univ (fun i => Ioo (a i) (b i)), ∀ i, HasFDerivAt (F i) (D i y) y)
    (hInt : IntegrableOn (fun y => ∑ i, D i y (Pi.single i 1)) (Icc a b))
    (hTop : ∀ i, EqOn (fun z => F i (Fin.insertNth i (b i) z)) 0 (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hSides : ∀ i ≠ (0 : Fin (m + 1)),
      EqOn (fun z => F i (Fin.insertNth i (a i) z)) 0 (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    (∫ y in Icc a b, ∑ i, D i y (Pi.single i 1)) =
      -∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), F 0 (Fin.insertNth 0 (a 0) z) := by
  have h := integral_divergence_of_hasFDerivAt_off_countable' a b hab F D ∅
    countable_empty hC (fun y hy => hD y hy.1) hInt
  rw [h, Finset.sum_eq_single (0 : Fin (m + 1))]
  · have hz : (∫ x in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0), F 0 (Fin.insertNth 0 (b 0) x)) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Icc (hTop 0)]
      simp
    rw [hz, zero_sub]
  · intro i _ hi
    rw [setIntegral_congr_fun measurableSet_Icc (hTop i),
      setIntegral_congr_fun measurableSet_Icc (hSides i hi)]
    simp
  · simp

theorem insertNth_mem_box {a b : Fin (m + 1) → ℝ}
    (i : Fin (m + 1)) {s : ℝ} (hs : s ∈ Icc (a i) (b i))
    {z : Fin m → ℝ} (hz : z ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) :
    Fin.insertNth i s z ∈ Icc a b := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j
      simpa using hs.1
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq h
      simpa using hz.1 k
  · intro j
    by_cases h : j = i
    · subst j
      simpa using hs.2
    · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq h
      simpa using hz.2 k

/-- Green's formula on a coordinate half box, relative to Lebesgue
measure in the coefficient coordinates. The supported test leaves
only the outward normal flux at the measured face. -/
theorem greenIdentity_normalBox
    {a b : Fin (m + 1) → ℝ} (hab : a ≤ b) (hBottom : a 0 = 0)
    {U : Set (X (m + 1))} (hU : IsOpen U)
    (hBox : MapsTo (WithLp.toLp 2) (Icc a b) U)
    {g : MetricField (m + 1)} (hg : CalderonN.SmoothMetric U g)
    (hNormal : HasNormalMetricBlock 0 g U)
    {u v : X (m + 1) → ℝ} (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v U)
    (hTop : ∀ i, EqOn (fun z => v (WithLp.toLp 2 (Fin.insertNth i (b i) z))) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)))
    (hSide : ∀ i ≠ (0 : Fin (m + 1)), EqOn
      (fun z => v (WithLp.toLp 2 (Fin.insertNth i (a i) z))) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove))) :
    (∫ y in Icc a b,
      (v (WithLp.toLp 2 y) * (chartVolume g (WithLp.toLp 2 y) * laplace g u (WithLp.toLp 2 y))) +
      ∑ i, coordDeriv i v (WithLp.toLp 2 y) * divergenceFlux g u (WithLp.toLp 2 y) i) =
      -∫ z in Icc (a ∘ Fin.succAbove 0) (b ∘ Fin.succAbove 0),
        v (WithLp.toLp 2 (Fin.insertNth 0 0 z)) *
        (chartVolume g (WithLp.toLp 2 (Fin.insertNth 0 0 z)) *
          coordDeriv 0 u (WithLp.toLp 2 (Fin.insertNth 0 0 z))) := by
  let L := (WithLp.linearEquiv 2 ℝ (Fin (m + 1) → ℝ)).symm.toContinuousLinearEquiv
  let P (i : Fin (m + 1)) (x : X (m + 1)) := v x * divergenceFlux g u x i
  let F (i : Fin (m + 1)) (y : Fin (m + 1) → ℝ) := P i (L y)
  let D (i : Fin (m + 1)) (y : Fin (m + 1) → ℝ) :=
    (fderiv ℝ (P i) (L y)).comp (L : (Fin (m + 1) → ℝ) →L[ℝ] X (m + 1))
  have hP (i : Fin (m + 1)) : ContDiffOn ℝ ∞ (P i) U :=
    hv.mul (CalderonN.contDiffOn_divergenceFlux hU hg hu i)
  have hLP (y : Fin (m + 1) → ℝ) : L y = WithLp.toLp 2 y := rfl
  have hLaxis (i : Fin (m + 1)) : L (Pi.single i 1) = axis i := rfl
  have hC (i : Fin (m + 1)) : ContinuousOn (F i) (Icc a b) :=
    (hP i).continuousOn.comp L.continuous.continuousOn (fun _ h => hBox h)
  have hDu (i : Fin (m + 1)) {y : Fin (m + 1) → ℝ} (hy : y ∈ Icc a b) :
      HasFDerivAt (F i) (D i y) y :=
    (((hP i).contDiffAt (hU.mem_nhds (hBox hy))).differentiableAt (by simp)).hasFDerivAt.comp y
      L.toContinuousLinearMap.hasFDerivAt
  have hD : ∀ y ∈ Set.pi univ (fun i => Ioo (a i) (b i)), ∀ i, HasFDerivAt (F i) (D i y) y := by
    intro y hy i
    exact hDu i ⟨fun k => ((mem_pi.mp hy) k (mem_univ k)).1.le,
      fun k => ((mem_pi.mp hy) k (mem_univ k)).2.le⟩
  have hInt : IntegrableOn (fun y => ∑ i, D i y (Pi.single i 1)) (Icc a b) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply continuousOn_finsetSum
    intro i _
    change ContinuousOn (fun y => fderiv ℝ (P i) (L y) (L (Pi.single i 1))) _
    exact (((hP i).fderiv_of_isOpen (m := 0) hU (by simp)).continuousOn.clm_apply continuousOn_const).comp
      L.continuous.continuousOn (fun _ hx => hBox hx)
  have hT (i : Fin (m + 1)) : EqOn (fun z => F i (Fin.insertNth i (b i) z)) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro z hz
    change v (L _) * _ = 0
    rw [hLP]
    exact mul_eq_zero_of_left (hTop i hz) _
  have hS (i : Fin (m + 1)) (hi : i ≠ 0) : EqOn (fun z => F i (Fin.insertNth i (a i) z)) 0
      (Icc (a ∘ i.succAbove) (b ∘ i.succAbove)) := by
    intro z hz
    change v (L _) * _ = 0
    rw [hLP]
    exact mul_eq_zero_of_left (hSide i hi hz) _
  have h := integral_divergence_eq_bottomFace hab F D hC hD hInt hT hS
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    have hx : WithLp.toLp 2 y ∈ U := hBox hy
    have hprod (i : Fin (m + 1)) :
        D i y (Pi.single i 1) =
          coordDeriv i v (WithLp.toLp 2 y) * divergenceFlux g u (WithLp.toLp 2 y) i +
            v (WithLp.toLp 2 y) * coordDeriv i (fun x => divergenceFlux g u x i) (WithLp.toLp 2 y) := by
      change fderiv ℝ (P i) (L y) (L (Pi.single i 1)) = _
      have hv' := ((hv.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have hflux' := (((CalderonN.contDiffOn_divergenceFlux hU hg hu i).contDiffAt
        (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      change fderiv ℝ (fun x => v x * divergenceFlux g u x i) (L y) (L (Pi.single i 1)) = _
      change fderiv ℝ (v * fun x => divergenceFlux g u x i) (L y) (L (Pi.single i 1)) = _
      rw [hLaxis, hLP, (hv'.mul hflux').fderiv]
      simp only [coordDeriv, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
      ring
    simp only [hprod, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← CalderonN.chartVolume_mul_laplace_eq_divergence hU hg hu hx]
    ring
  · congr 1
    apply setIntegral_congr_fun measurableSet_Icc
    intro z hz
    have hx : WithLp.toLp 2 (Fin.insertNth 0 (a 0) z) ∈ U :=
      hBox (insertNth_mem_box 0 ⟨le_rfl, hab 0⟩ hz)
    have hflux : divergenceFlux g u (WithLp.toLp 2 (Fin.insertNth 0 (a 0) z)) 0 =
      chartVolume g (WithLp.toLp 2 (Fin.insertNth 0 (a 0) z)) *
        coordDeriv 0 u (WithLp.toLp 2 (Fin.insertNth 0 (a 0) z)) := by
      simp only [divergenceFlux, CalderonN.divergenceCoeff, inverse_normalMetricBlock_row hNormal hx (hg.2 _ hx),
        mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    change _ = v (L _) * divergenceFlux g u (L _) 0
    rw [hLP, hflux, hBottom]

end CalderonPatch
