import Proof.AngularOutputSections
import Proof.WeightedOutputConvergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped ContDiff
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon.SphereHarmonic
open OAI.AnisotropicCalderon.AngularShiftGraph
open OAI.AnisotropicCalderon.HarmonicDerivativeOperator

def angularRaisingSum (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) : X → SphereL2 :=
  fun y => ∑ i,angularRaisingSection i (H i) G (hH i) hG (b i) y

def angularLoweringSum (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) : X → SphereL2 :=
  fun y => ∑ i,angularLoweringSection i (H i) G (hH i) hG (b i) y

lemma harmonicProjection_angularRaisingSum_zero (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) (y : X) :
    harmonicProjection 0 (angularRaisingSum H G hH hG b y) = 0 := by
  rw [angularRaisingSum,map_sum]
  have hh (i : I) := (angularRaisingSection_graph i (H i) G (hH i) hG (b i) y).1
  change ∑ i,harmonicProjection 0 (angularRaisingSection i (H i) G (hH i) hG (b i) y) = 0
  simp_rw [show ∀ i,harmonicProjection 0 (angularRaisingSection i (H i) G (hH i) hG (b i) y) = 0 from hh]
  exact Finset.sum_const_zero

lemma harmonicProjection_angularRaisingSum_succ (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) (y : X) (k : ℕ) :
    harmonicProjection (k+1) (angularRaisingSum H G hH hG b y) =
      ∑ i,harmonicDerivativeAdjoint sphereFischerInner k i
        (harmonicProjection k (weightedAngularSection (H i) G (hH i) hG (b i) 1 y)) := by
  rw [angularRaisingSum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (angularRaisingSection_graph i (H i) G (hH i) hG (b i) y).2 k

lemma harmonicProjection_angularLoweringSum (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) (y : X) (k : ℕ) :
    harmonicProjection k (angularLoweringSum H G hH hG b y) =
      ∑ i,harmonicDerivative sphereFischerInner k i
        (harmonicProjection (k+1) (weightedAngularSection (H i) G (hH i) hG (b i) (-1) y)) := by
  rw [angularLoweringSum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact angularLoweringSection_graph i (H i) G (hH i) hG (b i) y k

lemma contDiff_angularRaisingSum (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ)
    (hb : ∀ i,ContDiff ℝ ∞ (b i)) : ContDiff ℝ ∞ (angularRaisingSum H G hH hG b) :=
  ContDiff.sum (fun i _ => contDiff_angularRaisingSection i (H i) G (hH i) hG (b i) (hb i))

lemma contDiff_angularLoweringSum (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ)
    (hb : ∀ i,ContDiff ℝ ∞ (b i)) : ContDiff ℝ ∞ (angularLoweringSum H G hH hG b) :=
  ContDiff.sum (fun i _ => contDiff_angularLoweringSection i (H i) G (hH i) hG (b i) (hb i))

lemma angularRaisingSum_zero (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) (S : Set X)
    (hHz : ∀ i,∀ y ∉ S,∀ v : UnitSphere,H i (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) :
    angularRaisingSum H G hH hG b y = 0 := by
  unfold angularRaisingSum
  simp_rw [show ∀ i,angularRaisingSection i (H i) G (hH i) hG (b i) y = 0 from
    fun i => angularRaisingSection_zero i (H i) G (hH i) hG (b i) S (hHz i) hGz hy]
  exact Finset.sum_const_zero

lemma angularLoweringSum_zero (H : I → X × X → ℝ) (G : X × X → ℝ)
    (hH : ∀ i,ContDiff ℝ ∞ (H i)) (hG : ContDiff ℝ ∞ G) (b : I → X → ℝ) (S : Set X)
    (hHz : ∀ i,∀ y ∉ S,∀ v : UnitSphere,H i (y,v.val) = 0)
    (hGz : ∀ y ∉ S,∀ v : UnitSphere,G (y,v.val) = 0) {y : X} (hy : y ∉ S) :
    angularLoweringSum H G hH hG b y = 0 := by
  unfold angularLoweringSum
  simp_rw [show ∀ i,angularLoweringSection i (H i) G (hH i) hG (b i) y = 0 from
    fun i => angularLoweringSection_zero i (H i) G (hH i) hG (b i) S (hHz i) hGz hy]
  exact Finset.sum_const_zero

end ShrinkingSpheres
