import Proof.ParallelEnergySectors

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped InnerProductSpace
namespace ShrinkingSpheres.ParallelEnergy

/-- Order: scalar self, first self, potential self, scalar/first,
scalar/potential, first/potential, model/scalar, model/first, model/potential.
The final three sectors include the factor four from twice the model. -/
def weightedSquareSector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : ℝ) (F A : Fin 4 → H) : Fin 9 → ℝ
  | 0 => μ * (‖F 0‖^2 - ‖A 0‖^2)
  | 1 => μ * (‖F 1‖^2 - ‖A 1‖^2)
  | 2 => μ * (‖F 2‖^2 - ‖A 2‖^2)
  | 3 => 2 * μ * (⟪F 0,F 1⟫_ℝ - ⟪A 0,A 1⟫_ℝ)
  | 4 => 2 * μ * (⟪F 0,F 2⟫_ℝ - ⟪A 0,A 2⟫_ℝ)
  | 5 => 2 * μ * (⟪F 1,F 2⟫_ℝ - ⟪A 1,A 2⟫_ℝ)
  | 6 => 4 * μ * (⟪F 3,F 0⟫_ℝ - ⟪A 3,A 0⟫_ℝ)
  | 7 => 4 * μ * (⟪F 3,F 1⟫_ℝ - ⟪A 3,A 1⟫_ℝ)
  | 8 => 4 * μ * (⟪F 3,F 2⟫_ℝ - ⟪A 3,A 2⟫_ℝ)

lemma weighted_square_expansion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (μ : ℝ) (F A : Fin 4 → H) :
    μ * ‖(2:ℝ) • F 3 + (F 0 + F 1 + F 2)‖^2 -
      μ * ‖(2:ℝ) • A 3 + (A 0 + A 1 + A 2)‖^2 -
      4 * (μ * ‖F 3‖^2 - μ * ‖A 3‖^2) =
      ∑ i : Fin 9,weightedSquareSector μ F A i := by
  simp [Fin.sum_univ_succ,weightedSquareSector,norm_add_sq_real,inner_add_left,
    inner_add_right,real_inner_smul_left,norm_smul,mul_pow]
  ring

lemma weightedSquareSector_integrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {Y S : Set X} (hY : MeasurableSet Y)
    (hS : IsCompact S) (hSY : S ⊆ Y) (μ : X → ℝ) (hμ : ContinuousOn μ Y)
    (hμ0 : ∀ y ∈ Y,0 ≤ μ y) (F A : Fin 4 → X → H)
    (hF : ∀ k,MemLp (F k) 2 (volume.restrict Y))
    (hA : ∀ k,MemLp (A k) 2 (volume.restrict Y))
    (hzF : ∀ k,∀ y ∈ Y,y ∉ S → F k y=0)
    (hzA : ∀ k,∀ y ∈ Y,y ∉ S → A k y=0) (i : Fin 9) :
    IntegrableOn (fun y => weightedSquareSector (μ y) (fun k => F k y) (fun k => A k y) i) Y := by
  have hSqF (k) := integrableOn_local_weighted_norm_sq_of_memLp hY hS hSY
    (F k) (hF k) (hzF k) μ hμ hμ0
  have hSqA (k) := integrableOn_local_weighted_norm_sq_of_memLp hY hS hSY
    (A k) (hA k) (hzA k) μ hμ hμ0
  have hInnF (j k) := integrableOn_local_weighted_inner_of_memLp hY hS hSY
    (F j) (F k) (hF j) (hF k) (hzF j) μ hμ
  have hInnA (j k) := integrableOn_local_weighted_inner_of_memLp hY hS hSY
    (A j) (A k) (hA j) (hA k) (hzA j) μ hμ
  fin_cases i
  · exact ((hSqF 0).sub (hSqA 0)).congr (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact ((hSqF 1).sub (hSqA 1)).congr (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact ((hSqF 2).sub (hSqA 2)).congr (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact (((hInnF 0 1).sub (hInnA 0 1)).const_mul 2).congr
      (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact (((hInnF 0 2).sub (hInnA 0 2)).const_mul 2).congr
      (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact (((hInnF 1 2).sub (hInnA 1 2)).const_mul 2).congr
      (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact (((hInnF 3 0).sub (hInnA 3 0)).const_mul 4).congr
      (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact (((hInnF 3 1).sub (hInnA 3 1)).const_mul 4).congr
      (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))
  · exact (((hInnF 3 2).sub (hInnA 3 2)).const_mul 4).congr
      (Eventually.of_forall (fun y => by dsimp [weightedSquareSector];ring))

end ShrinkingSpheres.ParallelEnergy
