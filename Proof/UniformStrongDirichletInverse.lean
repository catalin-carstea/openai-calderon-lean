import Proof.InversePerturbation
import Proof.Archive.StrongInverseFamily
import Proof.Archive.CollaboratorFixedDirichletRegularityOct17
import Proof.Archive.CollaboratorFixedSobolevCalculusOct17
import Proof.Archive.TauCutoff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 15
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ShrinkingSpheres
open OAI.AnisotropicCalderon OAI.AnisotropicCalderon.EnergyBridge
open OAI.AnisotropicCalderon.DirichletFamily

/-- A fixed compact coefficient-jet representative of the Euclidean coefficient
    on the whole regularity neighborhood. Its arbitrary extension outside that
    neighborhood has no effect on the unit-ball Dirichlet operator. -/
theorem exists_flatCoefficientMatrix (r : ℕ) :
    ∃ F0 : SmoothCoefficientMatrix r,
      ∀ x ∈ Metric.closedBall (0:R3) 2,coefficientMatrixField r F0 x = 1 := by
  have hsub : Metric.closedBall (0:R3) 2 ⊆ Metric.ball (0:R3) 3 := by
    intro x hx
    change dist x 0 < 3
    change dist x 0 ≤ 2 at hx
    linarith
  obtain ⟨χ,hχ,_,hOne,hCompact,_⟩ :=
    (isCompact_closedBall (0:R3) 2).exists_contDiff_cutoff Metric.isOpen_ball hsub
  let q : SmoothCoefficientJets r := compactCoefficient r χ hχ hCompact
  let F0 : SmoothCoefficientMatrix r := fun i j => if i=j then q else 0
  refine ⟨F0,?_⟩
  intro x hx
  have hχx : χ x = 1 := by
    have hh : x ∈ χ ⁻¹' {1} := interior_subset (hOne hx)
    exact hh
  ext i j
  change coefficientValue r (if i=j then q else 0) x = (1:Matrix (Fin 3) (Fin 3) ℝ) i j
  split_ifs with hij
  · subst j
    rw [show coefficientValue r q = χ from coefficientValue_compactCoefficient r χ hχ hCompact]
    simpa using hχx
  · change (0:ℝ) = (1:Matrix (Fin 3) (Fin 3) ℝ) i j
    simp [hij]

/-- Uniform strong inverse bounds in a single finite coefficient-jet neighborhood
    of the flat operator. Both the neighborhood and the bound are chosen before
    the perturbed coefficient, so this does not use compactness of one metric family. -/
theorem exists_uniform_strongDirichlet_neighborhood (s : ℕ) :
    ∃ F0 : SmoothCoefficientMatrix (s+2),
      (∀ x ∈ Metric.closedBall (0:R3) 2,coefficientMatrixField (s+2) F0 x = 1) ∧
      ∃ δ C : ℝ,0 < δ ∧ 0 ≤ C ∧
      ∀ (F : SmoothCoefficientMatrix (s+2)) (lam Lam : ℝ),
        ‖F-F0‖ ≤ δ →
        TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
          (coefficientMatrixField (s+2) F) lam Lam →
        ‖(strongDirichletOperator fixedSobolevCalculus s F).inverse‖ ≤ C := by
  obtain ⟨F0,hF0⟩ := exists_flatCoefficientMatrix (s+2)
  have hUE0 : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3)
      (coefficientMatrixField (s+2) F0) 1 1 := by
    have h := TauCeti.PDE.uniformlyEllipticOn_const_one_one (n:=Fin 3) (ballOpens : Set R3)
    refine ⟨h.1,h.2.1,?_⟩
    intro x hx
    rw [hF0 x (by
      have hh : dist x 0 < 1 := hx
      change dist x 0 ≤ 2
      linarith)]
    exact h.2.2 hx
  let A0 := strongDirichletOperator fixedSobolevCalculus s F0
  have hA0 : A0.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity s F0 hUE0
  let B : ℝ := ‖A0.inverse‖+1
  let T := strongCoefficientOperatorL fixedSobolevCalculus s
  let δ : ℝ := (2*(B+1)*(‖T‖+1))⁻¹
  have hB : 0 < B := by dsimp [B]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨F0,hF0,δ,2*B,hδ,by positivity,?_⟩
  intro F lam Lam hNear hUE
  let A := strongDirichletOperator fixedSobolevCalculus s F
  have hA : A.IsInvertible := strongDirichletOperator_isInvertible_of_elliptic
    fixedSobolevCalculus fixedDirichletRegularity s F hUE
  apply inverse_norm_le_twice_of_half_perturbation A A0 hA hA0 B hB.le
    (by dsimp [B]; linarith)
  have hDiff : ‖A-A0‖ ≤ ‖T‖*δ := by
    have hh := T.le_opNorm (F-F0)
    have heq : T (F-F0) = A-A0 := by exact map_sub T F F0
    rw [heq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hNear (norm_nonneg T))
  have hOne : 2*(B+1)*(‖T‖+1)*δ = 1 := mul_inv_cancel₀ (by positivity)
  have hCompare : 2*B*‖T‖ ≤ 2*(B+1)*(‖T‖+1) := by
    nlinarith only [hB.le,norm_nonneg T]
  have hBound := mul_le_mul_of_nonneg_right hCompare hδ.le
  have hBD := mul_le_mul_of_nonneg_left hDiff hB.le
  nlinarith only [hOne,hBound,hBD]

end ShrinkingSpheres
