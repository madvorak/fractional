import Fractional.Classes
import Fractional.Distance


variable {S : Type} [Fintype S] [Fragma S]

def ε : ℝ := 0.00000001
axiom almostComm : ∀ x y : S, x ⬙ y 𝄩 y ⬙ x ≤ ε


lemma almostComm_distr (x y : 𝍖 S) : x ⬘ y 𝄩 y ⬘ x ≤ ε := by
  rw [dist_le_real_iff]
  show
    ∑ s : S,
      |(Distr.mk (∑ i : S, ∑ j : S, x i * y j * (i ⬙ j) ·) _ _ s) -
       (Distr.mk (∑ j : S, ∑ i : S, y j * x i * (j ⬙ i) ·) _ _ s)| ≤
    2 * ε
  conv =>
    lhs; congr; rfl; ext; congr; congr; rfl; congr; congr; ext; rw [Finset.sum_comm];
  show
    ∑ s : S,
      |(∑ i : S, ∑ j : S, x i * y j * (i ⬙ j) s -
        ∑ i : S, ∑ j : S, y j * x i * (j ⬙ i) s)| ≤
    2 * ε
  -- structure for the rest of the proof
  calc ∑ s, |(∑ i, ∑ j, x i * y j * (i ⬙ j) s - ∑ i, ∑ j, y j * x i * (j ⬙ i) s)|
     = ∑ s, |∑ i, ∑ j, x i * y j * ((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ ≤ ∑ s, ∑ i, |∑ j, x i * y j * ((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ ≤ ∑ s, ∑ i, ∑ j, |x i * y j * ((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ = ∑ i, ∑ s, ∑ j, |x i * y j * ((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ = ∑ i, ∑ j, ∑ s, |x i * y j * ((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ = ∑ i, ∑ j, ∑ s, x i * y j * |((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ = ∑ i, ∑ j, x i * y j * ∑ s, |((i ⬙ j) s - (j ⬙ i) s)| := ?_
   _ = ∑ i, ∑ j, x i * y j * (2 * (i ⬙ j) 𝄩 (j ⬙ i)) := ?_
   _ ≤ ∑ i, ∑ j, x i * y j * (2 * ε) := ?_
   _ = ∑ i, ∑ j, 2 * ε * (x i * y j) := ?_
   _ = ∑ i, 2 * ε * ∑ j, (x i * y j) := ?_
   _ = 2 * ε * ∑ i, ∑ j, (x i * y j) := ?_
   _ = 2 * ε * 1 := ?_
   _ = 2 * ε := mul_one _
  -- proofs of the (in)equalities above
  · simp [mul_sub, mul_comm]
  · apply Finset.sum_le_sum
    intros
    apply Finset.abs_sum_le_sum_abs
  · apply Finset.sum_le_sum
    intros
    apply Finset.sum_le_sum
    intros
    apply Finset.abs_sum_le_sum_abs
  · apply Finset.sum_comm
  · apply congr_arg
    ext
    apply Finset.sum_comm
  · apply congr_arg
    ext
    apply congr_arg
    ext
    apply congr_arg
    ext
    rw [abs_mul, abs_of_nonneg]
    apply mul_nonneg <;> apply Distr.nonNeg
  · apply congr_arg
    ext
    apply congr_arg
    ext
    symm
    apply Finset.mul_sum
  · apply congr_arg
    ext
    apply congr_arg
    ext
    apply congr_arg
    symm
    apply two_mul_dist
  · apply Finset.sum_le_sum
    intros
    apply Finset.sum_le_sum
    intros
    apply mul_le_mul_of_nonneg_left
    swap; apply mul_nonneg <;> apply Distr.nonNeg
    apply mul_le_mul_of_nonneg_left _ zero_le_two
    apply almostComm
  · apply congr_arg
    ext
    apply congr_arg
    ext
    apply mul_comm
  · apply congr_arg
    ext
    symm
    apply Finset.mul_sum
  · symm
    apply Finset.mul_sum
  · apply congr_arg
    conv => lhs; congr; rfl; ext; rw [←Finset.mul_sum, Distr.sumOne, mul_one]
    apply Distr.sumOne

/--` (x ⬘ y) ⬘ z ≈ (y ⬘ x) ⬘ z ≈ z ⬘ (y ⬘ x) `-/
theorem triple_backwards (x y z : 𝍖 S) : (x ⬘ y) ⬘ z 𝄩 z ⬘ (y ⬘ x) ≤ 2 * ε :=
  calc (x ⬘ y) ⬘ z 𝄩 z ⬘ (y ⬘ x)
     ≤ (x ⬘ y) ⬘ z 𝄩 (y ⬘ x) ⬘ z + (y ⬘ x) ⬘ z 𝄩 z ⬘ (y ⬘ x) := dist_triangle ..
   _ ≤ (x ⬘ y) ⬘ z 𝄩 (y ⬘ x) ⬘ z + ε := add_le_add_left (almostComm_distr ..) _
   _ ≤ (x ⬘ y) 𝄩 (y ⬘ x) + ε := add_le_add_right (FOP₂.app₂_dist_app₂_le_dist_left ..) _
   _ ≤ ε + ε := add_le_add_right (almostComm_distr ..) _
   _ = 2 * ε := (two_mul ε).symm

example [DecidableEq S] (x y z : S) : x ⬙ y ⬘ z 𝄩 z ⬘ y ⬙ x ≤ 2 * ε := by
  rw [Fragma.op_eq_app₂, Fragma.op_eq_app₂]
  apply triple_backwards

/--` (u ⬘ v) ⬘ (x ⬘ y) ≈ (x ⬘ y) ⬘ (u ⬘ v) ≈ (y ⬘ x) ⬘ (u ⬘ v) ≈ (y ⬘ x) ⬘ (v ⬘ u) `-/
theorem quadruple_backwards (u v x y : 𝍖 S) : (u ⬘ v) ⬘ (x ⬘ y) 𝄩 (y ⬘ x) ⬘ (v ⬘ u) ≤ 3 * ε := by
  calc (u ⬘ v) ⬘ (x ⬘ y) 𝄩 (y ⬘ x) ⬘ (v ⬘ u)
     ≤ (u ⬘ v) ⬘ (x ⬘ y) 𝄩 (x ⬘ y) ⬘ (u ⬘ v) + (x ⬘ y) ⬘ (u ⬘ v) 𝄩 (y ⬘ x) ⬘ (v ⬘ u) := dist_triangle ..
   _ ≤ ε + (x ⬘ y) ⬘ (u ⬘ v) 𝄩 (y ⬘ x) ⬘ (v ⬘ u) := add_le_add_right (almostComm_distr ..) _
   _ ≤ ε + (ε + ε) := ?_
   _ = 3 * ε := by ring
  · apply add_le_add_left
    apply (Fragma.op.app₂_dist_app₂_le_dist_add_dist (x ⬘ y) (y ⬘ x) (u ⬘ v) (v ⬘ u)).trans
    apply add_le_add <;> apply almostComm_distr

example [DecidableEq S] (u v x y : S) : u ⬙ v ⬘ x ⬙ y 𝄩 y ⬙ x ⬘ v ⬙ u ≤ 3 * ε := by
  repeat rw [Fragma.op_eq_app₂]
  apply quadruple_backwards
