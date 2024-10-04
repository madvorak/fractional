import Fractional.Basic


variable {α : Type} [Fintype α]

def Distr.similarity (x y : Distr α) : ℚ≥0 :=
  ∑ i : α, min (x i) (y i)

lemma Distr.similarity_le_one (x y : Distr α) :
    x.similarity y ≤ 1 := by
  sorry

lemma Distr.similarity_eq_one_iff (x y : Distr α) :
    x.similarity y = 1 ↔ x = y := by
  constructor <;> intro hxy
  · sorry
  · unfold Distr.similarity
    simp_rw [hxy, min_self]
    apply Distr.sumOne

lemma Distr.similarity_comm (x y : Distr α) :
    x.similarity y = y.similarity x := by
  unfold Distr.similarity
  apply congr_arg
  ext
  apply min_comm

def Distr.distance (x y : Distr α) : ℚ≥0 :=
  1 - x.similarity y

lemma Distr.distance_le_one (x y : Distr α) :
    x.distance y ≤ 1 := by
  apply tsub_le_self

lemma Distr.distance_eq_zero_iff (x y : Distr α) :
    x.distance y = 0 ↔ x = y := by
  convert Distr.similarity_eq_one_iff x y using 1
  unfold Distr.distance
  constructor <;> intro hxy
  · sorry
  · rw [hxy]
    exact tsub_eq_zero_of_le rfl

lemma Distr.distance_self (x : Distr α) :
    x.distance x = 0 := by
  rw [Distr.distance_eq_zero_iff]

lemma Distr.distance_comm (x y : Distr α) :
    x.distance y = y.distance x := by
  unfold Distr.distance
  rw [Distr.similarity_comm]

theorem Distr.distance_eq (x y : Distr α) :
    x.distance y = (∑ i : α, |(x i).val - (y i).val|) / 2 := by
  simp only [distance, similarity, NNRat.val_eq_cast]
  simp_rw [←max_sub_min_eq_abs]
  rw [Finset.sum_sub_distrib]
  sorry

instance : MetricSpace (Distr α) where
  dist x y := Distr.distance x y
  dist_self x := sorry -- Distr.distance_self x
  dist_comm x y := sorry -- Distr.distance_comm x y
  dist_triangle x y z := sorry
  eq_of_dist_eq_zero hxy := sorry -- Distr.distance_eq_zero_iff.mpr hxy
