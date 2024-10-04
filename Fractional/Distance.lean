import Fractional.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Topology.MetricSpace.Defs


noncomputable instance {α : Type} [Fintype α] : MetricSpace (Distr α) where
  dist x y :=
    (∑ i : α, |(x i).val - (y i).val|) / 2
  dist_self x := by
    simp [dist]
  dist_comm x y := by
    simp [dist, abs_sub_comm]
  dist_triangle x y z := by
    simp [dist]
    rw [←add_div, ←Finset.sum_add_distrib]
    apply div_le_div_of_nonneg_right
    swap; norm_num
    apply Finset.sum_le_sum
    intros
    apply abs_sub_le
  eq_of_dist_eq_zero hxy := by
    simp [dist] at hxy
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => abs_nonneg _)] at hxy
    ext i
    specialize hxy i (Finset.mem_univ i)
    rw [abs_eq_zero, sub_eq_zero] at hxy
    simp_all
