import Fractional.Basic


class Fragma (α : Type) [Fintype α] where
  op : FOP₂ α

infix:65 " ◇ " => Fragma.op⌞

example {α : Type} [Fintype α] [Fragma α] (x y : Distr α) :
    x ◇ y = (fun i : α => (Fragma.op i)⌞ y)⌞ x := by
  ext
  simp only [FOP₂.apply₂, FOP₁.apply₁, NNRat.coe_inj]
  apply congr_arg
  ext
  rw [NNRat.coe_inj, Finset.mul_sum]
  simp_rw [mul_assoc]
