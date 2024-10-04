import Fractional.Basic


class Fragma (α : Type) [Fintype α] where
  op : FOP₂ α

infix:65 " ⬙ " => Fragma.op
infix:65 " ⬘ " => Fragma.op.apply₂

theorem Fragma.op_eq {α : Type} [Fintype α] [DecidableEq α] [Fragma α] (a b : α) :
    a ⬙ b = a ⬘ b :=
  FOP₂.apply₂_coe Fragma.op a b
