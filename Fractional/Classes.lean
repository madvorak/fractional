import Fractional.Basic


class Fragma (α : Type) [Fintype α] where
  op : FOP₂ α

infix:85 " ⬙ " => Fragma.op
infix:84 " ⬘ " => Fragma.op.app₂

theorem Fragma.op_eq {α : Type} [Fintype α] [DecidableEq α] [Fragma α] (a b : α) :
    a ⬙ b = a ⬘ b :=
  FOP₂.app₂_coe Fragma.op a b
