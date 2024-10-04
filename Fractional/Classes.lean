import Fractional.Basic


class Fragma (α : Type) [Fintype α] where
  op : FOP₂ α

infix:65 " ◇ " => Fragma.op⌞
