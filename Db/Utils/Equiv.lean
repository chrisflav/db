universe u v

structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  invFun_toFun (a : α) : invFun (toFun a) = a
  toFun_invFun (b : β) : toFun (invFun b) = b

notation α:max " ≃ " β:max => Equiv α β

def Equiv.refl (α : Type u) : α ≃ α where
  toFun := id
  invFun := id
  invFun_toFun := by grind
  toFun_invFun := by grind
