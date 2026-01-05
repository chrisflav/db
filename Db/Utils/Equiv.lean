universe u₁ u₂ u₃ u₄ u v

structure Equiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  invFun_toFun (a : α) : invFun (toFun a) = a := by grind
  toFun_invFun (b : β) : toFun (invFun b) = b := by grind

attribute [simp, grind =] Equiv.invFun_toFun Equiv.toFun_invFun

notation α:max " ≃ " β:max => Equiv α β

@[ext]
theorem Equiv.ext {α : Type u} {β : Type v} {e₁ e₂ : α ≃ β}
    (h : e₁.toFun = e₂.toFun) : e₁ = e₂ := by
  obtain ⟨toFun₁, invFun₁, h₁₁, h₁₂⟩ := e₁
  obtain ⟨toFun₂, invFun₂, h₂₁, h₂₂⟩ := e₂
  simp only [mk.injEq]
  refine ⟨h, ?_⟩
  ext b
  dsimp at h
  rw [← h₂₂ b, h₂₁, ← h, h₁₁]

def Equiv.refl (α : Type u) : α ≃ α where
  toFun := id
  invFun := id

def Equiv.trans {α : Type u₁} {β : Type u₂} {γ : Type u₃}
    (e : α ≃ β) (f : β ≃ γ) :
    α ≃ γ where
  toFun a := f.toFun (e.toFun a)
  invFun c := e.invFun (f.invFun c)

def Equiv.sumCongr {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type u₃} {β₂ : Type u₄}
    (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
    (α₁ ⊕ β₁) ≃ (α₂ ⊕ β₂) where
  toFun := Sum.map ea.toFun eb.toFun
  invFun := Sum.map ea.invFun eb.invFun

def finSumFinEquiv {m n : Nat} :
    (Fin m ⊕ Fin n) ≃ (Fin (m + n)) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m ⊕ Fin n) Sum.inl Sum.inr i
  toFun_invFun i := by induction i using Fin.addCases <;> simp

def Equiv.optionCongr {α : Type u₁} {β : Type u₂} (e : α ≃ β) :
    (Option α) ≃ (Option β) where
  toFun := Option.map e.toFun
  invFun := Option.map e.invFun
  invFun_toFun a := by induction a <;> grind
  toFun_invFun b := by induction b <;> grind
