import RegularIndependentReserve
namespace JSP452Audit.StarHost
open SimpleGraph
abbrev ZhaoVertex (d : ℕ) := Option (Fin (2*d) ⊕ Fin (2*d))
def zhaoLeft {d : ℕ} (i : Fin (2*d)) : ZhaoVertex d := some (.inl i)
def zhaoRight {d : ℕ} (i : Fin (2*d)) : ZhaoVertex d := some (.inr i)
def zhaoAdj (d : ℕ) : ZhaoVertex d → ZhaoVertex d → Prop
  | none, none => False
  | none, some (.inl i) | none, some (.inr i) => i.val < d
  | some (.inl i), none | some (.inr i), none => i.val < d
  | some (.inl _), some (.inl _) | some (.inr _), some (.inr _) => False
  | some (.inl i), some (.inr j) => (i ≠ j) ∨ (d ≤ i.val)
  | some (.inr j), some (.inl i) => (i ≠ j) ∨ (d ≤ i.val)

def zhaoGraph (d : ℕ) : SimpleGraph (ZhaoVertex d) where
  Adj := zhaoAdj d
  symm := ⟨fun x y h => by
    rcases x with _|⟨x|x⟩ <;> rcases y with _|⟨y|y⟩ <;> exact h⟩
  loopless := ⟨fun x => by rcases x with _|⟨x|x⟩ <;> exact id⟩

instance (d : ℕ) : DecidableRel (zhaoGraph d).Adj := fun x y => by
  rcases x with _|⟨x|x⟩ <;> rcases y with _|⟨y|y⟩ <;> dsimp [zhaoGraph,zhaoAdj] <;> infer_instance

theorem zhao_order (d : ℕ) : Nat.card (ZhaoVertex d)=2*(2*d)+1 := by
  rw [Nat.card_eq_fintype_card]; simp [ZhaoVertex]; omega
end JSP452Audit.StarHost
